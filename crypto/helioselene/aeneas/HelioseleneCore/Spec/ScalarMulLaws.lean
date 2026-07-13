/-
# Correctness and laws for the translated scalar ladders

This file proves functional correctness of the Aeneas-translated `Mul`
implementations generated from the shared `curve!` macro in `src/point.rs`.
Both Rust instantiations use the same four-bit fixed-window algorithm:

1. build `table[j] = j P` for all `0 <= j < 16`;
2. read the canonical 32-byte scalar from bit 255 down to bit 0;
3. accumulate four bits at a time;
4. before every completed window except the first, double the result four
   times;
5. scan all 16 table entries with `ct_eq`/`conditional_select`, then add the
   selected entry; and
6. zeroize the consumed-bit buffer and scalar temporary before returning.

## Proof layers

The development follows the generated call graph rather than defining a
second scalar-multiplication algorithm:

1. Sections 1-3 prove the common machine-bit, byte-mutation, cleanup, and
   fixed-scan facts. `consumeScalarBit`, `select16`, and their
   continuation-passing variants are proof-only names whose unfoldings are the
   right-associated blocks emitted by Aeneas.
2. Sections 4 and 5 separately verify the exact generated Selene and Helios
   table constructions and `mul_loop.body` definitions. The duplication is
   intentional: each theorem bottoms out at the concrete generated function
   name and the appropriate already-verified point operation.
3. Section 6 extracts the successful on-curve representative, descends it
   through projective equivalence, installs Lean `SMul`, and proves that this
   action is natural repeated addition. `mulP_generated` keeps the
   choice-extracted representative propositionally tied to the exact generated
   `Result` output.
4. Section 7 separates laws that follow from repeated addition from laws that
   also require the curve exponent. `SMul` itself carries no laws. The
   point-side `DistribSMul` laws are unconditional; scalar addition and
   multiplication modulo the scalar-field prime require that prime to
   annihilate every point.

## Rust and model boundary

The generated model comes from the translation-only `point.rs` rewrite in
README section 4, hunk 8: direct canonical-byte indexing replaces the mutable
bitvec iterator, consumed-bit clearing moves to `clear_scalar_bit`, fixed inner
loops are unrolled, table borrows are shortened, and `res += term` is written
as its `AddAssign` body. Production Rust remains the source of truth. This file
proves the generated patched program; equivalence of that mechanical rewrite
to production Rust, and correctness of the unverified rustc/Charon/Aeneas
pipeline, remain human audit obligations recorded in
`human_audit_assumptions_{selene,helios}.txt` section V.

The proof also consumes functional models of canonical scalar bytes,
`usize::ct_eq`, point `conditional_select`, explicit zeroization, arrays, and
machine shifts. For Helios, every point operation additionally inherits the
idealized coordinate model `dalek_ff_group::FieldElement := ZMod (2^255-19)`.
These are value-semantics assumptions. Timing, memory-access patterns,
compiler preservation of branch-free code, and physical memory erasure are not
represented and are not conclusions of this file.

The public ladder theorems start from `SPt`/`HPt`, so they establish
correctness for verified on-curve representatives. The generic loop lemmas
cover every natural scalar below `2^256`, including values with the top bit
set; no theorem is claimed for arbitrary off-curve raw Rust points.
-/
import HelioseleneCore.Spec.ScalarMul
import HelioseleneCore.Spec.Field
import HelioseleneCore.Spec.Selene.GroupLaw
import HelioseleneCore.Spec.Helios.GroupLaw
import Mathlib

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std Result
open helioselene

namespace HelioseleneSpec

namespace ScalarMul

open HelioseleneModel

noncomputable section

/-! ## 1. Shared machine-bit facts

Hunk 8 reads iteration `i` from scalar bit `255 - i`. The definitions below
state the relation between that machine spelling and ordinary natural-number
bits. They also isolate the only wrapping operations used in the loop and show
that their actual operands are in ranges where the wrapped and mathematical
values coincide. -/

/-- Generic specification for a pure value embedded in `Result`. -/
private theorem lift_spec {α : Type u} (x : α) :
    Aeneas.Std.lift x ⦃ y => y = x ⦄ :=
  (WP.spec_ok _).mpr rfl

/-- The value of bit `i` of a natural number. -/
def natBit (n i : ℕ) : ℕ := (n >>> i) % 2

/-- Read bit `i` from a 32-byte little-endian Aeneas array. -/
def arrayBit (bytes : Aeneas.Std.Array Std.U8 32#usize) (i : ℕ) : ℕ :=
  (bytes.val[i / 8]!).val >>> (i % 8) % 2

/-- All still-unprocessed bits below `limit` agree with the original scalar.

The patched loop clears a bit immediately after reading it. Consequently the
entire mutable byte array cannot remain equal to the original representation.
`FutureBits bytes n limit` records exactly what the next iteration needs: every
lower bit that has not yet been visited still equals the corresponding bit of
`n`. No property is required of already-consumed higher bits. -/
def FutureBits (bytes : Aeneas.Std.Array Std.U8 32#usize) (n limit : ℕ) : Prop :=
  ∀ i, i < limit → arrayBit bytes i = natBit n i

/-- Reading a bit through the canonical little-endian byte decomposition gives
the corresponding bit of the original natural number. -/
theorem bit_of_byte8 (n i : ℕ) :
    ((n >>> (8 * (i / 8))) % 2^8) >>> (i % 8) % 2 = natBit n i := by
  have hr : i % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [natBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow]
  have hsplit : (2 : ℕ)^8 = 2^(i % 8) * 2^(8 - i % 8) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, Nat.mod_mul_right_div_self]
  have hdvd : (2 : ℕ) ∣ 2^(8 - i % 8) := dvd_pow_self 2 (by omega)
  rw [Nat.mod_mod_of_dvd _ hdvd]
  have hi : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  rw [Nat.div_div_eq_div_mul, ← pow_add, hi]

/-- A one-bit left shift of a three-bit accumulator is exact in `U8`. -/
theorem u8_shl1_val (b : Std.U8) (hb : b.val < 128) :
    (Std.U8.wrapping_shl b 1#u32).val = 2 * b.val := by
  show ((Std.U8.wrapping_shl b 1#u32).bv).toNat = 2 * b.bv.toNat
  rw [Std.U8.wrapping_shl_bv_eq]
  rw [show ((1#u32).val % 8) = 1 from by simp]
  rw [show b.bv.shiftLeft 1 = b.bv <<< 1 from rfl]
  rw [BitVec.toNat_shiftLeft]
  have hb' : b.bv.toNat < 128 := hb
  rw [Nat.shiftLeft_eq]
  omega

/-- A right shift by an in-range amount is exact in `U8`. -/
theorem u8_wrapping_shr_val (x : Std.U8) (s : Std.U32) (hs : s.val < 8) :
    (Std.U8.wrapping_shr x s).val = x.val >>> s.val := by
  show ((Std.U8.wrapping_shr x s).bv).toNat = x.bv.toNat >>> s.val
  rw [Std.U8.wrapping_shr_bv_eq, Nat.mod_eq_of_lt hs]
  exact BitVec.toNat_ushiftRight x.bv s.val

/-- OR-ing a fresh bit into an even accumulator is ordinary addition. -/
theorem or_two_mul_add (a b : ℕ) (hb : b < 2) :
    2 * a ||| b = 2 * a + b := by
  have h := Nat.two_pow_add_eq_or_of_lt (a := a) (i := 1) (b := b) (by simpa using hb)
  simpa using h.symm

/-- Clearing bit `offset` of a byte preserves every lower bit. -/
theorem clear_byte_preserves_lower (b : Std.U8) (offset j : ℕ)
    (hoffset : offset < 8) (hj : j < offset) :
    (b.bv &&& ~~~ ((1#8 : BitVec 8) <<< offset))[j]! = b.bv[j]! := by
  interval_cases offset <;> interval_cases j <;> simp_all

/-- Natural-value form of `clear_byte_preserves_lower`. -/
theorem clear_byte_preserves_lower_val (b : Std.U8) (offset j : ℕ)
    (hoffset : offset < 8) (hj : j < offset) :
    ((((b.bv &&& ~~~ ((1#8 : BitVec 8) <<< offset))).toNat >>> j) % 2) =
      ((b.val >>> j) % 2) := by
  have h := congrArg Bool.toNat (clear_byte_preserves_lower b offset j hoffset hj)
  rw [BitVec.getElem!_eq_testBit_toNat, BitVec.getElem!_eq_testBit_toNat,
    Nat.toNat_testBit, Nat.toNat_testBit] at h
  simpa only [Nat.shiftRight_eq_div_pow] using h

/-- The scalar-prefix recurrence when consuming bit `255 - i`. -/
theorem prefix_step (n i : ℕ) (hi : i < 256) :
    n >>> (256 - (i + 1)) =
      2 * (n >>> (256 - i)) + natBit n (255 - i) := by
  have h1 : 256 - i = (255 - i) + 1 := by omega
  have h2 : 256 - (i + 1) = 255 - i := by omega
  rw [h1, h2, Nat.shiftRight_add, Nat.shiftRight_one]
  unfold natBit
  omega

/-! ## 2. Canonical scalar bytes, consumed-bit clearing, and cleanup

`scalarBytes n` is the common mathematical representation used to specify the
two concrete `to_repr` paths. Selene's public theorem later proves the dalek
model returns `scalarBytes scalar.toZMod.val`; Helios proves translated
`field::verified::to_repr`/`Uint4::to_le_bytes` returns
`scalarBytes scalar.toNat`.

The mutation proof follows the translation-copy helper exactly. It proves that
clearing the current byte bit preserves every lower unread bit. This is both
the loop invariant needed for correctness and a check that the by-value helper
updates the intended index. The final zeroization theorem is deliberately only
functional: it proves totality of the generated cleanup call after its output
has become dead, not physical-memory erasure. -/

/-- The common concrete model of both scalar types' canonical 32-byte
little-endian representation. -/
def scalarBytes (n : ℕ) : Aeneas.Std.Array Std.U8 32#usize :=
  Aeneas.Std.Array.make 32#usize
    (List.ofFn (fun (i : Fin 32) => byteOfNat (n >>> (8 * i.val))))

/-- Every bit of `scalarBytes n` is the corresponding bit of `n`. -/
theorem scalarBytes_futureBits (n : ℕ) : FutureBits (scalarBytes n) n 256 := by
  intro i hi
  unfold arrayBit scalarBytes
  rw [Array.make_val]
  have hib : i / 8 < 32 := by omega
  rw [List.getElem!_ofFn _ _ hib, byteOfNat_val]
  exact bit_of_byte8 n i

/-- Restricting the unread-bit range preserves `FutureBits`. -/
theorem FutureBits.mono {bytes : Aeneas.Std.Array Std.U8 32#usize} {n a b : ℕ}
    (h : FutureBits bytes n a) (hba : b ≤ a) : FutureBits bytes n b := by
  intro i hi
  exact h i (lt_of_lt_of_le hi hba)

/-- Updating an in-bounds list position, phrased for the `getElem!` used by
`arrayBit`. -/
theorem list_getElem!_set {T : Type} [Inhabited T] (xs : List T) (x : T)
    (i j : ℕ) (hi : i < xs.length) (hj : j < xs.length) :
    (xs.set i x)[j]! = if i = j then x else xs[j]! := by
  by_cases hij : i = j
  · subst j
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set, hi, if_pos,
      Option.getD_some]
  · simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set, hij, if_false]

/-- Clear one bit of a byte, in the same `BitVec` form as the generated helper. -/
def clearByte (b : Std.U8) (offset : ℕ) : Std.U8 :=
  ⟨b.bv &&& ~~~ ((1#8 : BitVec 8) <<< offset)⟩

/-- Clearing the current bit `k` in its byte preserves `FutureBits` below `k`. -/
theorem FutureBits.set_clear {bytes : Aeneas.Std.Array Std.U8 32#usize} {n k : ℕ}
    (hk : k < 256) (hbits : FutureBits bytes n (k + 1))
    (byteIndex : Std.Usize) (hindex : byteIndex.val = k / 8) :
    FutureBits
      (bytes.set byteIndex (clearByte (bytes.val[k / 8]!) (k % 8))) n k := by
  intro j hj
  have hjbyte : j / 8 < bytes.val.length := by
    rw [bytes.property]
    norm_num
    omega
  have hkbyte : k / 8 < bytes.val.length := by
    rw [bytes.property]
    norm_num
    omega
  unfold arrayBit
  rw [Array.set_val_eq]
  rw [list_getElem!_set bytes.val _ byteIndex.val (j / 8)
    (by rw [hindex]; exact hkbyte) hjbyte]
  by_cases hsame : byteIndex.val = j / 8
  · rw [if_pos hsame]
    have hquot : j / 8 = k / 8 := by omega
    have hrem : j % 8 < k % 8 := by
      have hjdecomp := Nat.div_add_mod j 8
      have hkdecomp := Nat.div_add_mod k 8
      omega
    unfold clearByte
    change (((bytes.val[k / 8]!).bv &&& ~~~ ((1#8 : BitVec 8) <<< (k % 8))).toNat
      >>> (j % 8) % 2) = natBit n j
    rw [clear_byte_preserves_lower_val _ _ _ (Nat.mod_lt _ (by norm_num)) hrem]
    have hb := hbits j (by omega)
    unfold arrayBit at hb
    rw [hquot] at hb
    exact hb
  · rw [if_neg hsame]
    exact hbits j (by omega)

/-- The generated cleanup helper preserves every lower, still-unread scalar
bit.  This is the only semantic fact about its mutation needed by the ladder. -/
theorem clear_scalar_bit_future
    (bytes : Aeneas.Std.Array Std.U8 32#usize) (n k : ℕ) (hk : k < 256)
    (hbits : FutureBits bytes n (k + 1))
    (byteIndex : Std.Usize) (hindex : byteIndex.val = k / 8)
    (offset : Std.U32) (hoffset : offset.val = k % 8) :
    point.clear_scalar_bit bytes byteIndex offset
      ⦃ out => FutureBits out n k ⦄ := by
  unfold point.clear_scalar_bit
  step with lift_spec (Std.U8.wrapping_shl 1#u8 offset) as ⟨mask, hmask⟩
  step with lift_spec (~~~ mask) as ⟨notMask, hnotMask⟩
  step with Array.index_usize_spec bytes byteIndex
    (by scalar_tac) as ⟨old, hold⟩
  step with lift_spec (old &&& notMask) as ⟨cleared, hcleared⟩
  step with Array.update_spec bytes byteIndex cleared
    (by scalar_tac) as ⟨out, hout⟩
  rw [hout]
  have hold' : old = bytes.val[k / 8]! := by
    calc
      old = bytes.val[byteIndex.val]'(by scalar_tac) := hold
      _ = bytes.val[byteIndex.val]! :=
        (getElem!_pos bytes.val byteIndex.val (by scalar_tac)).symm
      _ = bytes.val[k / 8]! := by rw [hindex]
  have hmask_bv : mask.bv = (1#8 : BitVec 8) <<< (k % 8) := by
    rw [hmask, Std.U8.wrapping_shl_bv_eq, hoffset,
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
    rfl
  have hcleared' : cleared = clearByte (bytes.val[k / 8]!) (k % 8) := by
    apply U8.bv_eq_imp_eq
    simp only [hcleared, hnotMask, hold', UScalar.bv_and, UScalar.bv_not,
      clearByte, hmask_bv]
  rw [hcleared']
  exact FutureBits.set_clear hk hbits byteIndex hindex

theorem natBit_lt_two (n i : ℕ) : natBit n i < 2 :=
  Nat.mod_lt _ (by norm_num)

theorem mod4_eq_three_of_succ_mod_eq_zero (i : ℕ) (h : (i + 1) % 4 = 0) :
    i % 4 = 3 := by omega

theorem succ_mod4_eq_of_ne_zero (i : ℕ) (h : (i + 1) % 4 ≠ 0) :
    (i + 1) % 4 = i % 4 + 1 := by omega

theorem nonwindow_arithmetic (i a bits bit nextBits oldPrefix nextPrefix : ℕ)
    (hwindow : (i + 1) % 4 ≠ 0)
    (hold : oldPrefix = 2^(i % 4) * a + bits)
    (hnextPrefix : nextPrefix = 2 * oldPrefix + bit)
    (hnextBits : nextBits = 2 * bits + bit)
    (hbits : bits < 2^(i % 4)) (hbit : bit < 2) :
    nextPrefix = 2^((i + 1) % 4) * a + nextBits ∧
      nextBits < 2^((i + 1) % 4) := by
  have hmod := succ_mod4_eq_of_ne_zero i hwindow
  constructor
  · rw [hnextPrefix, hold, hnextBits, hmod, Nat.pow_succ]
    ring
  · rw [hnextBits, hmod, Nat.pow_succ]
    omega

theorem fullwindow_arithmetic (i a bits bit nextBits oldPrefix nextPrefix : ℕ)
    (hwindow : (i + 1) % 4 = 0)
    (hold : oldPrefix = 2^(i % 4) * a + bits)
    (hnextPrefix : nextPrefix = 2 * oldPrefix + bit)
    (hnextBits : nextBits = 2 * bits + bit) :
    nextPrefix = 16 * a + nextBits := by
  have hmod := mod4_eq_three_of_succ_mod_eq_zero i hwindow
  rw [hnextPrefix, hold, hnextBits, hmod]
  norm_num
  ring

theorem usize_wrapping_sub_255_val (i : Std.Usize) (hi : i.val ≤ 255) :
    (Std.Usize.wrapping_sub 255#usize i).val = 255 - i.val := by
  simp only [Std.Usize.wrapping_sub_val_eq]
  have hsize : 2^32 ≤ UScalar.size .Usize := by
    rw [UScalar.size]
    rcases System.Platform.numBits_eq with h | h <;>
      simp [UScalarTy.numBits, h]
  have hiSize : i.val < UScalar.size .Usize := by
    rw [UScalar.size]
    exact i.hBounds
  have heq : 255 + (UScalar.size .Usize - i.val) =
      (255 - i.val) + UScalar.size .Usize := by omega
  rw [show (255#usize).val = 255 by norm_num, heq, Nat.add_mod_right,
    Nat.mod_eq_of_lt]
  omega

theorem usize_wrapping_add_one_val (i : Std.Usize) (hi : i.val < 256) :
    (Std.Usize.wrapping_add i 1#usize).val = i.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hsize : 2^32 ≤ UScalar.size .Usize := by
    rw [UScalar.size]
    rcases System.Platform.numBits_eq with h | h <;>
      simp [UScalarTy.numBits, h]
  rw [show (1#usize).val = 1 by norm_num]
  omega

/-- The bit-consumption prefix shared verbatim by both generated loop bodies.

For iteration `i`, this definition performs the exact patched-Rust sequence:
compute `255 - i`, split it into byte/bit indices, shift the pending window,
read and mask one bit, OR it into the window, clear that bit in the owned byte
array, and zeroize the one-byte local. The theorem `consumeScalarBit_spec`
below proves both the new window value and preservation of all unread bits.

This is not called by the generated program. It is a foldable name for the
generated prefix; `bind_consumeScalarBit_eq` and `consumeScalarBitThen_eq`
prove the two monadic association forms used when matching `mul_loop.body`. -/
def consumeScalarBit (i : Std.Usize) (bits : Std.U8)
    (bytes : Aeneas.Std.Array Std.U8 32#usize) :
    Result (Std.U8 × Aeneas.Std.Array Std.U8 32#usize) := do
  let bitIndex ← lift (Std.Usize.wrapping_sub 255#usize i)
  let byteIndex ← bitIndex / 8#usize
  let offset0 ← bitIndex % 8#usize
  let offset ← lift (UScalar.cast .U32 offset0)
  let shiftedBits ← lift (Std.U8.wrapping_shl bits 1#u32)
  let byte ← Aeneas.Std.Array.index_usize bytes byteIndex
  let shiftedByte ← lift (Std.U8.wrapping_shr byte offset)
  let bit ← lift (shiftedByte &&& 1#u8)
  let nextBits ← lift (shiftedBits ||| bit)
  let nextBytes ← point.clear_scalar_bit bytes byteIndex offset
  let _ ← zeroize.Zeroize.Blanket.zeroize U8.Insts.ZeroizeDefaultIsZeroes bit
  ok (nextBits, nextBytes)

/-- Associativity-normalized form used to fold the generated bit-consumption
prefix while retaining its arbitrary continuation. -/
theorem bind_consumeScalarBit_eq {T : Type}
    (i : Std.Usize) (bits : Std.U8)
    (bytes : Aeneas.Std.Array Std.U8 32#usize)
    (k : (Std.U8 × Aeneas.Std.Array Std.U8 32#usize) → Result T) :
    (do
      let pair ← consumeScalarBit i bits bytes
      k pair) =
    (do
      let bitIndex ← lift (Std.Usize.wrapping_sub 255#usize i)
      let byteIndex ← bitIndex / 8#usize
      let offset0 ← bitIndex % 8#usize
      let offset ← lift (UScalar.cast .U32 offset0)
      let shiftedBits ← lift (Std.U8.wrapping_shl bits 1#u32)
      let byte ← Aeneas.Std.Array.index_usize bytes byteIndex
      let shiftedByte ← lift (Std.U8.wrapping_shr byte offset)
      let bit ← lift (shiftedByte &&& 1#u8)
      let nextBits ← lift (shiftedBits ||| bit)
      let nextBytes ← point.clear_scalar_bit bytes byteIndex offset
      let _ ← zeroize.Zeroize.Blanket.zeroize U8.Insts.ZeroizeDefaultIsZeroes bit
      k (nextBits, nextBytes)) := by
  simp only [consumeScalarBit, bind_assoc_eq, bind_tc_ok]

/-- Continuation-passing spelling of the generated prefix; unlike a nested
monadic bind, this unfolds definitionally to Aeneas's right-associated block. -/
def consumeScalarBitThen {T : Type}
    (i : Std.Usize) (bits : Std.U8)
    (bytes : Aeneas.Std.Array Std.U8 32#usize)
    (k : Std.U8 → Aeneas.Std.Array Std.U8 32#usize → Result T) : Result T := do
  let bitIndex ← lift (Std.Usize.wrapping_sub 255#usize i)
  let byteIndex ← bitIndex / 8#usize
  let offset0 ← bitIndex % 8#usize
  let offset ← lift (UScalar.cast .U32 offset0)
  let shiftedBits ← lift (Std.U8.wrapping_shl bits 1#u32)
  let byte ← Aeneas.Std.Array.index_usize bytes byteIndex
  let shiftedByte ← lift (Std.U8.wrapping_shr byte offset)
  let bit ← lift (shiftedByte &&& 1#u8)
  let nextBits ← lift (shiftedBits ||| bit)
  let nextBytes ← point.clear_scalar_bit bytes byteIndex offset
  let _ ← zeroize.Zeroize.Blanket.zeroize U8.Insts.ZeroizeDefaultIsZeroes bit
  k nextBits nextBytes

theorem consumeScalarBitThen_eq {T : Type}
    (i : Std.Usize) (bits : Std.U8)
    (bytes : Aeneas.Std.Array Std.U8 32#usize)
    (k : Std.U8 → Aeneas.Std.Array Std.U8 32#usize → Result T) :
    consumeScalarBitThen i bits bytes k = (do
      let pair ← consumeScalarBit i bits bytes
      k pair.1 pair.2) := by
  simp only [consumeScalarBitThen, consumeScalarBit, bind_assoc_eq, bind_tc_ok]

/-- Consuming bit `255 - i` appends that bit to the window accumulator and
preserves all lower, still-unread bits in the progressively cleared byte array.

The precondition `bits.val < 8` is the state immediately before shifting a
not-yet-complete four-bit window. It implies the `U8` left shift is exact. The
postcondition proves the result is below 16, so it is a valid table index once
the fourth bit completes a window. Every array index, cast, and shift bound in
the generated prefix is discharged inside this proof. -/
theorem consumeScalarBit_spec
    (n : ℕ) (i : Std.Usize) (hi : i.val < 256) (bits : Std.U8)
    (hbits : bits.val < 8) (bytes : Aeneas.Std.Array Std.U8 32#usize)
    (hfuture : FutureBits bytes n (256 - i.val)) :
    consumeScalarBit i bits bytes
      ⦃ out => out.1.val = 2 * bits.val + natBit n (255 - i.val) ∧
        out.1.val < 16 ∧ FutureBits out.2 n (255 - i.val) ⦄ := by
  unfold consumeScalarBit
  step with lift_spec (Std.Usize.wrapping_sub 255#usize i) as ⟨bitIndex, hbitIndex⟩
  have hbitIndexVal : bitIndex.val = 255 - i.val := by
    rw [hbitIndex]
    exact usize_wrapping_sub_255_val i (by omega)
  step as ⟨byteIndex, hbyteIndex⟩
  step as ⟨offset0, hoffset0⟩
  step with lift_spec (UScalar.cast .U32 offset0) as ⟨offset, hoffset⟩
  have hbyteIndexVal : byteIndex.val = (255 - i.val) / 8 := by
    rw [hbyteIndex, hbitIndexVal]
  have hoffsetVal : offset.val = (255 - i.val) % 8 := by
    rw [hoffset, UScalar.cast_val_eq, hoffset0, hbitIndexVal]
    apply Nat.mod_eq_of_lt
    have := Nat.mod_lt (255 - i.val) (by norm_num : 0 < 8)
    exact lt_trans this (by norm_num [UScalarTy.numBits])
  step with lift_spec (Std.U8.wrapping_shl bits 1#u32) as ⟨shiftedBits, hshiftedBits⟩
  have hshiftedBitsVal : shiftedBits.val = 2 * bits.val := by
    rw [hshiftedBits]
    exact u8_shl1_val bits (by omega)
  step with Aeneas.Std.Array.index_usize_spec bytes byteIndex
    (by scalar_tac) as ⟨byte, hbyte⟩
  have hbyteVal : byte.val = (bytes.val[(255 - i.val) / 8]!).val := by
    calc
      byte.val = (bytes.val[byteIndex.val]'(by scalar_tac)).val :=
        congrArg (fun x : Std.U8 => x.val) hbyte
      _ = (bytes.val[byteIndex.val]!).val :=
        congrArg (fun x : Std.U8 => x.val)
          (getElem!_pos bytes.val byteIndex.val (by scalar_tac)).symm
      _ = (bytes.val[(255 - i.val) / 8]!).val := by rw [hbyteIndexVal]
  step with lift_spec (Std.U8.wrapping_shr byte offset) as ⟨shiftedByte, hshiftedByte⟩
  have hshiftedByteVal : shiftedByte.val =
      byte.val >>> ((255 - i.val) % 8) := by
    rw [hshiftedByte, u8_wrapping_shr_val byte offset (by
      rw [hoffsetVal]
      exact Nat.mod_lt _ (by norm_num)), hoffsetVal]
  step with lift_spec (shiftedByte &&& 1#u8) as ⟨bit, hbit⟩
  have hbitVal : bit.val = natBit n (255 - i.val) := by
    have hread := hfuture (255 - i.val) (by omega)
    unfold arrayBit at hread
    rw [hbit, UScalar.val_and, show (1#u8).val = 1 by norm_num,
      Nat.and_one_is_mod, hshiftedByteVal, hbyteVal, hread]
  step with lift_spec (shiftedBits ||| bit) as ⟨nextBits, hnextBits⟩
  have hnextBitsVal : nextBits.val =
      2 * bits.val + natBit n (255 - i.val) := by
    rw [hnextBits, UScalar.val_or, hshiftedBitsVal, hbitVal,
      or_two_mul_add _ _ (natBit_lt_two n (255 - i.val))]
  step with clear_scalar_bit_future bytes n (255 - i.val) (by omega)
    (by simpa only [show 255 - i.val + 1 = 256 - i.val by omega] using hfuture)
    byteIndex hbyteIndexVal offset hoffsetVal as ⟨nextBytes, hnextBytes⟩
  unfold zeroize.Zeroize.Blanket.zeroize
  simp only [bind_tc_ok]
  refine ⟨by simpa using hnextBitsVal, ?_, by simpa using hnextBytes⟩
  change nextBits.val < 16
  rw [hnextBitsVal]
  ·
    have := natBit_lt_two n (255 - i.val)
    omega

theorem list_mapM_const_ok {T : Type} (l : List T)
    {g : Result T} {v : T} (hg : g = .ok v) :
    l.mapM (fun _ => g) = .ok (List.replicate l.length v) := by
  subst hg
  have hloop : ∀ acc,
      List.mapM.loop (fun _ => (.ok v : Result T)) l acc =
        .ok (acc.reverse ++ List.replicate l.length v) := by
    intro acc
    induction l generalizing acc with
    | nil => simp [List.mapM.loop, pure]
    | cons _ tail ih =>
        simp [List.mapM.loop, bind_tc_ok, ih, List.reverse_cons,
          List.append_assoc, List.replicate_succ]
  simp [List.mapM, hloop]

/-- Zeroizing the dead scalar-byte buffer is total; its value is intentionally
absent from the postcondition.

The external zeroize model maps every byte to zero. At this point the loop has
already returned its point and the Rust function immediately discards the
buffer, so totality is the only property needed for scalar-multiplication
correctness. This theorem does not model volatile writes, optimizer barriers,
stack copies, or any other physical-erasure guarantee. -/
theorem u8Array_zeroize_total
    (bytes : Aeneas.Std.Array Std.U8 32#usize) :
    Array.Insts.ZeroizeZeroize.zeroize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) bytes
      ⦃ _ => True ⦄ := by
  unfold Array.Insts.ZeroizeZeroize.zeroize Aeneas.Std.Array.clone List.clone
  have hmap : List.mapM
      (zeroize.Zeroize.Blanket.zeroize U8.Insts.ZeroizeDefaultIsZeroes) bytes.val =
      .ok (List.replicate bytes.val.length 0#u8) := by
    rw [show zeroize.Zeroize.Blanket.zeroize U8.Insts.ZeroizeDefaultIsZeroes =
      (fun _ : Std.U8 => .ok 0#u8) by rfl]
    exact list_mapM_const_ok bytes.val rfl
  split
  · simp_all only [bind_tc_ok, WP.spec_ok]
  · rename_i _ heq
    have hbad := hmap.symm.trans heq
    cases hbad
  · rename_i heq
    have hbad := hmap.symm.trans heq
    cases hbad

/-! ## 3. The generated fixed 16-entry table scan

Hunk 8 unrolls the original `table[1..].iter().enumerate()` loop into 15
literal candidate blocks. `select16` records precisely those blocks in indices
1 through 15, starting from entry 0. The invariant says that after candidate
`k`, the current value is the addressed table entry if its index has already
been visited and entry 0 otherwise.

The only semantic assumptions are the value results of `usize::ct_eq` and the
point-level `conditional_select`: equality yields true exactly at the addressed
index, and selection returns its second argument exactly when true. The theorem
therefore proves a full scan returns `table[bits]`. It does **not** prove that
execution time or memory access is independent of `bits`; those properties are
erased by `Choice := Bool` and the pure external models. -/

/-- One of the 15 candidate-selection blocks in the generated scan.

The table candidate is copied into a local in patched Rust before it is
borrowed. Because points are `Copy`, the generated value here is exactly the
same table entry; no aliasing fact remains in the pure model. -/
def selectCandidate {T : Type} (select : T → T → subtle.Choice → Result T)
    (table : Aeneas.Std.Array T 16#usize) (bits : Std.U8)
    (index : Std.Usize) (current : T) : Result T := do
  let candidate ← Aeneas.Std.Array.index_usize table index
  let i ← lift (core.convert.num.FromUsizeU8.from bits)
  let c ← Usize.Insts.SubtleConstantTimeEq.ct_eq i index
  select current candidate c

/-- Continuation-passing form of one candidate block.  Its unfolding matches
the right-associated `do` block emitted by Aeneas. -/
def selectCandidateThen {T U : Type}
    (select : T → T → subtle.Choice → Result T)
    (table : Aeneas.Std.Array T 16#usize) (bits : Std.U8)
    (index : Std.Usize) (current : T) (k : T → Result U) : Result U := do
  let candidate ← Aeneas.Std.Array.index_usize table index
  let i ← lift (core.convert.num.FromUsizeU8.from bits)
  let c ← Usize.Insts.SubtleConstantTimeEq.ct_eq i index
  let out ← select current candidate c
  k out

/-- The fixed, unrolled table scan shared by both generated ladders.  Unfolding
`selectCandidate` makes this definition textually identical to the translated
block, so folding it in a proof does not replace any generated computation. -/
def select16 {T : Type} (select : T → T → subtle.Choice → Result T)
    (table : Aeneas.Std.Array T 16#usize) (bits : Std.U8) : Result T := do
  let term0 ← Aeneas.Std.Array.index_usize table 0#usize
  let term1 ← selectCandidate select table bits 1#usize term0
  let term2 ← selectCandidate select table bits 2#usize term1
  let term3 ← selectCandidate select table bits 3#usize term2
  let term4 ← selectCandidate select table bits 4#usize term3
  let term5 ← selectCandidate select table bits 5#usize term4
  let term6 ← selectCandidate select table bits 6#usize term5
  let term7 ← selectCandidate select table bits 7#usize term6
  let term8 ← selectCandidate select table bits 8#usize term7
  let term9 ← selectCandidate select table bits 9#usize term8
  let term10 ← selectCandidate select table bits 10#usize term9
  let term11 ← selectCandidate select table bits 11#usize term10
  let term12 ← selectCandidate select table bits 12#usize term11
  let term13 ← selectCandidate select table bits 13#usize term12
  let term14 ← selectCandidate select table bits 14#usize term13
  selectCandidate select table bits 15#usize term14

theorem index16_eq {T : Type} [Inhabited T]
    (table : Aeneas.Std.Array T 16#usize) (index : Std.Usize)
    (hindex : index.val < 16) :
    Aeneas.Std.Array.index_usize table index = .ok table.val[index.val]! := by
  obtain ⟨x, hx, hval⟩ := WP.spec_imp_exists
    (Aeneas.Std.Array.index_usize_spec table index (by scalar_tac))
  rw [hx, hval, getElem!_pos table.val index.val (by scalar_tac)]

/-- After candidate `k`, the scan has selected the addressed entry when its
index is at most `k`, and still holds entry zero otherwise. -/
def ScanInv {T : Type} [Inhabited T] (table : Aeneas.Std.Array T 16#usize)
    (bits : Std.U8) (k : ℕ) (current : T) : Prop :=
  current = if bits.val ≤ k then table.val[bits.val]! else table.val[0]!

theorem scanInv_zero {T : Type} [Inhabited T]
    (table : Aeneas.Std.Array T 16#usize) (bits : Std.U8) (current : T)
    (hcurrent : current = table.val[0]!) : ScanInv table bits 0 current := by
  unfold ScanInv
  rw [hcurrent]
  by_cases hzero : bits.val = 0
  · simp [hzero]
  · simp [hzero]

theorem ScanInv.next {T : Type} [Inhabited T]
    (table : Aeneas.Std.Array T 16#usize) (bits : Std.U8) (k : ℕ)
    (current candidate : T) (hcurrent : ScanInv table bits k current)
    (hcandidate : candidate = table.val[k + 1]!) :
    ScanInv table bits (k + 1)
      (if decide (bits.val = k + 1) then candidate else current) := by
  unfold ScanInv at hcurrent ⊢
  rw [hcurrent, hcandidate]
  by_cases heq : bits.val = k + 1
  · simp [heq]
  · by_cases hle : bits.val ≤ k
    · have hle' : bits.val ≤ k + 1 := by omega
      simp [heq, hle, hle']
    · have hgt : ¬bits.val ≤ k + 1 := by omega
      simp [heq, hle, hgt]

theorem fromU8_beq_eq (bits : Std.U8) (index : Std.Usize) :
    (core.convert.num.FromUsizeU8.from bits == index) =
      decide (bits.val = index.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, UScalar.eq_equiv,
    core.convert.num.FromUsizeU8.from_val_eq]

theorem usize_ct_eq_spec (a b : Std.Usize) :
    Usize.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ c => c = (a == b) ⦄ :=
  (WP.spec_ok _).mpr rfl

theorem selectCandidate_spec {T : Type} [Inhabited T]
    (select : T → T → subtle.Choice → Result T)
    (hselect : ∀ A B c, select A B c = .ok (if c then B else A))
    (table : Aeneas.Std.Array T 16#usize) (bits : Std.U8) (k : ℕ)
    (index : Std.Usize) (hindex : index.val = k + 1) (hk : k + 1 < 16)
    (current : T) (hcurrent : ScanInv table bits k current) :
    selectCandidate select table bits index current
      ⦃ out => ScanInv table bits (k + 1) out ⦄ := by
  unfold selectCandidate
  step with Aeneas.Std.Array.index_usize_spec table index
    (by scalar_tac) as ⟨candidate, hcandidate⟩
  step with lift_spec (core.convert.num.FromUsizeU8.from bits) as ⟨i, hi⟩
  step with usize_ct_eq_spec i index as ⟨c, hc⟩
  have hsel : select current candidate c
      ⦃ out => out = if c then candidate else current ⦄ := by
    rw [hselect]
    exact (WP.spec_ok _).mpr rfl
  step with hsel as ⟨out, hout⟩
  have hc' : c = decide (bits.val = k + 1) := by
    rw [hc, hi, fromU8_beq_eq, hindex]
  have hcand' : candidate = table.val[k + 1]! := by
    calc
      candidate = table.val[index.val]'(by scalar_tac) := hcandidate
      _ = table.val[index.val]! :=
        (getElem!_pos table.val index.val (by scalar_tac)).symm
      _ = table.val[k + 1]! := by rw [hindex]
  rw [hout, hc']
  exact ScanInv.next table bits k current candidate hcurrent hcand'

/-- If the point-level conditional select has its Rust semantics, the entire
unrolled scan returns exactly the entry addressed by the four-bit value. -/
theorem select16_spec {T : Type} [Inhabited T]
    (select : T → T → subtle.Choice → Result T)
    (hselect : ∀ A B c, select A B c = .ok (if c then B else A))
    (table : Aeneas.Std.Array T 16#usize) (bits : Std.U8) (hbits : bits.val < 16) :
    select16 select table bits ⦃ out => out = table.val[bits.val]! ⦄ := by
  unfold select16
  step with Aeneas.Std.Array.index_usize_spec table 0#usize
    (by norm_num) as ⟨term0, hterm0⟩
  have h0 : ScanInv table bits 0 term0 := by
    apply scanInv_zero
    rw [hterm0]
    exact (getElem!_pos table.val 0 (by scalar_tac)).symm
  step with selectCandidate_spec select hselect table bits 0 1#usize
    (by norm_num) (by norm_num) term0 h0 as ⟨term1, h1⟩
  step with selectCandidate_spec select hselect table bits 1 2#usize
    (by norm_num) (by norm_num) term1 h1 as ⟨term2, h2⟩
  step with selectCandidate_spec select hselect table bits 2 3#usize
    (by norm_num) (by norm_num) term2 h2 as ⟨term3, h3⟩
  step with selectCandidate_spec select hselect table bits 3 4#usize
    (by norm_num) (by norm_num) term3 h3 as ⟨term4, h4⟩
  step with selectCandidate_spec select hselect table bits 4 5#usize
    (by norm_num) (by norm_num) term4 h4 as ⟨term5, h5⟩
  step with selectCandidate_spec select hselect table bits 5 6#usize
    (by norm_num) (by norm_num) term5 h5 as ⟨term6, h6⟩
  step with selectCandidate_spec select hselect table bits 6 7#usize
    (by norm_num) (by norm_num) term6 h6 as ⟨term7, h7⟩
  step with selectCandidate_spec select hselect table bits 7 8#usize
    (by norm_num) (by norm_num) term7 h7 as ⟨term8, h8⟩
  step with selectCandidate_spec select hselect table bits 8 9#usize
    (by norm_num) (by norm_num) term8 h8 as ⟨term9, h9⟩
  step with selectCandidate_spec select hselect table bits 9 10#usize
    (by norm_num) (by norm_num) term9 h9 as ⟨term10, h10⟩
  step with selectCandidate_spec select hselect table bits 10 11#usize
    (by norm_num) (by norm_num) term10 h10 as ⟨term11, h11⟩
  step with selectCandidate_spec select hselect table bits 11 12#usize
    (by norm_num) (by norm_num) term11 h11 as ⟨term12, h12⟩
  step with selectCandidate_spec select hselect table bits 12 13#usize
    (by norm_num) (by norm_num) term12 h12 as ⟨term13, h13⟩
  step with selectCandidate_spec select hselect table bits 13 14#usize
    (by norm_num) (by norm_num) term13 h13 as ⟨term14, h14⟩
  step with selectCandidate_spec select hselect table bits 14 15#usize
    (by norm_num) (by norm_num) term14 h14 as ⟨term15, h15⟩
  unfold ScanInv at h15
  rw [if_pos (by omega)] at h15
  exact h15

/-! ## 4. Selene ladder correctness

The Selene point carrier `SPt` comes from `Spec/Selene/GroupLaw.lean`: it is a
reduced, on-curve projective representative. `SClass` quotients those
representatives by projective equivalence and already has an `AddCommGroup`
whose addition, zero, and doubling are tied to the translated Rust point
operations.

This section lifts those one-step contracts through the exact generated scalar
code. `Represents raw x` keeps both facts needed at every generated call: the
raw coordinates are an actual valid `SPt`, and their quotient class is `x`.
The precomputation invariant then states that table entry `j` represents
`j • base`; the loop invariant states how the committed coefficient and pending
window reconstruct the scalar prefix.

Selene coordinates use the verified helioselene field. Its scalar is the
foreign `dalek_ff_group::FieldElement`, concretely modeled as
`ZMod (2^255 - 19)`. Thus the Selene-specific foreign assumption here is that
the dalek `to_repr` model is the canonical little-endian encoding of that
value; point arithmetic itself does not cross the Helios idealized-coordinate
boundary. -/

namespace SeleneLadder

open Selene

abbrev RawPoint := point.selene.SelenePoint

private instance : Inhabited RawPoint where
  default := { x := default, y := default, z := default }

/-- A raw translated point represents a point in the verified quotient group.

Keeping the witness `P : SPt` prevents the proof from silently extending the
Rust `Mul` implementation to off-curve raw coordinates. Every generated add,
double, and select result is shown to retain such a witness. -/
def Represents (raw : RawPoint) (x : SClass) : Prop :=
  ∃ P : SPt, raw = P.1 ∧ SClass.mk P = x

theorem represents_raw (P : SPt) : Represents P.1 (SClass.mk P) :=
  ⟨P, rfl, rfl⟩

/-- The translated componentwise point select returns its second argument
exactly when the `Choice` is true. -/
theorem point_select_eq (A B : RawPoint) (c : subtle.Choice) :
    point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select A B c
      = .ok (if c then B else A) := by
  by_cases hc : c = true
  · simp only [hc, ↓reduceIte]
    rfl
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- The generated identity represents group zero. -/
theorem identity_exact_spec :
    point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.identity
      ⦃ raw => raw = Selene.idP.1 ⦄ := by
  rw [Selene.idP_ok]
  exact (WP.spec_ok _).mpr rfl

theorem identity_spec :
    point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.identity
      ⦃ raw => Represents raw 0 ⦄ := by
  rw [Selene.idP_ok]
  apply (WP.spec_ok _).mpr
  exact ⟨Selene.idP, rfl, Selene.SClass_zero_def.symm⟩

/-- The generated dedicated doubling circuit represents natural doubling. -/
theorem double_spec {raw : RawPoint} {x : SClass} (h : Represents raw x) :
    point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.double raw
      ⦃ out => Represents out (2 • x) ⦄ := by
  obtain ⟨P, hraw, hP⟩ := h
  rw [hraw]
  rw [Selene.doubleP_ok]
  apply (WP.spec_ok _).mpr
  refine ⟨Selene.doubleP P, rfl, ?_⟩
  rw [Selene.SClass_double, hP]
  exact (two_nsmul x).symm

theorem doubleMultiple_spec {raw : RawPoint} {base : SClass} (j : ℕ)
    (h : Represents raw (j • base)) :
    point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.double raw
      ⦃ out => Represents out ((2 * j) • base) ⦄ := by
  apply WP.spec_mono (double_spec h)
  intro out hout
  simpa only [← mul_smul] using hout

/-- The generated complete addition circuit represents quotient-group addition. -/
theorem add_spec {raw₁ raw₂ : RawPoint} {x y : SClass}
    (h₁ : Represents raw₁ x) (h₂ : Represents raw₂ y) :
    point.selene.SelenePoint.Insts.CoreOpsArithAddSelenePointSelenePoint.add raw₁ raw₂
      ⦃ out => Represents out (x + y) ⦄ := by
  obtain ⟨P, hraw₁, hP⟩ := h₁
  obtain ⟨Q, hraw₂, hQ⟩ := h₂
  rw [hraw₁, hraw₂]
  rw [Selene.addP_ok]
  apply (WP.spec_ok _).mpr
  refine ⟨Selene.addP P Q, rfl, ?_⟩
  rw [← Selene.SClass_add_def, hP, hQ]

theorem addBase_spec {raw baseRaw : RawPoint} {base : SClass} (j : ℕ)
    (hraw : Represents raw (j • base)) (hbase : Represents baseRaw base) :
    point.selene.SelenePoint.Insts.CoreOpsArithAddSelenePointSelenePoint.add raw baseRaw
      ⦃ out => Represents out ((j + 1) • base) ⦄ := by
  apply WP.spec_mono (add_spec hraw hbase)
  intro out hout
  simpa only [add_nsmul, one_nsmul] using hout

/-- The four dedicated doublings used between windows multiply a represented
group element by 16. -/
def fourDoubles (raw : RawPoint) : Result RawPoint := do
  let raw1 ←
    point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.double raw
  let raw2 ←
    point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.double raw1
  let raw3 ←
    point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.double raw2
  point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.double raw3

theorem fourDoubles_spec {raw : RawPoint} {x : SClass} (h : Represents raw x) :
    fourDoubles raw ⦃ out => Represents out (16 • x) ⦄ := by
  unfold fourDoubles
  step with double_spec h as ⟨raw1, h1⟩
  step with double_spec h1 as ⟨raw2, h2⟩
  step with double_spec h2 as ⟨raw3, h3⟩
  step with double_spec h3 as ⟨raw4, h4⟩
  simpa only [← mul_smul] using h4

/-- Entries below `limit` contain the corresponding small natural multiples.

The public `mul` body fills the table in the source order
`0, P, 2P, 3P, ..., 15P`, using the same optimized mixture of doubles and
adds as Rust. `TablePrefix` permits verifying that concrete assignment order
one update at a time without replacing it by a mathematically generated table. -/
def TablePrefix (table : Aeneas.Std.Array RawPoint 16#usize)
    (base : SClass) (limit : ℕ) : Prop :=
  limit ≤ 16 ∧ ∀ j, j < limit → Represents table.val[j]! (j • base)

theorem table_repeat_zero_prefix {raw : RawPoint} {base : SClass}
    (hraw : Represents raw 0) :
    TablePrefix (Aeneas.Std.Array.repeat 16#usize raw) base 1 := by
  refine ⟨by norm_num, ?_⟩
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  simpa [Aeneas.Std.Array.repeat_val] using hraw

/-- Writing the next verified multiple extends a table prefix by one. -/
theorem TablePrefix.set_next
    {table : Aeneas.Std.Array RawPoint 16#usize} {base : SClass} {limit : ℕ}
    (hlimit : limit < 16) (hprefix : TablePrefix table base limit)
    (index : Std.Usize) (hindex : index.val = limit)
    (raw : RawPoint) (hraw : Represents raw (limit • base)) :
    TablePrefix (table.set index raw) base (limit + 1) := by
  obtain ⟨_, hprefix⟩ := hprefix
  refine ⟨by omega, ?_⟩
  intro j hj
  rw [Aeneas.Std.Array.set_val_eq]
  have hi : index.val < table.val.length := by
    rw [table.property, hindex]
    norm_num
    omega
  have hjlen : j < table.val.length := by
    rw [table.property]
    norm_num
    omega
  rw [list_getElem!_set table.val raw index.val j hi hjlen]
  by_cases hij : index.val = j
  · rw [if_pos hij]
    have : j = limit := by omega
    subst j
    simpa [hindex] using hraw
  · rw [if_neg hij]
    exact hprefix j (by omega)

theorem TablePrefix.update_next_spec
    {table : Aeneas.Std.Array RawPoint 16#usize} {base : SClass} {limit : ℕ}
    (hprefix : TablePrefix table base limit) (hlimit : limit < 16)
    (index : Std.Usize) (hindex : index.val = limit)
    (raw : RawPoint) (hraw : Represents raw (limit • base)) :
    Aeneas.Std.Array.update table index raw
      ⦃ out => TablePrefix out base (limit + 1) ⦄ := by
  apply WP.spec_mono (Aeneas.Std.Array.update_spec table index raw (by scalar_tac))
  intro out hout
  rw [hout]
  exact TablePrefix.set_next hlimit hprefix index hindex raw hraw

/-- Looking up a verified table prefix returns the represented multiple. -/
theorem TablePrefix.index_spec
    {table : Aeneas.Std.Array RawPoint 16#usize} {base : SClass} {limit : ℕ}
    (hprefix : TablePrefix table base limit)
    (index : Std.Usize) (hindex : index.val < limit) :
    Aeneas.Std.Array.index_usize table index
      ⦃ raw => Represents raw (index.val • base) ⦄ := by
  obtain ⟨hlimit, hprefix⟩ := hprefix
  have hib : index.val < table.val.length := by
    rw [table.property]
    norm_num
    omega
  apply WP.spec_mono (Aeneas.Std.Array.index_usize_spec table index (by simpa using hib))
  intro raw hraw
  rw [hraw]
  have h := hprefix index.val hindex
  rw [getElem!_pos table.val index.val hib] at h
  exact h

/-- The exact unrolled Selene scan returns the represented multiple named by
the pending four-bit window. Its value proof uses `point_select_eq`; timing
remains outside the model. -/
theorem TablePrefix.select_spec
    {table : Aeneas.Std.Array RawPoint 16#usize} {base : SClass}
    (hprefix : TablePrefix table base 16) (bits : Std.U8) (hbits : bits.val < 16) :
    select16
      point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
      table bits ⦃ raw => Represents raw (bits.val • base) ⦄ := by
  apply WP.spec_mono
    (select16_spec _ point_select_eq table bits hbits)
  intro raw hraw
  rw [hraw]
  exact hprefix.2 bits.val hbits

/-- Proof-only fold for the generated full Selene table scan followed by one
point addition. -/
def addSelected (table : Aeneas.Std.Array RawPoint 16#usize)
    (raw : RawPoint) (bits : Std.U8) : Result RawPoint := do
  let term ← select16
    point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits
  point.selene.SelenePoint.Insts.CoreOpsArithAddSelenePointSelenePoint.add raw term

theorem addSelected_spec
    {table : Aeneas.Std.Array RawPoint 16#usize} {base x : SClass}
    (htable : TablePrefix table base 16) {raw : RawPoint} (hraw : Represents raw x)
    (bits : Std.U8) (hbits : bits.val < 16) :
    addSelected table raw bits
      ⦃ out => Represents out (x + bits.val • base) ⦄ := by
  unfold addSelected
  step with htable.select_spec bits hbits as ⟨term, hterm⟩
  step with add_spec hraw hterm as ⟨out, hout⟩
  exact hout

/-- Continuation-passing spelling of the exact unrolled Selene scan followed
by the generated point addition.  Unfolding this definition yields the block
in `mul_loop.body` verbatim. -/
def scanAddThen {T : Type} (table : Aeneas.Std.Array RawPoint 16#usize)
    (raw : RawPoint) (bits : Std.U8) (k : RawPoint → Result T) : Result T := do
  let term0 ← Aeneas.Std.Array.index_usize table 0#usize
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 1#usize term0 fun term1 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 2#usize term1 fun term2 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 3#usize term2 fun term3 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 4#usize term3 fun term4 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 5#usize term4 fun term5 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 6#usize term5 fun term6 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 7#usize term6 fun term7 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 8#usize term7 fun term8 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 9#usize term8 fun term9 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 10#usize term9 fun term10 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 11#usize term10 fun term11 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 12#usize term11 fun term12 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 13#usize term12 fun term13 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 14#usize term13 fun term14 =>
  selectCandidateThen point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 15#usize term14 fun term15 => do
  let out ←
    point.selene.SelenePoint.Insts.CoreOpsArithAddSelenePointSelenePoint.add raw term15
  k out

theorem scanAddThen_eq {T : Type}
    (table : Aeneas.Std.Array RawPoint 16#usize) (raw : RawPoint) (bits : Std.U8)
    (k : RawPoint → Result T) :
    scanAddThen table raw bits k = (do
      let out ← addSelected table raw bits
      k out) := by
  simp only [scanAddThen, selectCandidateThen, addSelected, select16, selectCandidate,
    bind_assoc_eq]

abbrev LoopState :=
  core.ops.range.Range Std.Usize × RawPoint × Std.U8 ×
    Aeneas.Std.Array Std.U8 32#usize

/-- The complete scalar-loop invariant.

At iteration `i = st.1.start.val`:

* `a` is the coefficient already committed to the point accumulator;
* `bits` is the pending prefix of the current four-bit window and is bounded by
  `2^(i % 4)`;
* `n >>> (256-i) = 2^(i % 4) * a + bits`, so committed and pending pieces are
  exactly the processed high-bit prefix; and
* `FutureBits ... (256-i)` says every lower bit still to be read remains equal
  to the original scalar despite progressive clearing.

When a window completes, the generated code changes `a` to `16*a + bits` and
resets the pending value. Before the first completed window (`i = 3`) it skips
the four doubles; the invariant proves the previous committed coefficient is
zero, so that special case has the same mathematical update. -/
def LoopInv (n : ℕ) (base : SClass) (st : LoopState) : Prop :=
  st.1.«end».val = 256 ∧ st.1.start.val ≤ 256 ∧
    ∃ a : ℕ,
      Represents st.2.1 (a • base) ∧
      n >>> (256 - st.1.start.val) =
        2^(st.1.start.val % 4) * a + st.2.2.1.val ∧
      st.2.2.1.val < 2^(st.1.start.val % 4) ∧
      FutureBits st.2.2.2 n (256 - st.1.start.val)

/-- The complete generated Selene loop is total and represents canonical
natural repeated addition for every 256-bit scalar.

The theorem targets the generated `mul_loop` directly and uses the decreasing
measure `256 - i`; therefore its `.ok` conclusion proves termination as well
as value correctness. It covers every branch of all 256 iterations, including
the first-window exception, non-window iterations, full table scans, and every
array access. The broad hypothesis `n < 2^256` deliberately verifies more than
Selene's canonical scalar range, so no hidden top-bit assumption enters the
loop argument. -/
theorem mul_loop_spec
    (table : Aeneas.Std.Array RawPoint 16#usize) (base : SClass)
    (htable : TablePrefix table base 16) (n : ℕ) (hn : n < 2^256) :
    point.selene.SelenePoint.Insts.CoreOpsArithMulFieldElementSelenePoint.mul_loop
      { start := 0#usize, «end» := 256#usize } table Selene.idP.1 0#u8
        (scalarBytes n)
      ⦃ out => Represents out.1 (n • base) ⦄ := by
  unfold point.selene.SelenePoint.Insts.CoreOpsArithMulFieldElementSelenePoint.mul_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (st : LoopState) => 256 - st.1.start.val)
    (inv := LoopInv n base)
  · rintro ⟨iter, res, bits, bytes⟩ hinv
    obtain ⟨hend, hstartBound, a, hres, hprefix, hbits, hfuture⟩ := hinv
    dsimp only at hend hstartBound hres hprefix hbits hfuture ⊢
    unfold point.selene.SelenePoint.Insts.CoreOpsArithMulFieldElementSelenePoint.mul_loop.body
    step as ⟨o, iter1, ho, hoend⟩
    split at ho
    · rename_i hlt
      obtain ⟨ho1, hstart1⟩ := ho
      simp only [ho1]
      have hi : iter.start.val < 256 := by omega
      change consumeScalarBitThen iter.start bits bytes (fun bits2 bytes1 => _)
        ⦃ _ ⦄
      rw [consumeScalarBitThen_eq]
      have hbits8 : bits.val < 8 := by
        have hmod : iter.start.val % 4 ≤ 3 := by
          have := Nat.mod_lt iter.start.val (by norm_num : 0 < 4)
          omega
        have hpow : 2^(iter.start.val % 4) ≤ (2 : ℕ)^3 :=
          pow_le_pow_right' (by norm_num) hmod
        norm_num at hpow
        exact lt_of_lt_of_le hbits hpow
      step with consumeScalarBit_spec n iter.start hi bits hbits8
        bytes hfuture as ⟨consumed, hbits2Val, hbits2Bound, hfuture2⟩
      rcases consumed with ⟨bits2, bytes1⟩
      step with lift_spec (Std.Usize.wrapping_add iter.start 1#usize) as ⟨nextI, hnextI⟩
      have hnextIVal : nextI.val = iter.start.val + 1 := by
        rw [hnextI]
        exact usize_wrapping_add_one_val iter.start hi
      step as ⟨window, hwindowVal⟩
      have hwindowVal' : window.val = (iter.start.val + 1) % 4 := by
        rw [hwindowVal, hnextIVal]
      split
      · rename_i hwindow
        have hwindowNat : (iter.start.val + 1) % 4 = 0 := by
          rw [← hwindowVal']
          exact congrArg UScalar.val hwindow
        have hresWindow :
            (if iter.start != 3#usize then fourDoubles res else ok res)
              ⦃ out => Represents out ((16 * a) • base) ⦄ := by
          split
          · apply WP.spec_mono (fourDoubles_spec hres)
            intro out hout
            simpa only [← mul_smul] using hout
          · rename_i hfirst
            simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hfirst
            have hi3 : iter.start.val = 3 := congrArg UScalar.val hfirst
            have htop : n >>> 253 < 8 := by
              rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]
              simpa [show (8 : ℕ) = 2^3 by norm_num, ← pow_add] using hn
            have ha0 : a = 0 := by
              have hp := hprefix
              rw [hi3] at hp
              norm_num at hp
              omega
            apply (WP.spec_ok _).mpr
            simpa [ha0] using hres
        change (do
          let res1 ← if iter.start != 3#usize then fourDoubles res else ok res
          _) ⦃ _ ⦄
        step with hresWindow as ⟨res1, hres1⟩
        change scanAddThen table res1 bits2 (fun res2 => _) ⦃ _ ⦄
        rw [scanAddThen_eq]
        step with addSelected_spec htable hres1 bits2 hbits2Bound as ⟨res2, hres2⟩
        have hres2' : Represents res2 ((16 * a + bits2.val) • base) := by
          simpa only [add_nsmul] using hres2
        have hpstep := prefix_step n iter.start.val hi
        have hpnew : n >>> (256 - (iter.start.val + 1)) =
            16 * a + bits2.val :=
          fullwindow_arithmetic iter.start.val a bits.val
            (natBit n (255 - iter.start.val)) bits2.val
            (n >>> (256 - iter.start.val))
            (n >>> (256 - (iter.start.val + 1))) hwindowNat hprefix hpstep hbits2Val
        refine ⟨?_, ?_⟩
        · refine ⟨by rw [hoend]; exact hend, by rw [hstart1]; omega,
            16 * a + bits2.val, hres2', ?_, by simp, ?_⟩
          · rw [hstart1, hwindowNat]
            simpa using hpnew
          · rw [hstart1]
            simpa only [show 256 - (iter.start.val + 1) = 255 - iter.start.val by omega]
              using hfuture2
        · rw [hstart1]
          omega
      · rename_i hwindow
        have hwindowNat : (iter.start.val + 1) % 4 ≠ 0 := by
          intro hz
          apply hwindow
          apply UScalar.eq_of_val_eq
          rw [hwindowVal', hz]
          norm_num
        have hpstep := prefix_step n iter.start.val hi
        obtain ⟨hpnew, hbitsNew⟩ :=
          nonwindow_arithmetic iter.start.val a bits.val
            (natBit n (255 - iter.start.val)) bits2.val
            (n >>> (256 - iter.start.val))
            (n >>> (256 - (iter.start.val + 1))) hwindowNat hprefix hpstep hbits2Val
            hbits (natBit_lt_two n (255 - iter.start.val))
        refine ⟨?_, ?_⟩
        · refine ⟨by rw [hoend]; exact hend, by rw [hstart1]; omega,
            a, hres, ?_, ?_, ?_⟩
          · rw [hstart1]
            exact hpnew
          · rw [hstart1]
            exact hbitsNew
          · rw [hstart1]
            simpa only [show 256 - (iter.start.val + 1) = 255 - iter.start.val by omega]
              using hfuture2
        · rw [hstart1]
          omega
    · rename_i hnotlt
      obtain ⟨ho1, hstart1⟩ := ho
      simp only [ho1, WP.spec_ok]
      have hi256 : iter.start.val = 256 := by omega
      have hbits0 : bits.val = 0 := by
        have hb := hbits
        rw [hi256] at hb
        norm_num at hb
        omega
      have ha : a = n := by
        have hp := hprefix
        rw [hi256, hbits0] at hp
        norm_num at hp
        omega
      simpa [ha] using hres
  · refine ⟨by norm_num, by norm_num, 0, ?_, ?_, by norm_num,
      scalarBytes_futureBits n⟩
    · simpa using (represents_raw Selene.idP)
    · change n >>> 256 = 0
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hn]

/-- The concrete dalek scalar model serializes its canonical `ZMod` value as
32 little-endian bytes.

This is the load-bearing Selene representation assumption corresponding to
Rust `FieldElement::to_repr` and `PrimeFieldBits::to_le_bits`. The latter is not
translated in hunk 8; human equivalence review establishes that production
Rust's bitvec view is exactly the bytes specified here. -/
theorem dalek_to_repr_spec (scalar : dalek_ff_group.field.FieldElement) :
    dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.to_repr scalar
      ⦃ bytes => bytes = scalarBytes scalar.toZMod.val ⦄ :=
  (WP.spec_ok _).mpr rfl

/-- The public generated Selene multiplication returns a verified
representative of natural repeated addition by the scalar's canonical value.

This proof follows the public generated body in order: obtain identity, execute
each concrete table assignment, call the concrete dalek `to_repr` model, run
the verified generated loop, zeroize the remaining byte array, zeroize the
scalar temporary, and return the loop point. The postcondition is
`scalar.toZMod.val • SClass.mk P`; the successful raw result also carries an
`SPt` witness. No alternate multiplication function or failure default is
introduced. -/
theorem mul_spec (P : SPt) (scalar : dalek_ff_group.field.FieldElement) :
    point.selene.SelenePoint.Insts.CoreOpsArithMulFieldElementSelenePoint.mul P.1 scalar
      ⦃ out => Represents out (scalar.toZMod.val • SClass.mk P) ⦄ := by
  let base := SClass.mk P
  let n := scalar.toZMod.val
  have hP : Represents P.1 base := represents_raw P
  have hn : n < 2^255 := by
    have hnq := scalar.toZMod.val_lt
    dsimp only [n]
    norm_num at hnq ⊢
    omega
  have hn256 : n < 2^256 := lt_trans hn (by norm_num)
  unfold point.selene.SelenePoint.Insts.CoreOpsArithMulFieldElementSelenePoint.mul
  step with identity_exact_spec as ⟨sp, hspEq⟩
  have hsp : Represents sp 0 := by
    rw [hspEq]
    exact ⟨Selene.idP, rfl, Selene.SClass_zero_def.symm⟩
  have htable0 : TablePrefix (Aeneas.Std.Array.repeat 16#usize sp) base 1 :=
    table_repeat_zero_prefix hsp
  step with htable0.update_next_spec (by norm_num) 1#usize (by norm_num) P.1
    (by simpa using hP) as ⟨table1, htable1⟩
  have hP1 : Represents P.1 (1 • base) := by simpa using hP
  step with doubleMultiple_spec 1 hP1 as ⟨sp1, hsp1⟩
  have hsp1' : Represents sp1 (2 • base) := by simpa using hsp1
  step with htable1.update_next_spec (by norm_num) 2#usize (by norm_num) sp1 hsp1'
    as ⟨table2, htable2⟩
  step with htable2.index_spec 2#usize (by norm_num) as ⟨sp2, hsp2⟩
  have hsp2' : Represents sp2 (2 • base) := by simpa using hsp2
  step with addBase_spec 2 hsp2' hP as ⟨sp3, hsp3⟩
  have hsp3' : Represents sp3 (3 • base) := by simpa using hsp3
  step with htable2.update_next_spec (by norm_num) 3#usize (by norm_num) sp3 hsp3'
    as ⟨table3, htable3⟩
  step with htable3.index_spec 2#usize (by norm_num) as ⟨sp4, hsp4⟩
  have hsp4' : Represents sp4 (2 • base) := by simpa using hsp4
  step with doubleMultiple_spec 2 hsp4' as ⟨sp5, hsp5⟩
  have hsp5' : Represents sp5 (4 • base) := by simpa using hsp5
  step with htable3.update_next_spec (by norm_num) 4#usize (by norm_num) sp5 hsp5'
    as ⟨table4, htable4⟩
  step with htable4.index_spec 4#usize (by norm_num) as ⟨sp6, hsp6⟩
  have hsp6' : Represents sp6 (4 • base) := by simpa using hsp6
  step with addBase_spec 4 hsp6' hP as ⟨sp7, hsp7⟩
  have hsp7' : Represents sp7 (5 • base) := by simpa using hsp7
  step with htable4.update_next_spec (by norm_num) 5#usize (by norm_num) sp7 hsp7'
    as ⟨table5, htable5⟩
  step with htable5.index_spec 3#usize (by norm_num) as ⟨sp8, hsp8⟩
  have hsp8' : Represents sp8 (3 • base) := by simpa using hsp8
  step with doubleMultiple_spec 3 hsp8' as ⟨sp9, hsp9⟩
  have hsp9' : Represents sp9 (6 • base) := by simpa using hsp9
  step with htable5.update_next_spec (by norm_num) 6#usize (by norm_num) sp9 hsp9'
    as ⟨table6, htable6⟩
  step with htable6.index_spec 6#usize (by norm_num) as ⟨sp10, hsp10⟩
  have hsp10' : Represents sp10 (6 • base) := by simpa using hsp10
  step with addBase_spec 6 hsp10' hP as ⟨sp11, hsp11⟩
  have hsp11' : Represents sp11 (7 • base) := by simpa using hsp11
  step with htable6.update_next_spec (by norm_num) 7#usize (by norm_num) sp11 hsp11'
    as ⟨table7, htable7⟩
  step with htable7.index_spec 4#usize (by norm_num) as ⟨sp12, hsp12⟩
  have hsp12' : Represents sp12 (4 • base) := by simpa using hsp12
  step with doubleMultiple_spec 4 hsp12' as ⟨sp13, hsp13⟩
  have hsp13' : Represents sp13 (8 • base) := by simpa using hsp13
  step with htable7.update_next_spec (by norm_num) 8#usize (by norm_num) sp13 hsp13'
    as ⟨table8, htable8⟩
  step with htable8.index_spec 8#usize (by norm_num) as ⟨sp14, hsp14⟩
  have hsp14' : Represents sp14 (8 • base) := by simpa using hsp14
  step with addBase_spec 8 hsp14' hP as ⟨sp15, hsp15⟩
  have hsp15' : Represents sp15 (9 • base) := by simpa using hsp15
  step with htable8.update_next_spec (by norm_num) 9#usize (by norm_num) sp15 hsp15'
    as ⟨table9, htable9⟩
  step with htable9.index_spec 5#usize (by norm_num) as ⟨sp16, hsp16⟩
  have hsp16' : Represents sp16 (5 • base) := by simpa using hsp16
  step with doubleMultiple_spec 5 hsp16' as ⟨sp17, hsp17⟩
  have hsp17' : Represents sp17 (10 • base) := by simpa using hsp17
  step with htable9.update_next_spec (by norm_num) 10#usize (by norm_num) sp17 hsp17'
    as ⟨table10, htable10⟩
  step with htable10.index_spec 10#usize (by norm_num) as ⟨sp18, hsp18⟩
  have hsp18' : Represents sp18 (10 • base) := by simpa using hsp18
  step with addBase_spec 10 hsp18' hP as ⟨sp19, hsp19⟩
  have hsp19' : Represents sp19 (11 • base) := by simpa using hsp19
  step with htable10.update_next_spec (by norm_num) 11#usize (by norm_num) sp19 hsp19'
    as ⟨table11, htable11⟩
  step with htable11.index_spec 6#usize (by norm_num) as ⟨sp20, hsp20⟩
  have hsp20' : Represents sp20 (6 • base) := by simpa using hsp20
  step with doubleMultiple_spec 6 hsp20' as ⟨sp21, hsp21⟩
  have hsp21' : Represents sp21 (12 • base) := by simpa using hsp21
  step with htable11.update_next_spec (by norm_num) 12#usize (by norm_num) sp21 hsp21'
    as ⟨table12, htable12⟩
  step with htable12.index_spec 12#usize (by norm_num) as ⟨sp22, hsp22⟩
  have hsp22' : Represents sp22 (12 • base) := by simpa using hsp22
  step with addBase_spec 12 hsp22' hP as ⟨sp23, hsp23⟩
  have hsp23' : Represents sp23 (13 • base) := by simpa using hsp23
  step with htable12.update_next_spec (by norm_num) 13#usize (by norm_num) sp23 hsp23'
    as ⟨table13, htable13⟩
  step with htable13.index_spec 7#usize (by norm_num) as ⟨sp24, hsp24⟩
  have hsp24' : Represents sp24 (7 • base) := by simpa using hsp24
  step with doubleMultiple_spec 7 hsp24' as ⟨sp25, hsp25⟩
  have hsp25' : Represents sp25 (14 • base) := by simpa using hsp25
  step with htable13.update_next_spec (by norm_num) 14#usize (by norm_num) sp25 hsp25'
    as ⟨table14, htable14⟩
  step with htable14.index_spec 14#usize (by norm_num) as ⟨sp26, hsp26⟩
  have hsp26' : Represents sp26 (14 • base) := by simpa using hsp26
  step with addBase_spec 14 hsp26' hP as ⟨sp27, hsp27⟩
  have hsp27' : Represents sp27 (15 • base) := by simpa using hsp27
  step with htable14.update_next_spec (by norm_num) 15#usize (by norm_num) sp27 hsp27'
    as ⟨table15, htable15⟩
  step with dalek_to_repr_spec scalar as ⟨bytes, hbytes⟩
  rw [hbytes]
  rw [hspEq]
  step with mul_loop_spec table15 base htable15 n hn256
    as ⟨res, remainingBytes, hloop⟩
  step with u8Array_zeroize_total remainingBytes as ⟨zeroBytes⟩
  unfold dalek_ff_group.field.FieldElement.Insts.ZeroizeZeroize.zeroize
  simp only [bind_tc_ok]
  simpa [base, n] using hloop

end SeleneLadder

/-! ## 5. Helios ladder correctness

The generated Helios ladder has the same source shape as Selene because both
come from `curve!`, but its two field roles are reversed:

* point coordinates are `dalek_ff_group::FieldElement`, represented here by
  the idealized `ZMod (2^255 - 19)` external model inherited from the Helios
  group-law proof; and
* the scalar is the crate's `HelioseleneField`, whose generated type is the raw
  four-limb `Uint 4` and whose serialization is translated verified code.

The generic public theorem below intentionally accepts every raw generated
scalar value and proves multiplication by its full natural value below
`2^256`. Section 6 restricts the law-bearing scalar action to `HField`, the
verified reduced subtype, because scalar addition/multiplication and their
field laws live there.

The Selene-shaped proof is repeated against the concrete `point.helios.*`
definitions. This keeps the audit trail direct and makes the idealized
coordinate dependency visible at each add, double, and conditional select. -/

namespace HeliosLadder

open Helios

abbrev RawPoint := point.helios.HeliosPoint

-- `getElem!` requires an inhabitant while stating generic array lemmas. All
-- actual table indices are proved in bounds, so this value is never selected
-- as a fallback and cannot become the ladder result.
private instance : Inhabited dalek_ff_group.field.FieldElement where
  default := .ofZMod 0

private instance : Inhabited RawPoint where
  default := { x := default, y := default, z := default }

/-- A raw generated Helios point is a valid on-curve representative of `x`.

This witness is the domain restriction absent from Rust's raw point type. It
lets the proof reuse the Helios group-law contracts while making no claim for
off-curve coordinates. -/
def Represents (raw : RawPoint) (x : HClass) : Prop :=
  ∃ P : HPt, raw = P.1 ∧ HClass.mk P = x

theorem represents_raw (P : HPt) : Represents P.1 (HClass.mk P) :=
  ⟨P, rfl, rfl⟩

/-- The generated componentwise Helios selection has the required value
semantics: choose `B` iff `c` is true.

This unfolds through the idealized dalek coordinate-selection model. It is a
functional statement only, not a constant-time or memory-access theorem. -/
theorem point_select_eq (A B : RawPoint) (c : subtle.Choice) :
    point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select A B c
      = .ok (if c then B else A) := by
  by_cases hc : c = true
  · simp only [hc, ↓reduceIte]
    rfl
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- The generated Helios identity returns the exact verified identity
representative, not merely an equivalent class. -/
theorem identity_exact_spec :
    point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.identity
      ⦃ raw => raw = Helios.idP.1 ⦄ := by
  rw [Helios.idP_ok]
  exact (WP.spec_ok _).mpr rfl

/-- The generated Helios identity represents quotient-group zero. -/
theorem identity_spec :
    point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.identity
      ⦃ raw => Represents raw 0 ⦄ := by
  rw [Helios.idP_ok]
  apply (WP.spec_ok _).mpr
  exact ⟨Helios.idP, rfl, Helios.HClass_zero_def.symm⟩

/-- The generated dedicated Helios doubling circuit represents natural
doubling in `HClass`. This imports the already-proved raw-operation contract
from `Spec/Helios/GroupLaw.lean`. -/
theorem double_spec {raw : RawPoint} {x : HClass} (h : Represents raw x) :
    point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.double raw
      ⦃ out => Represents out (2 • x) ⦄ := by
  obtain ⟨P, hraw, hP⟩ := h
  rw [hraw, Helios.doubleP_ok]
  apply (WP.spec_ok _).mpr
  refine ⟨Helios.doubleP P, rfl, ?_⟩
  rw [Helios.HClass_double, hP]
  exact (two_nsmul x).symm

theorem doubleMultiple_spec {raw : RawPoint} {base : HClass} (j : ℕ)
    (h : Represents raw (j • base)) :
    point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.double raw
      ⦃ out => Represents out ((2 * j) • base) ⦄ := by
  apply WP.spec_mono (double_spec h)
  intro out hout
  simpa only [← mul_smul] using hout

/-- The generated complete Helios addition circuit represents addition in
`HClass`, while retaining an on-curve representative witness. -/
theorem add_spec {raw₁ raw₂ : RawPoint} {x y : HClass}
    (h₁ : Represents raw₁ x) (h₂ : Represents raw₂ y) :
    point.helios.HeliosPoint.Insts.CoreOpsArithAddHeliosPointHeliosPoint.add raw₁ raw₂
      ⦃ out => Represents out (x + y) ⦄ := by
  obtain ⟨P, hraw₁, hP⟩ := h₁
  obtain ⟨Q, hraw₂, hQ⟩ := h₂
  rw [hraw₁, hraw₂, Helios.addP_ok]
  apply (WP.spec_ok _).mpr
  refine ⟨Helios.addP P Q, rfl, ?_⟩
  rw [← Helios.HClass_add_def, hP, hQ]

theorem addBase_spec {raw baseRaw : RawPoint} {base : HClass} (j : ℕ)
    (hraw : Represents raw (j • base)) (hbase : Represents baseRaw base) :
    point.helios.HeliosPoint.Insts.CoreOpsArithAddHeliosPointHeliosPoint.add raw baseRaw
      ⦃ out => Represents out ((j + 1) • base) ⦄ := by
  apply WP.spec_mono (add_spec hraw hbase)
  intro out hout
  simpa only [add_nsmul, one_nsmul] using hout

/-- The exact four unrolled Helios doubles emitted from hunk 8. This proof-only
fold unfolds to the generated block and represents multiplication by 16. -/
def fourDoubles (raw : RawPoint) : Result RawPoint := do
  let raw1 ←
    point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.double raw
  let raw2 ←
    point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.double raw1
  let raw3 ←
    point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.double raw2
  point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.double raw3

theorem fourDoubles_spec {raw : RawPoint} {x : HClass} (h : Represents raw x) :
    fourDoubles raw ⦃ out => Represents out (16 • x) ⦄ := by
  unfold fourDoubles
  step with double_spec h as ⟨raw1, h1⟩
  step with double_spec h1 as ⟨raw2, h2⟩
  step with double_spec h2 as ⟨raw3, h3⟩
  step with double_spec h3 as ⟨raw4, h4⟩
  simpa only [← mul_smul] using h4

/-- Entries below `limit` contain the corresponding natural multiples of the
base. The generated optimized assignment order is checked one update at a
time against this invariant. -/
def TablePrefix (table : Aeneas.Std.Array RawPoint 16#usize)
    (base : HClass) (limit : ℕ) : Prop :=
  limit ≤ 16 ∧ ∀ j, j < limit → Represents table.val[j]! (j • base)

theorem table_repeat_zero_prefix {raw : RawPoint} {base : HClass}
    (hraw : Represents raw 0) :
    TablePrefix (Aeneas.Std.Array.repeat 16#usize raw) base 1 := by
  refine ⟨by norm_num, ?_⟩
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  simpa [Aeneas.Std.Array.repeat_val] using hraw

theorem TablePrefix.set_next
    {table : Aeneas.Std.Array RawPoint 16#usize} {base : HClass} {limit : ℕ}
    (hlimit : limit < 16) (hprefix : TablePrefix table base limit)
    (index : Std.Usize) (hindex : index.val = limit)
    (raw : RawPoint) (hraw : Represents raw (limit • base)) :
    TablePrefix (table.set index raw) base (limit + 1) := by
  obtain ⟨_, hprefix⟩ := hprefix
  refine ⟨by omega, ?_⟩
  intro j hj
  rw [Aeneas.Std.Array.set_val_eq]
  have hi : index.val < table.val.length := by
    rw [table.property, hindex]
    norm_num
    omega
  have hjlen : j < table.val.length := by
    rw [table.property]
    norm_num
    omega
  rw [list_getElem!_set table.val raw index.val j hi hjlen]
  by_cases hij : index.val = j
  · rw [if_pos hij]
    have : j = limit := by omega
    subst j
    simpa [hindex] using hraw
  · rw [if_neg hij]
    exact hprefix j (by omega)

theorem TablePrefix.update_next_spec
    {table : Aeneas.Std.Array RawPoint 16#usize} {base : HClass} {limit : ℕ}
    (hprefix : TablePrefix table base limit) (hlimit : limit < 16)
    (index : Std.Usize) (hindex : index.val = limit)
    (raw : RawPoint) (hraw : Represents raw (limit • base)) :
    Aeneas.Std.Array.update table index raw
      ⦃ out => TablePrefix out base (limit + 1) ⦄ := by
  apply WP.spec_mono (Aeneas.Std.Array.update_spec table index raw (by scalar_tac))
  intro out hout
  rw [hout]
  exact TablePrefix.set_next hlimit hprefix index hindex raw hraw

theorem TablePrefix.index_spec
    {table : Aeneas.Std.Array RawPoint 16#usize} {base : HClass} {limit : ℕ}
    (hprefix : TablePrefix table base limit)
    (index : Std.Usize) (hindex : index.val < limit) :
    Aeneas.Std.Array.index_usize table index
      ⦃ raw => Represents raw (index.val • base) ⦄ := by
  obtain ⟨hlimit, hprefix⟩ := hprefix
  have hib : index.val < table.val.length := by
    rw [table.property]
    norm_num
    omega
  apply WP.spec_mono (Aeneas.Std.Array.index_usize_spec table index (by simpa using hib))
  intro raw hraw
  rw [hraw]
  have h := hprefix index.val hindex
  rw [getElem!_pos table.val index.val hib] at h
  exact h

/-- The exact unrolled Helios scan returns the verified multiple named by the
pending four-bit window. Its value proof uses `point_select_eq`; timing remains
outside the model. -/
theorem TablePrefix.select_spec
    {table : Aeneas.Std.Array RawPoint 16#usize} {base : HClass}
    (hprefix : TablePrefix table base 16) (bits : Std.U8) (hbits : bits.val < 16) :
    select16
      point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
      table bits ⦃ raw => Represents raw (bits.val • base) ⦄ := by
  apply WP.spec_mono (select16_spec _ point_select_eq table bits hbits)
  intro raw hraw
  rw [hraw]
  exact hprefix.2 bits.val hbits

/-- Proof-only fold for the generated full table scan followed by one Helios
point addition. -/
def addSelected (table : Aeneas.Std.Array RawPoint 16#usize)
    (raw : RawPoint) (bits : Std.U8) : Result RawPoint := do
  let term ← select16
    point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits
  point.helios.HeliosPoint.Insts.CoreOpsArithAddHeliosPointHeliosPoint.add raw term

theorem addSelected_spec
    {table : Aeneas.Std.Array RawPoint 16#usize} {base x : HClass}
    (htable : TablePrefix table base 16) {raw : RawPoint} (hraw : Represents raw x)
    (bits : Std.U8) (hbits : bits.val < 16) :
    addSelected table raw bits
      ⦃ out => Represents out (x + bits.val • base) ⦄ := by
  unfold addSelected
  step with htable.select_spec bits hbits as ⟨term, hterm⟩
  step with add_spec hraw hterm as ⟨out, hout⟩
  exact hout

/-- Continuation-passing spelling of the exact unrolled Helios scan and add.
Unfolding this definition yields the corresponding generated
`mul_loop.body` block verbatim. -/
def scanAddThen {T : Type} (table : Aeneas.Std.Array RawPoint 16#usize)
    (raw : RawPoint) (bits : Std.U8) (k : RawPoint → Result T) : Result T := do
  let term0 ← Aeneas.Std.Array.index_usize table 0#usize
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 1#usize term0 fun term1 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 2#usize term1 fun term2 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 3#usize term2 fun term3 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 4#usize term3 fun term4 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 5#usize term4 fun term5 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 6#usize term5 fun term6 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 7#usize term6 fun term7 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 8#usize term7 fun term8 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 9#usize term8 fun term9 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 10#usize term9 fun term10 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 11#usize term10 fun term11 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 12#usize term11 fun term12 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 13#usize term12 fun term13 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 14#usize term13 fun term14 =>
  selectCandidateThen point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
    table bits 15#usize term14 fun term15 => do
  let out ←
    point.helios.HeliosPoint.Insts.CoreOpsArithAddHeliosPointHeliosPoint.add raw term15
  k out

theorem scanAddThen_eq {T : Type}
    (table : Aeneas.Std.Array RawPoint 16#usize) (raw : RawPoint) (bits : Std.U8)
    (k : RawPoint → Result T) :
    scanAddThen table raw bits k = (do
      let out ← addSelected table raw bits
      k out) := by
  simp only [scanAddThen, selectCandidateThen, addSelected, select16, selectCandidate,
    bind_assoc_eq]

abbrev LoopState :=
  core.ops.range.Range Std.Usize × RawPoint × Std.U8 ×
    Aeneas.Std.Array Std.U8 32#usize

/-- The Helios scalar-loop invariant.

For iteration `i`, the accumulator represents `a • base`, the processed high
prefix is `2^(i % 4) * a + bits`, `bits` is in the pending-window range, and
every lower unread bit still agrees with `n`. At a completed window this gives
the update `a := 16*a + bits`; at the first window the generated skipped
doubles are sound because the prior `a` is proved zero. -/
def LoopInv (n : ℕ) (base : HClass) (st : LoopState) : Prop :=
  st.1.«end».val = 256 ∧ st.1.start.val ≤ 256 ∧
    ∃ a : ℕ,
      Represents st.2.1 (a • base) ∧
      n >>> (256 - st.1.start.val) =
        2^(st.1.start.val % 4) * a + st.2.2.1.val ∧
      st.2.2.1.val < 2^(st.1.start.val % 4) ∧
      FutureBits st.2.2.2 n (256 - st.1.start.val)

/-- The complete generated Helios loop terminates and returns natural repeated
addition for every raw 256-bit scalar value.

The decreasing measure is `256 - i`. The proof checks all generated branches,
all 64 completed windows, every fixed table scan, all byte/table bounds, and
the full top-bit case. Its target is the concrete Helios `mul_loop`, not a
shared mathematical reimplementation. -/
theorem mul_loop_spec
    (table : Aeneas.Std.Array RawPoint 16#usize) (base : HClass)
    (htable : TablePrefix table base 16) (n : ℕ) (hn : n < 2^256) :
    point.helios.HeliosPoint.Insts.CoreOpsArithMulHelioseleneFieldHeliosPoint.mul_loop
      { start := 0#usize, «end» := 256#usize } table Helios.idP.1 0#u8
        (scalarBytes n)
      ⦃ out => Represents out.1 (n • base) ⦄ := by
  unfold point.helios.HeliosPoint.Insts.CoreOpsArithMulHelioseleneFieldHeliosPoint.mul_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (st : LoopState) => 256 - st.1.start.val)
    (inv := LoopInv n base)
  · rintro ⟨iter, res, bits, bytes⟩ hinv
    obtain ⟨hend, hstartBound, a, hres, hprefix, hbits, hfuture⟩ := hinv
    dsimp only at hend hstartBound hres hprefix hbits hfuture ⊢
    unfold point.helios.HeliosPoint.Insts.CoreOpsArithMulHelioseleneFieldHeliosPoint.mul_loop.body
    step as ⟨o, iter1, ho, hoend⟩
    split at ho
    · rename_i hlt
      obtain ⟨ho1, hstart1⟩ := ho
      simp only [ho1]
      have hi : iter.start.val < 256 := by omega
      change consumeScalarBitThen iter.start bits bytes (fun bits2 bytes1 => _)
        ⦃ _ ⦄
      rw [consumeScalarBitThen_eq]
      have hbits8 : bits.val < 8 := by
        have hmod : iter.start.val % 4 ≤ 3 := by
          have := Nat.mod_lt iter.start.val (by norm_num : 0 < 4)
          omega
        have hpow : 2^(iter.start.val % 4) ≤ (2 : ℕ)^3 :=
          pow_le_pow_right' (by norm_num) hmod
        norm_num at hpow
        exact lt_of_lt_of_le hbits hpow
      step with consumeScalarBit_spec n iter.start hi bits hbits8
        bytes hfuture as ⟨consumed, hbits2Val, hbits2Bound, hfuture2⟩
      rcases consumed with ⟨bits2, bytes1⟩
      step with lift_spec (Std.Usize.wrapping_add iter.start 1#usize) as ⟨nextI, hnextI⟩
      have hnextIVal : nextI.val = iter.start.val + 1 := by
        rw [hnextI]
        exact usize_wrapping_add_one_val iter.start hi
      step as ⟨window, hwindowVal⟩
      have hwindowVal' : window.val = (iter.start.val + 1) % 4 := by
        rw [hwindowVal, hnextIVal]
      split
      · rename_i hwindow
        have hwindowNat : (iter.start.val + 1) % 4 = 0 := by
          rw [← hwindowVal']
          exact congrArg UScalar.val hwindow
        have hresWindow :
            (if iter.start != 3#usize then fourDoubles res else ok res)
              ⦃ out => Represents out ((16 * a) • base) ⦄ := by
          split
          · apply WP.spec_mono (fourDoubles_spec hres)
            intro out hout
            simpa only [← mul_smul] using hout
          · rename_i hfirst
            simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hfirst
            have hi3 : iter.start.val = 3 := congrArg UScalar.val hfirst
            have htop : n >>> 253 < 8 := by
              rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]
              simpa [show (8 : ℕ) = 2^3 by norm_num, ← pow_add] using hn
            have ha0 : a = 0 := by
              have hp := hprefix
              rw [hi3] at hp
              norm_num at hp
              omega
            apply (WP.spec_ok _).mpr
            simpa [ha0] using hres
        change (do
          let res1 ← if iter.start != 3#usize then fourDoubles res else ok res
          _) ⦃ _ ⦄
        step with hresWindow as ⟨res1, hres1⟩
        change scanAddThen table res1 bits2 (fun res2 => _) ⦃ _ ⦄
        rw [scanAddThen_eq]
        step with addSelected_spec htable hres1 bits2 hbits2Bound as ⟨res2, hres2⟩
        have hres2' : Represents res2 ((16 * a + bits2.val) • base) := by
          simpa only [add_nsmul] using hres2
        have hpstep := prefix_step n iter.start.val hi
        have hpnew : n >>> (256 - (iter.start.val + 1)) =
            16 * a + bits2.val :=
          fullwindow_arithmetic iter.start.val a bits.val
            (natBit n (255 - iter.start.val)) bits2.val
            (n >>> (256 - iter.start.val))
            (n >>> (256 - (iter.start.val + 1))) hwindowNat hprefix hpstep hbits2Val
        refine ⟨?_, ?_⟩
        · refine ⟨by rw [hoend]; exact hend, by rw [hstart1]; omega,
            16 * a + bits2.val, hres2', ?_, by simp, ?_⟩
          · rw [hstart1, hwindowNat]
            simpa using hpnew
          · rw [hstart1]
            simpa only [show 256 - (iter.start.val + 1) = 255 - iter.start.val by omega]
              using hfuture2
        · rw [hstart1]
          omega
      · rename_i hwindow
        have hwindowNat : (iter.start.val + 1) % 4 ≠ 0 := by
          intro hz
          apply hwindow
          apply UScalar.eq_of_val_eq
          rw [hwindowVal', hz]
          norm_num
        have hpstep := prefix_step n iter.start.val hi
        obtain ⟨hpnew, hbitsNew⟩ :=
          nonwindow_arithmetic iter.start.val a bits.val
            (natBit n (255 - iter.start.val)) bits2.val
            (n >>> (256 - iter.start.val))
            (n >>> (256 - (iter.start.val + 1))) hwindowNat hprefix hpstep hbits2Val
            hbits (natBit_lt_two n (255 - iter.start.val))
        refine ⟨?_, ?_⟩
        · refine ⟨by rw [hoend]; exact hend, by rw [hstart1]; omega,
            a, hres, ?_, ?_, ?_⟩
          · rw [hstart1]
            exact hpnew
          · rw [hstart1]
            exact hbitsNew
          · rw [hstart1]
            simpa only [show 256 - (iter.start.val + 1) = 255 - iter.start.val by omega]
              using hfuture2
        · rw [hstart1]
          omega
    · rename_i hnotlt
      obtain ⟨ho1, hstart1⟩ := ho
      simp only [ho1, WP.spec_ok]
      have hi256 : iter.start.val = 256 := by omega
      have hbits0 : bits.val = 0 := by
        have hb := hbits
        rw [hi256] at hb
        norm_num at hb
        omega
      have ha : a = n := by
        have hp := hprefix
        rw [hi256, hbits0] at hp
        norm_num at hp
        omega
      simpa [ha] using hres
  · refine ⟨by norm_num, by norm_num, 0, ?_, ?_, by norm_num,
      scalarBytes_futureBits n⟩
    · simpa using (represents_raw Helios.idP)
    · change n >>> 256 = 0
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hn]

/-- The translated Helios scalar serialization is exactly the 32-byte
little-endian decomposition of its four-limb natural value. Unlike Selene's
dalek serialization, this path unfolds translated `field::verified::to_repr`
and the concrete `Uint4::to_le_bytes` model. -/
theorem helios_to_repr_spec (scalar : field.HelioseleneField) :
    field.HelioseleneField.Insts.FfPrimeFieldArrayU832.to_repr scalar
      ⦃ bytes => bytes = scalarBytes scalar.toNat ⦄ := by
  unfold field.HelioseleneField.Insts.FfPrimeFieldArrayU832.to_repr
    field.verified.to_repr
    crypto_bigint.uint.Uint4.Insts.Crypto_bigintTraitsEncodingArrayU832.to_le_bytes
  exact (WP.spec_ok _).mpr rfl

/-- The public generated Helios multiplication returns a verified
representative of natural repeated addition by the raw scalar value.

The proof executes the generated body in source order: exact identity,
optimized assignments for all 16 table entries, translated scalar
serialization, the concrete 256-iteration loop, byte-array zeroization, and
scalar zeroization. It accepts raw generated `HelioseleneField` values and
therefore proves the stronger full-`Uint4` claim. The law-bearing action in the
next section invokes this theorem on `HField.val`. -/
theorem mul_spec (P : HPt) (scalar : field.HelioseleneField) :
    point.helios.HeliosPoint.Insts.CoreOpsArithMulHelioseleneFieldHeliosPoint.mul
      P.1 scalar ⦃ out => Represents out (scalar.toNat • HClass.mk P) ⦄ := by
  let base := HClass.mk P
  let n := scalar.toNat
  have hP : Represents P.1 base := represents_raw P
  have hn : n < 2^256 := Uint4.toNat_lt scalar
  unfold point.helios.HeliosPoint.Insts.CoreOpsArithMulHelioseleneFieldHeliosPoint.mul
  step with identity_exact_spec as ⟨hp, hpEq⟩
  have hhp : Represents hp 0 := by
    rw [hpEq]
    exact ⟨Helios.idP, rfl, Helios.HClass_zero_def.symm⟩
  have htable0 : TablePrefix (Aeneas.Std.Array.repeat 16#usize hp) base 1 :=
    table_repeat_zero_prefix hhp
  step with htable0.update_next_spec (by norm_num) 1#usize (by norm_num) P.1
    (by simpa using hP) as ⟨table1, htable1⟩
  have hP1 : Represents P.1 (1 • base) := by simpa using hP
  step with doubleMultiple_spec 1 hP1 as ⟨hp1, hhp1⟩
  have hhp1' : Represents hp1 (2 • base) := by simpa using hhp1
  step with htable1.update_next_spec (by norm_num) 2#usize (by norm_num) hp1 hhp1'
    as ⟨table2, htable2⟩
  step with htable2.index_spec 2#usize (by norm_num) as ⟨hp2, hhp2⟩
  have hhp2' : Represents hp2 (2 • base) := by simpa using hhp2
  step with addBase_spec 2 hhp2' hP as ⟨hp3, hhp3⟩
  have hhp3' : Represents hp3 (3 • base) := by simpa using hhp3
  step with htable2.update_next_spec (by norm_num) 3#usize (by norm_num) hp3 hhp3'
    as ⟨table3, htable3⟩
  step with htable3.index_spec 2#usize (by norm_num) as ⟨hp4, hhp4⟩
  have hhp4' : Represents hp4 (2 • base) := by simpa using hhp4
  step with doubleMultiple_spec 2 hhp4' as ⟨hp5, hhp5⟩
  have hhp5' : Represents hp5 (4 • base) := by simpa using hhp5
  step with htable3.update_next_spec (by norm_num) 4#usize (by norm_num) hp5 hhp5'
    as ⟨table4, htable4⟩
  step with htable4.index_spec 4#usize (by norm_num) as ⟨hp6, hhp6⟩
  have hhp6' : Represents hp6 (4 • base) := by simpa using hhp6
  step with addBase_spec 4 hhp6' hP as ⟨hp7, hhp7⟩
  have hhp7' : Represents hp7 (5 • base) := by simpa using hhp7
  step with htable4.update_next_spec (by norm_num) 5#usize (by norm_num) hp7 hhp7'
    as ⟨table5, htable5⟩
  step with htable5.index_spec 3#usize (by norm_num) as ⟨hp8, hhp8⟩
  have hhp8' : Represents hp8 (3 • base) := by simpa using hhp8
  step with doubleMultiple_spec 3 hhp8' as ⟨hp9, hhp9⟩
  have hhp9' : Represents hp9 (6 • base) := by simpa using hhp9
  step with htable5.update_next_spec (by norm_num) 6#usize (by norm_num) hp9 hhp9'
    as ⟨table6, htable6⟩
  step with htable6.index_spec 6#usize (by norm_num) as ⟨hp10, hhp10⟩
  have hhp10' : Represents hp10 (6 • base) := by simpa using hhp10
  step with addBase_spec 6 hhp10' hP as ⟨hp11, hhp11⟩
  have hhp11' : Represents hp11 (7 • base) := by simpa using hhp11
  step with htable6.update_next_spec (by norm_num) 7#usize (by norm_num) hp11 hhp11'
    as ⟨table7, htable7⟩
  step with htable7.index_spec 4#usize (by norm_num) as ⟨hp12, hhp12⟩
  have hhp12' : Represents hp12 (4 • base) := by simpa using hhp12
  step with doubleMultiple_spec 4 hhp12' as ⟨hp13, hhp13⟩
  have hhp13' : Represents hp13 (8 • base) := by simpa using hhp13
  step with htable7.update_next_spec (by norm_num) 8#usize (by norm_num) hp13 hhp13'
    as ⟨table8, htable8⟩
  step with htable8.index_spec 8#usize (by norm_num) as ⟨hp14, hhp14⟩
  have hhp14' : Represents hp14 (8 • base) := by simpa using hhp14
  step with addBase_spec 8 hhp14' hP as ⟨hp15, hhp15⟩
  have hhp15' : Represents hp15 (9 • base) := by simpa using hhp15
  step with htable8.update_next_spec (by norm_num) 9#usize (by norm_num) hp15 hhp15'
    as ⟨table9, htable9⟩
  step with htable9.index_spec 5#usize (by norm_num) as ⟨hp16, hhp16⟩
  have hhp16' : Represents hp16 (5 • base) := by simpa using hhp16
  step with doubleMultiple_spec 5 hhp16' as ⟨hp17, hhp17⟩
  have hhp17' : Represents hp17 (10 • base) := by simpa using hhp17
  step with htable9.update_next_spec (by norm_num) 10#usize (by norm_num) hp17 hhp17'
    as ⟨table10, htable10⟩
  step with htable10.index_spec 10#usize (by norm_num) as ⟨hp18, hhp18⟩
  have hhp18' : Represents hp18 (10 • base) := by simpa using hhp18
  step with addBase_spec 10 hhp18' hP as ⟨hp19, hhp19⟩
  have hhp19' : Represents hp19 (11 • base) := by simpa using hhp19
  step with htable10.update_next_spec (by norm_num) 11#usize (by norm_num) hp19 hhp19'
    as ⟨table11, htable11⟩
  step with htable11.index_spec 6#usize (by norm_num) as ⟨hp20, hhp20⟩
  have hhp20' : Represents hp20 (6 • base) := by simpa using hhp20
  step with doubleMultiple_spec 6 hhp20' as ⟨hp21, hhp21⟩
  have hhp21' : Represents hp21 (12 • base) := by simpa using hhp21
  step with htable11.update_next_spec (by norm_num) 12#usize (by norm_num) hp21 hhp21'
    as ⟨table12, htable12⟩
  step with htable12.index_spec 12#usize (by norm_num) as ⟨hp22, hhp22⟩
  have hhp22' : Represents hp22 (12 • base) := by simpa using hhp22
  step with addBase_spec 12 hhp22' hP as ⟨hp23, hhp23⟩
  have hhp23' : Represents hp23 (13 • base) := by simpa using hhp23
  step with htable12.update_next_spec (by norm_num) 13#usize (by norm_num) hp23 hhp23'
    as ⟨table13, htable13⟩
  step with htable13.index_spec 7#usize (by norm_num) as ⟨hp24, hhp24⟩
  have hhp24' : Represents hp24 (7 • base) := by simpa using hhp24
  step with doubleMultiple_spec 7 hhp24' as ⟨hp25, hhp25⟩
  have hhp25' : Represents hp25 (14 • base) := by simpa using hhp25
  step with htable13.update_next_spec (by norm_num) 14#usize (by norm_num) hp25 hhp25'
    as ⟨table14, htable14⟩
  step with htable14.index_spec 14#usize (by norm_num) as ⟨hp26, hhp26⟩
  have hhp26' : Represents hp26 (14 • base) := by simpa using hhp26
  step with addBase_spec 14 hhp26' hP as ⟨hp27, hhp27⟩
  have hhp27' : Represents hp27 (15 • base) := by simpa using hhp27
  step with htable14.update_next_spec (by norm_num) 15#usize (by norm_num) hp27 hhp27'
    as ⟨table15, htable15⟩
  step with helios_to_repr_spec scalar as ⟨bytes, hbytes⟩
  rw [hbytes, hpEq]
  step with mul_loop_spec table15 base htable15 n hn
    as ⟨res, remainingBytes, hloop⟩
  step with u8Array_zeroize_total remainingBytes as ⟨zeroBytes⟩
  unfold zeroize.Zeroize.Blanket.zeroize
  simpa [base, n] using hloop

end HeliosLadder

/-! ## 6. Descending exact generated results to scalar actions

The generated functions return `Result RawPoint`, while a law-bearing action
must be a total function on projective classes. The ladder specifications close
that gap without inventing a fallback:

1. `generated_mul_exists` obtains the successful raw output and its on-curve
   witness directly from `mul_spec`;
2. `mulP` uses `Classical.choice` to name that witness;
3. `mulP_generated` records that the exact generated function returns the
   chosen representative, while `mulP_class` records its mathematical class;
4. `classSmul` descends this representative through projective equivalence;
5. the `SMul` instance is this descended function; and
6. `smul_eq_nsmul` proves it equals canonical natural repeated addition.

`Classical.choice` is therefore an extraction mechanism, not an implementation
assumption: the generated `.ok` equation pins the selected witness. The
`result_smul_eq_generated_rep` theorems finally connect this quotient action to
the exact result-valued adapters from `Spec/ScalarMul.lean`.

The scalar carriers differ intentionally. Selene uses `ZMod (2^255 - 19)`,
which is exactly the value carrier of the concrete dalek scalar model, and
calls generated Rust through `FieldElement.ofZMod`. Helios uses verified
`HField` and calls the raw generated function on its underlying `Uint4` value.
-/

namespace SeleneAction

open Selene

/-- Law-bearing Selene scalar values, matching the concrete value model of
Rust's `dalek_ff_group::FieldElement`. -/
abbrev Scalar := ZMod (2^255 - 19)

/-- The exact generated Selene ladder succeeds with an on-curve representative
of natural repeated addition. This is the sole existence input to `mulP`. -/
theorem generated_mul_exists (P : SPt) (scalar : Scalar) :
    ∃ Q : SPt,
      point.selene.SelenePoint.Insts.CoreOpsArithMulFieldElementSelenePoint.mul
          P.1 (.ofZMod scalar) = .ok Q.1 ∧
      SClass.mk Q = scalar.val • SClass.mk P := by
  obtain ⟨raw, hraw, hrep⟩ :=
    WP.spec_imp_exists (SeleneLadder.mul_spec P (.ofZMod scalar))
  obtain ⟨Q, hQ, hclass⟩ := hrep
  exact ⟨Q, by rw [hraw, hQ], hclass⟩

/-- Carrier representative extracted from the successful generated ladder.
Its generated return equation is retained by `mulP_generated` immediately
below; no arbitrary default is used. -/
noncomputable def mulP (P : SPt) (scalar : Scalar) : SPt :=
  (generated_mul_exists P scalar).choose

theorem mulP_generated (P : SPt) (scalar : Scalar) :
    point.selene.SelenePoint.Insts.CoreOpsArithMulFieldElementSelenePoint.mul
        P.1 (.ofZMod scalar) = .ok (mulP P scalar).1 :=
  (generated_mul_exists P scalar).choose_spec.1

theorem mulP_class (P : SPt) (scalar : Scalar) :
    SClass.mk (mulP P scalar) = scalar.val • SClass.mk P :=
  (generated_mul_exists P scalar).choose_spec.2

/-- Descend the generated result through projective equivalence.

Well-definedness follows by rewriting both representatives with
`mulP_class`: equivalent inputs have equal classes, and natural repeated
addition respects equality. -/
noncomputable def classSmul (scalar : Scalar) :
    SClass → SClass :=
  Quotient.map (fun P => mulP P scalar) fun P Q hPQ => by
    apply Quotient.exact
    change SClass.mk (mulP P scalar) = SClass.mk (mulP Q scalar)
    rw [mulP_class, mulP_class]
    exact congrArg (fun x : SClass => scalar.val • x) (Quotient.sound hPQ)

/-- The law-bearing Selene action is the generated ladder descended to `SClass`. -/
noncomputable instance instSMulScalarSClass : SMul Scalar SClass where
  smul scalar x := classSmul scalar x

theorem smul_mk (scalar : Scalar) (P : SPt) :
    scalar • SClass.mk P = SClass.mk (mulP P scalar) := rfl

/-- The descended generated action is canonical natural repeated addition. -/
theorem smul_eq_nsmul (scalar : Scalar) (x : SClass) :
    scalar • x = scalar.val • x := by
  refine Quotient.inductionOn x fun P => ?_
  change SClass.mk (mulP P scalar) = scalar.val • SClass.mk P
  exact mulP_class P scalar

/-- The original result-valued adapter returns the representative used by the
law-bearing quotient action. -/
theorem result_smul_eq_generated_rep
    (scalar : Scalar) (P : SPt) :
    dalek_ff_group.field.FieldElement.ofZMod scalar •
        (.ok P.1 : Result point.selene.SelenePoint) =
      .ok (mulP P scalar).1 := by
  rw [HelioseleneSpec.selene_smul_apply_ok, mulP_generated]

/-- Scalar zero acts as point zero because the generated action is `0`-fold
natural repeated addition. No curve-order premise is needed. -/
theorem zero_smul (x : SClass) :
    (0 : Scalar) • x = 0 := by
  rw [smul_eq_nsmul]
  simp

/-- Scalar one acts as the identity because its canonical value is one. -/
theorem one_smul (x : SClass) :
    (1 : Scalar) • x = x := by
  rw [smul_eq_nsmul]
  exact one_nsmul x

/-- Every scalar sends point zero to zero, inherited from natural repeated
addition. -/
theorem smul_zero (scalar : Scalar) :
    scalar • (0 : SClass) = 0 := by
  rw [smul_eq_nsmul, nsmul_zero]

/-- The generated Selene action distributes over point addition. This is the
nontrivial operation law packaged by `DistribSMul`, and is unconditional. -/
theorem smul_add (scalar : Scalar) (x y : SClass) :
    scalar • (x + y) = scalar • x + scalar • y := by
  rw [smul_eq_nsmul, smul_eq_nsmul, smul_eq_nsmul, nsmul_add]

/-- Unconditional point-side distributive action for the generated Selene
ladder. This is intentionally weaker than `Module`: it needs no curve order. -/
noncomputable instance instDistribSMulScalarSClass : DistribSMul Scalar SClass where
  smul_zero := smul_zero
  smul_add := smul_add

end SeleneAction

namespace HeliosAction

open Helios

/-- The exact generated Helios ladder succeeds on `scalar.val` and returns an
on-curve representative of multiplication by its natural limb value. -/
theorem generated_mul_exists (P : HPt) (scalar : HField) :
    ∃ Q : HPt,
      point.helios.HeliosPoint.Insts.CoreOpsArithMulHelioseleneFieldHeliosPoint.mul
          P.1 scalar.val = .ok Q.1 ∧
      HClass.mk Q = scalar.val.toNat • HClass.mk P := by
  obtain ⟨raw, hraw, hrep⟩ := WP.spec_imp_exists (HeliosLadder.mul_spec P scalar.val)
  obtain ⟨Q, hQ, hclass⟩ := hrep
  exact ⟨Q, by rw [hraw, hQ], hclass⟩

/-- Name the successful generated Helios representative. The next theorem pins
this choice to the concrete generated `.ok` result. -/
noncomputable def mulP (P : HPt) (scalar : HField) : HPt :=
  (generated_mul_exists P scalar).choose

theorem mulP_generated (P : HPt) (scalar : HField) :
    point.helios.HeliosPoint.Insts.CoreOpsArithMulHelioseleneFieldHeliosPoint.mul
        P.1 scalar.val = .ok (mulP P scalar).1 :=
  (generated_mul_exists P scalar).choose_spec.1

theorem mulP_class (P : HPt) (scalar : HField) :
    HClass.mk (mulP P scalar) = scalar.val.toNat • HClass.mk P :=
  (generated_mul_exists P scalar).choose_spec.2

/-- Descend the generated Helios representative through projective
equivalence. As for Selene, well-definedness is obtained from the already-
proved natural-multiple class equation. -/
noncomputable def classSmul (scalar : HField) : HClass → HClass :=
  Quotient.map (fun P => mulP P scalar) fun P Q hPQ => by
    apply Quotient.exact
    change HClass.mk (mulP P scalar) = HClass.mk (mulP Q scalar)
    rw [mulP_class, mulP_class]
    exact congrArg (fun x : HClass => scalar.val.toNat • x) (Quotient.sound hPQ)

/-- The law-bearing Helios action uses verified scalar field elements and the
generated raw ladder on their underlying four-limb values. -/
noncomputable instance instSMulHFieldHClass : SMul HField HClass where
  smul scalar x := classSmul scalar x

theorem smul_mk (scalar : HField) (P : HPt) :
    scalar • HClass.mk P = HClass.mk (mulP P scalar) := rfl

/-- The descended generated Helios action is exactly natural repeated
addition by the reduced scalar's underlying integer. -/
theorem smul_eq_nsmul (scalar : HField) (x : HClass) :
    scalar • x = scalar.val.toNat • x := by
  refine Quotient.inductionOn x fun P => ?_
  change HClass.mk (mulP P scalar) = scalar.val.toNat • HClass.mk P
  exact mulP_class P scalar

/-- The original result-valued `SMul` adapter returns the same representative
used by the law-bearing Helios quotient action. -/
theorem result_smul_eq_generated_rep (scalar : HField) (P : HPt) :
    scalar.val • (.ok P.1 : Result point.helios.HeliosPoint) =
      .ok (mulP P scalar).1 := by
  rw [HelioseleneSpec.helios_smul_apply_ok, mulP_generated]

/-- Scalar zero acts as point zero for the generated Helios action. -/
theorem zero_smul (x : HClass) : (0 : HField) • x = 0 := by
  rw [smul_eq_nsmul, HField.zero_val]
  exact zero_nsmul x

/-- Scalar one acts as the identity for the generated Helios action. -/
theorem one_smul (x : HClass) : (1 : HField) • x = x := by
  rw [smul_eq_nsmul, HField.one_val]
  exact one_nsmul x

/-- Every verified Helios scalar sends point zero to zero. -/
theorem smul_zero (scalar : HField) : scalar • (0 : HClass) = 0 := by
  rw [smul_eq_nsmul, nsmul_zero]

/-- The generated Helios action distributes over point addition without a
curve-order premise. -/
theorem smul_add (scalar : HField) (x y : HClass) :
    scalar • (x + y) = scalar • x + scalar • y := by
  rw [smul_eq_nsmul, smul_eq_nsmul, smul_eq_nsmul, nsmul_add]

/-- Unconditional point-side distributive action for the generated Helios
ladder. -/
noncomputable instance instDistribSMulHFieldHClass : DistribSMul HField HClass where
  smul_zero := smul_zero
  smul_add := smul_add

end HeliosAction

/-! ## 7. Scalar-ring laws and the exact curve-exponent premise

Why are the remaining laws not automatic from `SMul`? In Lean, `SMul R M`
contains only the operation `R → M → M`. `DistribSMul` adds distribution on
the **point** side, and `Module` adds compatibility with scalar zero, one,
addition, and multiplication. The equation `smul_eq_nsmul` immediately proves
the point-side laws because natural repeated addition distributes over an
additive group.

Scalar-field addition and multiplication are different: their canonical
integer representatives are reduced modulo the field modulus, whereas natural
repeated addition is indexed by unreduced naturals. Replacing `n % modulus` by
`n` on points is valid exactly when `modulus • x = 0`. The helper theorem below
isolates that argument, and `SeleneExponent`/`HeliosExponent` state precisely
the missing all-points premises.

No exponent proposition is declared as an axiom and no certificate instance is
constructed in this file. `moduleOfExponent` is an ordinary function from a
proof of the proposition to a `Module` structure. The convenience instances
become available only if a caller later supplies the corresponding certificate.
-/

theorem nsmul_mod_eq_of_annihilates {A : Type} [AddCommMonoid A]
    (modulus n : ℕ) (x : A) (hmod : modulus • x = 0) :
    (n % modulus) • x = n • x := by
  symm
  calc
    n • x = (n % modulus + modulus * (n / modulus)) • x := by
      rw [Nat.mod_add_div]
    _ = (n % modulus) • x + (n / modulus) • (modulus • x) := by
      rw [add_nsmul, mul_nsmul]
    _ = (n % modulus) • x := by rw [hmod, nsmul_zero, add_zero]

/-- The exact Selene exponent statement needed for field-scalar addition and
multiplication laws: the dalek scalar modulus annihilates every Selene class.

The stronger design claim `Fintype.card SClass = 2^255 - 19` would imply this,
but cardinality is not assumed here; any direct proof of annihilation would be
sufficient. -/
def SeleneExponent : Prop :=
  ∀ x : Selene.SClass, (2^255 - 19) • x = 0

/-- The exact Helios exponent statement needed for field-scalar addition and
multiplication laws: the verified scalar-field modulus `p` annihilates every
Helios class. As for Selene, a cardinality theorem is one sufficient route but
is not built into the statement. -/
def HeliosExponent : Prop :=
  ∀ x : Helios.HClass, p • x = 0

/-- Supply this only after proving the external Selene cycle/order claim. -/
class SeleneExponentCertificate : Prop where
  exponent : SeleneExponent

/-- Supply this only after proving the external Helios cycle/order claim. -/
class HeliosExponentCertificate : Prop where
  exponent : HeliosExponent

namespace SeleneAction

open Selene

/-- Scalar addition is compatible with the generated Selene action once
reduction modulo `2^255 - 19` is invisible on points by `SeleneExponent`. -/
theorem add_smul_of_exponent (h : SeleneExponent)
    (a b : Scalar) (x : SClass) :
    (a + b) • x = a • x + b • x := by
  rw [smul_eq_nsmul, smul_eq_nsmul, smul_eq_nsmul, ZMod.val_add]
  rw [nsmul_mod_eq_of_annihilates (2^255 - 19) _ x (h x)]
  exact add_nsmul x a.val b.val

/-- Scalar multiplication is associative with the generated Selene action once
reduction modulo `2^255 - 19` is invisible on points by `SeleneExponent`. -/
theorem mul_smul_of_exponent (h : SeleneExponent)
    (a b : Scalar) (x : SClass) :
    (a * b) • x = a • b • x := by
  rw [smul_eq_nsmul, smul_eq_nsmul, smul_eq_nsmul, ZMod.val_mul]
  rw [nsmul_mod_eq_of_annihilates (2^255 - 19) _ x (h x)]
  simpa [Nat.mul_comm] using mul_nsmul x b.val a.val

/-- A full `Module` structure for the descended generated ladder, constructed
from (and therefore visibly conditional on) the Selene group-exponent proof. -/
@[reducible] noncomputable def moduleOfExponent (h : SeleneExponent) :
    Module Scalar SClass where
  one_smul := one_smul
  mul_smul := mul_smul_of_exponent h
  smul_zero := smul_zero
  smul_add := smul_add
  add_smul := add_smul_of_exponent h
  zero_smul := zero_smul

/-- Once a cycle-order certificate is in scope, Lean obtains all scalar laws
through the standard `Module` hierarchy automatically.  This file deliberately
does not manufacture an instance of `SeleneExponentCertificate`. -/
noncomputable instance instModuleScalarSClass [h : SeleneExponentCertificate] :
    Module Scalar SClass :=
  moduleOfExponent h.exponent

end SeleneAction

namespace HeliosAction

open Helios

/-- Scalar addition is compatible with the generated Helios action once
reduction modulo `p` is invisible on points by `HeliosExponent`. -/
theorem add_smul_of_exponent (h : HeliosExponent) (a b : HField) (x : HClass) :
    (a + b) • x = a • x + b • x := by
  rw [smul_eq_nsmul, smul_eq_nsmul, smul_eq_nsmul, HField.add_val]
  rw [nsmul_mod_eq_of_annihilates p _ x (h x)]
  exact add_nsmul x a.val.toNat b.val.toNat

/-- Scalar multiplication is associative with the generated Helios action once
reduction modulo `p` is invisible on points by `HeliosExponent`. -/
theorem mul_smul_of_exponent (h : HeliosExponent) (a b : HField) (x : HClass) :
    (a * b) • x = a • b • x := by
  rw [smul_eq_nsmul, smul_eq_nsmul, smul_eq_nsmul, HField.mul_val]
  rw [nsmul_mod_eq_of_annihilates p _ x (h x)]
  simpa [Nat.mul_comm] using mul_nsmul x b.val.toNat a.val.toNat

/-- Construct the full Helios `Module` structure from, and visibly conditional
on, the all-points exponent theorem. -/
@[reducible] noncomputable def moduleOfExponent (h : HeliosExponent) : Module HField HClass where
  one_smul := one_smul
  mul_smul := mul_smul_of_exponent h
  smul_zero := smul_zero
  smul_add := smul_add
  add_smul := add_smul_of_exponent h
  zero_smul := zero_smul

/-- Expose standard module laws only when a caller supplies an explicit Helios
exponent certificate. This repository deliberately provides no such instance. -/
noncomputable instance instModuleHFieldHClass [h : HeliosExponentCertificate] :
    Module HField HClass :=
  moduleOfExponent h.exponent

end HeliosAction

/-! ## 8. Axiom audit

These commands make the dependency boundary visible in ordinary Lean build
output.  In particular, the conditional module constructors consume an
ordinary theorem argument; they do not add an axiom for either exponent
statement.

The expected ladder cones contain Lean's standard logical axioms and the
already-documented generated string-length constants reached through the point
and field operations. Concrete external models are definitions, so their
presence is load-bearing for model fidelity but does not appear as an axiom.
The Helios conditional module constructor also reaches the verified `HField`
field proof and its documented field/inversion constants. Neither cone may
contain an existence-only `FunsExternal` axiom, `sorryAx`, or an exponent
certificate. The duplicate checks in `Spec/AxCheck.lean` keep these results
available from the compact audit target as well. -/

#print axioms SeleneLadder.mul_spec
#print axioms HeliosLadder.mul_spec
#print axioms SeleneAction.result_smul_eq_generated_rep
#print axioms HeliosAction.result_smul_eq_generated_rep
#print axioms SeleneAction.moduleOfExponent
#print axioms HeliosAction.moduleOfExponent

end

end ScalarMul

end HelioseleneSpec
