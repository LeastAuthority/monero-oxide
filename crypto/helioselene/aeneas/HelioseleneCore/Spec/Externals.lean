/- Spec lemmas for the external MODELS (the defs in FunsExternal.lean/TypesExternal.lean)
   plus the basic `Uint` number theory used throughout the HelioseleneSpec development.

   Everything in this file is PROVED (no `sorry`, no new axioms, no `native_decide`);
   exported lemmas that mention the generated hex-string constants (`MODULUS_ok` etc.)
   transitively inherit the pre-existing `<const>._native.decide.ax_1` axioms baked into
   Funs.lean (see README §5c). -/
import HelioseleneCore.Funs

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std Result
open helioselene

namespace HelioseleneSpec

open crypto_bigint.uint crypto_bigint.limb HelioseleneModel

/-- 4-limb unsigned integers: the representation type of Helioselene field elements. -/
abbrev Uint4 := crypto_bigint.uint.Uint 4#usize

/-- 2-limb unsigned integers (the reduction-distance constants). -/
abbrev Uint2 := crypto_bigint.uint.Uint 2#usize

/-! ## The prime modulus (as a `Nat` literal) -/

/-- The Helioselene field prime `p = 2^255 - 0x8cab7e2e6960ce8067af49720ee20ad`. -/
def p : ℕ := 57896044618658097711785492504343953926623305935230693509004809574567321395027

theorem p_pos : 0 < p := by unfold p; norm_num

theorem one_lt_p : 1 < p := by unfold p; norm_num

theorem p_lt : p < 2^256 := by unfold p; norm_num

theorem p_lt_two_pow_255 : p < 2^255 := by unfold p; norm_num

/-! ## Decidable equality for Aeneas arrays (hence for `Uint LIMBS`) -/

instance instDecEqAeneasArray {α : Type u} [DecidableEq α] {n : Usize} :
    DecidableEq (Aeneas.Std.Array α n) :=
  inferInstanceAs (DecidableEq { l : List α // l.length = n.val })

example : DecidableEq Uint4 := inferInstance

/-- `(Array.make n l h).val = l` (definitional; named for `rw`). -/
theorem Array.make_val {α : Type u} (n : Usize) (l : List α) (h : l.length = n.val) :
    (Aeneas.Std.Array.make n l h).val = l := rfl

/-! ## Nat-level little-endian digit folds

`digitsVal w ds` is the value of the little-endian digit list `ds` in base `2^w`.
Both `Uint.toNat` (w = 64) and `HelioseleneModel.leBytesToNat` (w = 8) are instances. -/

/-- Value of a little-endian digit list in base `2^w`. -/
def digitsVal (w : Nat) (ds : List Nat) : Nat := ds.foldr (fun d acc => acc * 2^w + d) 0

@[simp] theorem digitsVal_nil (w : Nat) : digitsVal w [] = 0 := rfl

@[simp] theorem digitsVal_cons (w d : Nat) (ds : List Nat) :
    digitsVal w (d :: ds) = digitsVal w ds * 2^w + d := rfl

theorem digitsVal_lt (w : Nat) (ds : List Nat) (h : ∀ d ∈ ds, d < 2^w) :
    digitsVal w ds < 2^(w * ds.length) := by
  induction ds with
  | nil => simp only [digitsVal_nil, List.length_nil, Nat.mul_zero, Nat.pow_zero]; omega
  | cons d ds ih =>
    have hd : d < 2^w := h d List.mem_cons_self
    have ht : digitsVal w ds < 2^(w * ds.length) := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hpow : 2^(w * (ds.length + 1)) = 2^(w * ds.length) * 2^w := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    rw [digitsVal_cons, List.length_cons, hpow]
    have h1 : digitsVal w ds * 2^w + d < (digitsVal w ds + 1) * 2^w := by
      rw [Nat.succ_mul]; omega
    have h2 : (digitsVal w ds + 1) * 2^w ≤ 2^(w * ds.length) * 2^w :=
      Nat.mul_le_mul_right _ ht
    omega

/-- The little-endian base-`2^w` digits of `n` fold back to `n % 2^(w·k)`. -/
theorem digitsVal_ofFn (w k n : Nat) :
    digitsVal w (List.ofFn (fun i : Fin k => (n >>> (w * i.val)) % 2^w)) = n % 2^(w * k) := by
  induction k generalizing n with
  | zero => simp only [List.ofFn_zero, digitsVal_nil, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | succ k ih =>
    rw [List.ofFn_succ, digitsVal_cons]
    have htail : (fun i : Fin k => (n >>> (w * ((Fin.succ i).val))) % 2^w)
        = (fun i : Fin k => ((n >>> w) >>> (w * i.val)) % 2^w) := by
      funext i
      rw [Fin.val_succ, ← Nat.shiftRight_add]
      congr 1
      ring_nf
    rw [htail, ih]
    rw [Fin.val_zero, Nat.mul_zero, Nat.shiftRight_zero]
    rw [Nat.shiftRight_eq_div_pow]
    rw [show w * (k + 1) = w + w * k by ring, Nat.pow_add, Nat.mod_mul]
    ring

/-- Digit lists of equal length with digits `< 2^w` and equal values are equal. -/
theorem digitsVal_inj (w : Nat) : ∀ (ds es : List Nat), ds.length = es.length →
    (∀ d ∈ ds, d < 2^w) → (∀ e ∈ es, e < 2^w) →
    digitsVal w ds = digitsVal w es → ds = es := by
  intro ds
  induction ds with
  | nil =>
    intro es hlen _ _ _
    cases es with
    | nil => rfl
    | cons e es => simp at hlen
  | cons d ds ih =>
    intro es hlen hd he heq
    cases es with
    | nil => simp at hlen
    | cons e es =>
      rw [digitsVal_cons, digitsVal_cons] at heq
      have hdlt : d < 2^w := hd d List.mem_cons_self
      have helt : e < 2^w := he e List.mem_cons_self
      have hde : d = e := by
        have h1 : (d + digitsVal w ds * 2^w) % 2^w = (e + digitsVal w es * 2^w) % 2^w := by
          rw [Nat.add_comm d, Nat.add_comm e, heq]
        rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
            Nat.mod_eq_of_lt hdlt, Nat.mod_eq_of_lt helt] at h1
        exact h1
      subst hde
      have hpos : 0 < 2^w := Nat.two_pow_pos w
      have hval : digitsVal w ds = digitsVal w es :=
        Nat.eq_of_mul_eq_mul_right hpos (by omega)
      rw [ih es (by simpa using hlen) (fun x hx => hd x (List.mem_cons_of_mem _ hx))
        (fun x hx => he x (List.mem_cons_of_mem _ hx)) hval]

/-! ## Limb / byte constructors of the model -/

theorem limbOfNat_val (n : Nat) : (limbOfNat n).val = n % 2^64 :=
  BitVec.toNat_ofNat n 64

theorem byteOfNat_val (n : Nat) : (byteOfNat n).val = n % 2^8 :=
  BitVec.toNat_ofNat n 8

theorem limbAllOnes_val : limbAllOnes.val = 2^64 - 1 :=
  BitVec.toNat_allOnes

/-- Any `U64` limb value shifted right by 63 bits is a 0/1 flag. -/
theorem shiftRight63_le_one (x : Std.U64) : x.val >>> 63 ≤ 1 := by
  have hx : x.val < 2^64 := x.hBounds
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-! ## `Uint.toNat` / `Uint.ofNat` number theory -/

theorem Uint.toNat_eq_digitsVal {LIMBS : Usize} (u : Uint LIMBS) :
    u.toNat = digitsVal 64 (u.val.map UScalar.val) := by
  unfold crypto_bigint.uint.Uint.toNat digitsVal
  rw [List.foldr_map]

theorem Uint.map_val_lt {LIMBS : Usize} (u : Uint LIMBS) :
    ∀ d ∈ u.val.map UScalar.val, d < 2^64 := by
  intro d hd
  rw [List.mem_map] at hd
  obtain ⟨x, _, rfl⟩ := hd
  exact x.hBounds

/-- `Uint.toNat` is always below `2^(64·LIMBS)`. -/
theorem Uint.toNat_lt {LIMBS : Usize} (u : Uint LIMBS) : u.toNat < 2^(64 * LIMBS.val) := by
  rw [Uint.toNat_eq_digitsVal]
  have h := digitsVal_lt 64 _ (Uint.map_val_lt u)
  rwa [List.length_map, Aeneas.Std.Array.length_eq] at h

theorem Uint.ofNat_val_map (LIMBS : Usize) (n : Nat) :
    (Uint.ofNat LIMBS n).val.map UScalar.val
      = List.ofFn (fun i : Fin LIMBS.val => (n >>> (64 * i.val)) % 2^64) := by
  unfold crypto_bigint.uint.Uint.ofNat
  rw [Array.make_val, List.map_ofFn]
  congr 1

/-- `Uint.ofNat` truncates: the round trip gives `n mod 2^(64·LIMBS)`. -/
theorem Uint.toNat_ofNat_mod (LIMBS : Usize) (n : Nat) :
    (Uint.ofNat LIMBS n).toNat = n % 2^(64 * LIMBS.val) := by
  rw [Uint.toNat_eq_digitsVal, Uint.ofNat_val_map, digitsVal_ofFn]

/-- `Uint.ofNat` is exact on in-range inputs. -/
theorem Uint.toNat_ofNat {LIMBS : Usize} {n : Nat} (h : n < 2^(64 * LIMBS.val)) :
    (Uint.ofNat LIMBS n).toNat = n := by
  rw [Uint.toNat_ofNat_mod, Nat.mod_eq_of_lt h]

/-- `Uint.toNat` is injective. -/
theorem Uint.toNat_inj {LIMBS : Usize} {a b : Uint LIMBS} (h : a.toNat = b.toNat) : a = b := by
  rw [Uint.toNat_eq_digitsVal, Uint.toNat_eq_digitsVal] at h
  have hlists : a.val.map UScalar.val = b.val.map UScalar.val :=
    digitsVal_inj 64 _ _
      (by rw [List.length_map, List.length_map, Aeneas.Std.Array.length_eq,
              Aeneas.Std.Array.length_eq])
      (Uint.map_val_lt a) (Uint.map_val_lt b) h
  have hinj : Function.Injective (List.map (UScalar.val (ty := .U64))) :=
    List.map_injective_iff.2 (fun x y hxy => (UScalar.eq_equiv x y).2 hxy)
  exact Subtype.ext (hinj hlists)

/-- `Uint.ofNat ∘ Uint.toNat = id`. -/
theorem Uint.ofNat_toNat {LIMBS : Usize} (u : Uint LIMBS) : Uint.ofNat LIMBS u.toNat = u :=
  Uint.toNat_inj (by rw [Uint.toNat_ofNat (Uint.toNat_lt u)])

/-! ### Specializations at the concrete limb counts 4 and 2 -/

theorem usize4_val : (4#usize).val = 4 := by simp
theorem usize2_val : (2#usize).val = 2 := by simp
theorem usize1_val : (1#usize).val = 1 := by simp

theorem Uint4.toNat_lt (u : Uint4) : u.toNat < 2^256 := by
  have h := Uint.toNat_lt u
  rwa [usize4_val, show 64 * 4 = 256 from by norm_num] at h

theorem Uint4.toNat_ofNat {n : Nat} (h : n < 2^256) : (Uint.ofNat 4#usize n).toNat = n :=
  Uint.toNat_ofNat (by rwa [usize4_val, show 64 * 4 = 256 from by norm_num])

theorem Uint4.toNat_ofNat_mod (n : Nat) : (Uint.ofNat 4#usize n).toNat = n % 2^256 := by
  rw [Uint.toNat_ofNat_mod, usize4_val, show 64 * 4 = 256 from by norm_num]

theorem Uint2.toNat_lt (u : Uint2) : u.toNat < 2^128 := by
  have h := Uint.toNat_lt u
  rwa [usize2_val, show 64 * 2 = 128 from by norm_num] at h

theorem Uint2.toNat_ofNat {n : Nat} (h : n < 2^128) : (Uint.ofNat 2#usize n).toNat = n :=
  Uint.toNat_ofNat (by rwa [usize2_val, show 64 * 2 = 128 from by norm_num])

/-! ## Little-endian byte values -/

theorem leBytesToNat_eq_digitsVal (bs : List Std.U8) :
    leBytesToNat bs = digitsVal 8 (bs.map UScalar.val) := by
  unfold HelioseleneModel.leBytesToNat digitsVal
  rw [List.foldr_map]
  congr 1

theorem leBytesToNat_lt (bs : List Std.U8) : leBytesToNat bs < 2^(8 * bs.length) := by
  rw [leBytesToNat_eq_digitsVal]
  have h := digitsVal_lt 8 (bs.map UScalar.val) ?bound
  · rwa [List.length_map] at h
  case bound =>
    intro d hd
    rw [List.mem_map] at hd
    obtain ⟨x, _, rfl⟩ := hd
    exact x.hBounds

/-! ## The `String`/`Str` bridge (for the `from_be_hex` constants)

`toStr` (Aeneas) maps a string literal through `String.toByteArray.toList`, whose
well-founded loop the kernel cannot reduce. We rewrite it to the structural
`.data.toList` spelling, after which everything about concrete literals is
kernel-decidable. -/

private theorem byteArray_get!_eq (bs : ByteArray) (i : Nat) : bs.get! i = bs.data[i]! := by
  cases bs; rfl

theorem byteArray_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  have loop_eq : ∀ (i : Nat) (r : List UInt8),
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro i r
    fun_induction ByteArray.toList.loop bs i r with
    | case1 i r h ih =>
      have hlt : i < bs.data.toList.length := by
        rw [Array.length_toList]; exact h
      rw [ih, List.drop_eq_getElem_cons hlt, List.reverse_cons, List.append_assoc]
      congr 1
      rw [List.singleton_append, byteArray_get!_eq]
      congr 1
      rw [← getElem!_pos bs.data.toList i hlt]
      simp only [Array.getElem!_toList]
    | case2 i r h =>
      rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; exact Nat.le_of_not_lt h),
          List.append_nil]
  unfold ByteArray.toList
  rw [loop_eq]
  simp only [List.reverse_nil, List.drop_zero, List.nil_append]

/-- The byte-to-`U8` embedding used by `toStr` (definitionally equal to its inline map). -/
def toU8byte (x : UInt8) : Std.U8 := ⟨⟨⟨x.toNat, by simpa using x.toNat_lt⟩⟩⟩

/-- The `Str` produced by `toStr` is the (kernel-computable) list of UTF-8 bytes. -/
theorem toStr_val (s : String) (h : s.toByteArray.size ≤ U32.max) :
    (toStr s h).val = s.toByteArray.data.toList.map toU8byte := by
  have base : (toStr s h).val = s.toByteArray.toList.map toU8byte := rfl
  rw [base, byteArray_toList_eq]

/-! ## Spec lemmas: `Limb` operations -/

theorem Limb.wrapping_add_ok (a b : Limb) :
    ∃ r, crypto_bigint.limb.add.Limb.wrapping_add a b = ok r
      ∧ r.val = (a.val + b.val) % 2^64 :=
  ⟨_, rfl, BitVec.toNat_add a.bv b.bv⟩

theorem Limb.bitand_ok (a b : Limb) :
    ∃ r, Limb.Insts.CoreOpsBitBitAndLimbLimb.bitand a b = ok r
      ∧ r.val = a.val &&& b.val :=
  ⟨_, rfl, BitVec.toNat_and a.bv b.bv⟩

theorem Limb.bitor_ok (a b : Limb) :
    ∃ r, Limb.Insts.CoreOpsBitBitOrLimbLimb.bitor a b = ok r
      ∧ r.val = a.val ||| b.val :=
  ⟨_, rfl, BitVec.toNat_or a.bv b.bv⟩

theorem Limb.bitxor_ok (a b : Limb) :
    ∃ r, Limb.Insts.CoreOpsBitBitXorLimbLimb.bitxor a b = ok r
      ∧ r.val = a.val ^^^ b.val :=
  ⟨_, rfl, BitVec.toNat_xor a.bv b.bv⟩

theorem Limb.not_ok (a : Limb) :
    ∃ r, Limb.Insts.CoreOpsBitNotLimb.not a = ok r
      ∧ r.val = 2^64 - 1 - a.val :=
  ⟨_, rfl, BitVec.toNat_not⟩

theorem Limb.wrapping_neg_ok (a : Limb) :
    ∃ r, crypto_bigint.limb.neg.Limb.wrapping_neg a = ok r
      ∧ r.val = (2^64 - a.val) % 2^64 :=
  ⟨_, rfl, BitVec.toNat_neg a.bv⟩

theorem Limb.ct_eq_ok (a b : Limb) :
    ∃ c, Limb.Insts.SubtleConstantTimeEq.ct_eq a b = ok c
      ∧ (c = true ↔ a.val = b.val) :=
  ⟨_, rfl, beq_iff_eq⟩

/-- `mac`: exact multiply-accumulate, `lo + 2^64·hi = a + b·c + carry`. -/
theorem Limb.mac_ok (a b c carry : Limb) :
    ∃ lo hi, crypto_bigint.limb.mul.Limb.mac a b c carry = ok (lo, hi)
      ∧ lo.val + 2^64 * hi.val = a.val + b.val * c.val + carry.val
      ∧ lo.val = (a.val + b.val * c.val + carry.val) % 2^64
      ∧ hi.val = (a.val + b.val * c.val + carry.val) / 2^64 := by
  refine ⟨_, _, rfl, ?_⟩
  have ha : a.val < 2^64 := a.hBounds
  have hb : b.val < 2^64 := b.hBounds
  have hc : c.val < 2^64 := c.hBounds
  have hcy : carry.val < 2^64 := carry.hBounds
  have hbc : b.val * c.val ≤ (2^64 - 1) * (2^64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hrlt : a.val + b.val * c.val + carry.val < 2^128 := by omega
  rw [limbOfNat_val, limbOfNat_val, Nat.shiftRight_eq_div_pow]
  have hdiv : (a.val + b.val * c.val + carry.val) / 2^64 < 2^64 := by omega
  rw [Nat.mod_eq_of_lt hdiv]
  omega

theorem Limb.shl_ok (a : Limb) (s : Usize) (hs : s.val < 64) :
    ∃ r, Limb.Insts.CoreOpsBitShlUsizeLimb.shl a s = ok r
      ∧ r.val = (a.val <<< s.val) % 2^64 := by
  unfold Limb.Insts.CoreOpsBitShlUsizeLimb.shl
  rw [if_pos hs]
  exact ⟨_, rfl, BitVec.toNat_shiftLeft⟩

theorem Limb.shr_ok (a : Limb) (s : Usize) (hs : s.val < 64) :
    ∃ r, Limb.Insts.CoreOpsBitShrUsizeLimb.shr a s = ok r
      ∧ r.val = a.val >>> s.val := by
  unfold Limb.Insts.CoreOpsBitShrUsizeLimb.shr
  rw [if_pos hs]
  exact ⟨_, rfl, BitVec.toNat_ushiftRight a.bv s.val⟩

theorem Limb.clone_ok (a : Limb) :
    Limb.Insts.CoreCloneClone.clone a = ok a := rfl

/-! ### `Limb` constants -/

theorem Limb.ZERO_ok : ∃ z, crypto_bigint.limb.Limb.ZERO = ok z ∧ z.val = 0 :=
  ⟨_, rfl, by simp⟩

theorem Limb.ONE_ok : ∃ o, crypto_bigint.limb.Limb.ONE = ok o ∧ o.val = 1 :=
  ⟨_, rfl, by simp⟩

theorem Limb.MAX_ok : ∃ m, crypto_bigint.limb.Limb.MAX = ok m ∧ m.val = 2^64 - 1 :=
  ⟨_, rfl, limbAllOnes_val⟩

theorem Limb.BITS_ok : ∃ b, crypto_bigint.limb.Limb.BITS = ok b ∧ b.val = 64 :=
  ⟨_, rfl, by simp⟩

/-! ### Re-exports: `overflowing_add` / `overflowing_sub` in equation form -/

private theorem U64_size_eq : UScalar.size .U64 = 2^64 := by
  rw [UScalar.size_def]; rfl

private theorem U64_max_eq : UScalar.max .U64 = 2^64 - 1 := by
  rw [UScalar.max_def]; rfl

/-- `overflowing_add`: `lo + 2^64·carry = x + y` with a 0/1 carry flag. -/
theorem U64.overflowing_add_val (x y : Std.U64) :
    (core.num.U64.overflowing_add x y).1.val
      + 2^64 * (if (core.num.U64.overflowing_add x y).2 then 1 else 0)
      = x.val + y.val := by
  have h := core.num.U64.overflowing_add_eq x y
  have hs := U64_size_eq
  have hm := U64_max_eq
  split at h
  · rw [h.2, if_pos rfl]; omega
  · rw [h.2, if_neg Bool.false_ne_true]; omega

/-- `overflowing_sub`: `diff + y = x + 2^64·borrow` with a 0/1 borrow flag. -/
theorem U64.overflowing_sub_val (x y : Std.U64) :
    (core.num.U64.overflowing_sub x y).1.val + y.val
      = x.val + 2^64 * (if (core.num.U64.overflowing_sub x y).2 then 1 else 0) := by
  have h := core.num.U64.overflowing_sub_eq x y
  have hs := U64_size_eq
  have hx : x.val < 2^64 := x.hBounds
  have hy : y.val < 2^64 := y.hBounds
  split at h
  · rw [h.2, if_pos rfl]; omega
  · rw [h.2, if_neg Bool.false_ne_true]; omega

/-! ## Spec lemmas: `Uint` operations -/

theorem Uint.wrapping_add_ok {LIMBS : Usize} (a b : Uint LIMBS) :
    ∃ r, crypto_bigint.uint.add.Uint.wrapping_add a b = ok r
      ∧ r.toNat = (a.toNat + b.toNat) % 2^(64 * LIMBS.val) :=
  ⟨_, rfl, Uint.toNat_ofNat_mod _ _⟩

theorem Uint.wrapping_sub_ok {LIMBS : Usize} (a b : Uint LIMBS) :
    ∃ r, crypto_bigint.uint.sub.Uint.wrapping_sub a b = ok r
      ∧ r.toNat = (a.toNat + 2^(64 * LIMBS.val) - b.toNat) % 2^(64 * LIMBS.val) :=
  ⟨_, rfl, Uint.toNat_ofNat_mod _ _⟩

/-- `sbb` raw form. Conventions (matching the model exactly):
    * the borrow-IN is the TOP bit of the incoming borrow limb, `borrow.val >>> 63`;
    * the borrow-OUT is the all-ones mask `2^64 - 1` on underflow and `0` otherwise. -/
theorem Uint.sbb_ok {LIMBS : Usize} (a b : Uint LIMBS) (borrow : Limb) :
    ∃ d bo, crypto_bigint.uint.sub.Uint.sbb a b borrow = ok (d, bo)
      ∧ d.toNat = (a.toNat + 2^(64 * LIMBS.val) - (b.toNat + borrow.val >>> 63))
                    % 2^(64 * LIMBS.val)
      ∧ bo = (if a.toNat < b.toNat + borrow.val >>> 63 then limbAllOnes else 0#u64) :=
  ⟨_, _, rfl, Uint.toNat_ofNat_mod _ _, rfl⟩

/-- `sbb` split form: exact subtraction identities plus borrow-out values. -/
theorem Uint.sbb_ok' {LIMBS : Usize} (a b : Uint LIMBS) (borrow : Limb) :
    ∃ d bo, crypto_bigint.uint.sub.Uint.sbb a b borrow = ok (d, bo)
      ∧ (if a.toNat < b.toNat + borrow.val >>> 63
         then d.toNat + (b.toNat + borrow.val >>> 63) = a.toNat + 2^(64 * LIMBS.val)
              ∧ bo.val = 2^64 - 1
         else d.toNat + (b.toNat + borrow.val >>> 63) = a.toNat ∧ bo.val = 0) := by
  obtain ⟨d, bo, heq, hd, hbo⟩ := Uint.sbb_ok a b borrow
  refine ⟨d, bo, heq, ?_⟩
  have hM : (0:ℕ) < 2^(64 * LIMBS.val) := Nat.two_pow_pos _
  have ha := Uint.toNat_lt a
  have hb := Uint.toNat_lt b
  have hbi : borrow.val >>> 63 ≤ 1 := shiftRight63_le_one borrow
  split
  case isTrue h =>
    refine ⟨?_, ?_⟩
    · rw [hd, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [hbo, if_pos h]; exact limbAllOnes_val
  case isFalse h =>
    refine ⟨?_, ?_⟩
    · rw [hd, show a.toNat + 2^(64 * LIMBS.val) - (b.toNat + borrow.val >>> 63)
            = (a.toNat - (b.toNat + borrow.val >>> 63)) + 2^(64 * LIMBS.val) from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [hbo, if_neg h]; simp

/-- `mul_wide` is exact: `lo + 2^(64·LIMBS)·hi = a·b`. -/
theorem Uint.mul_wide_ok {LIMBS HLIMBS : Usize} (a : Uint LIMBS) (b : Uint HLIMBS) :
    ∃ lo hi, crypto_bigint.uint.mul.Uint.mul_wide a b = ok (lo, hi)
      ∧ lo.toNat + 2^(64 * LIMBS.val) * hi.toNat = a.toNat * b.toNat
      ∧ lo.toNat = (a.toNat * b.toNat) % 2^(64 * LIMBS.val)
      ∧ hi.toNat = (a.toNat * b.toNat) / 2^(64 * LIMBS.val) := by
  refine ⟨_, _, rfl, ?_⟩
  have hab : a.toNat * b.toNat < 2^(64 * LIMBS.val) * 2^(64 * HLIMBS.val) :=
    Nat.mul_lt_mul_of_lt_of_lt (Uint.toNat_lt a) (Uint.toNat_lt b)
  have hlo : (Uint.ofNat LIMBS (a.toNat * b.toNat)).toNat
      = (a.toNat * b.toNat) % 2^(64 * LIMBS.val) := Uint.toNat_ofNat_mod _ _
  have hhi : (Uint.ofNat HLIMBS ((a.toNat * b.toNat) >>> (64 * LIMBS.val))).toNat
      = (a.toNat * b.toNat) / 2^(64 * LIMBS.val) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Uint.toNat_ofNat (Nat.div_lt_of_lt_mul hab)
  refine ⟨?_, hlo, hhi⟩
  rw [hlo, hhi]
  exact Nat.mod_add_div _ _

/-- `square_wide` is exact: `lo + 2^(64·LIMBS)·hi = a²`. -/
theorem Uint.square_wide_ok {LIMBS : Usize} (a : Uint LIMBS) :
    ∃ lo hi, crypto_bigint.uint.mul.Uint.square_wide a = ok (lo, hi)
      ∧ lo.toNat + 2^(64 * LIMBS.val) * hi.toNat = a.toNat * a.toNat
      ∧ lo.toNat = (a.toNat * a.toNat) % 2^(64 * LIMBS.val)
      ∧ hi.toNat = (a.toNat * a.toNat) / 2^(64 * LIMBS.val) := by
  refine ⟨_, _, rfl, ?_⟩
  have hab : a.toNat * a.toNat < 2^(64 * LIMBS.val) * 2^(64 * LIMBS.val) :=
    Nat.mul_lt_mul_of_lt_of_lt (Uint.toNat_lt a) (Uint.toNat_lt a)
  have hlo : (Uint.ofNat LIMBS (a.toNat * a.toNat)).toNat
      = (a.toNat * a.toNat) % 2^(64 * LIMBS.val) := Uint.toNat_ofNat_mod _ _
  have hhi : (Uint.ofNat LIMBS ((a.toNat * a.toNat) >>> (64 * LIMBS.val))).toNat
      = (a.toNat * a.toNat) / 2^(64 * LIMBS.val) := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Uint.toNat_ofNat (Nat.div_lt_of_lt_mul hab)
  refine ⟨?_, hlo, hhi⟩
  rw [hlo, hhi]
  exact Nat.mod_add_div _ _

theorem Uint.shl_vartime_ok {LIMBS : Usize} (a : Uint LIMBS) (s : Usize)
    (hs : s.val < 64 * LIMBS.val) :
    ∃ r, crypto_bigint.uint.shl.Uint.shl_vartime a s = ok r
      ∧ r.toNat = (a.toNat * 2^s.val) % 2^(64 * LIMBS.val) := by
  unfold crypto_bigint.uint.shl.Uint.shl_vartime
  rw [if_pos hs]
  exact ⟨_, rfl, by rw [Uint.toNat_ofNat_mod, Nat.shiftLeft_eq]⟩

theorem Uint.shr_vartime_ok {LIMBS : Usize} (a : Uint LIMBS) (s : Usize)
    (hs : s.val < 64 * LIMBS.val) :
    ∃ r, crypto_bigint.uint.shr.Uint.shr_vartime a s = ok r
      ∧ r.toNat = a.toNat / 2^s.val := by
  unfold crypto_bigint.uint.shr.Uint.shr_vartime
  rw [if_pos hs]
  refine ⟨_, rfl, ?_⟩
  rw [Nat.shiftRight_eq_div_pow]
  exact Uint.toNat_ofNat (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Uint.toNat_lt a))

/-- Shift-by-1 specialization used by field doubling. -/
theorem Uint4.shl_vartime_one_ok (a : Uint4) :
    ∃ r, crypto_bigint.uint.shl.Uint.shl_vartime a 1#usize = ok r
      ∧ r.toNat = (2 * a.toNat) % 2^256 := by
  obtain ⟨r, heq, hval⟩ := Uint.shl_vartime_ok a 1#usize
    (by rw [usize1_val, usize4_val]; norm_num)
  refine ⟨r, heq, ?_⟩
  rw [hval, usize1_val, usize4_val]
  norm_num [Nat.mul_comm]

/-- Shift-by-1 specialization used by `invert`'s halving steps. -/
theorem Uint4.shr_vartime_one_ok (a : Uint4) :
    ∃ r, crypto_bigint.uint.shr.Uint.shr_vartime a 1#usize = ok r
      ∧ r.toNat = a.toNat / 2 := by
  obtain ⟨r, heq, hval⟩ := Uint.shr_vartime_ok a 1#usize
    (by rw [usize1_val, usize4_val]; norm_num)
  refine ⟨r, heq, ?_⟩
  rw [hval, usize1_val]
  norm_num

theorem Uint.as_limbs_ok {LIMBS : Usize} (u : Uint LIMBS) :
    crypto_bigint.uint.Uint.as_limbs u = ok u := rfl

theorem Uint.as_limbs_mut_ok {LIMBS : Usize} (u : Uint LIMBS) :
    crypto_bigint.uint.Uint.as_limbs_mut u = ok (u, fun a => a) := rfl

theorem Uint.conditional_select_ok {LIMBS : Usize} (a b : Uint LIMBS) (c : subtle.Choice) :
    Uint.Insts.SubtleConditionallySelectable.conditional_select a b c
      = ok (if c then b else a) := rfl

/-! ### `Uint` constants -/

theorem Uint.ZERO_ok (LIMBS : Usize) :
    ∃ z, crypto_bigint.uint.Uint.ZERO LIMBS = ok z ∧ z.toNat = 0 :=
  ⟨_, rfl, by rw [Uint.toNat_ofNat_mod, Nat.zero_mod]⟩

theorem Uint.ONE_ok (LIMBS : Usize) (h : 0 < LIMBS.val) :
    ∃ o, crypto_bigint.uint.Uint.ONE LIMBS = ok o ∧ o.toNat = 1 := by
  refine ⟨_, rfl, ?_⟩
  rw [Uint.toNat_ofNat_mod, Nat.mod_eq_of_lt]
  exact Nat.one_lt_two_pow_iff.2 (by omega)

theorem Uint.LIMBS_1_ok (LIMBS : Usize) :
    crypto_bigint.uint.Uint.LIMBS_1 LIMBS = ok LIMBS := rfl

/-! ### Encodings -/

theorem Uint.from_le_slice_ok (LIMBS : Usize) (s : Slice Std.U8)
    (hlen : s.val.length = 8 * LIMBS.val) :
    ∃ r, crypto_bigint.uint.encoding.Uint.from_le_slice LIMBS s = ok r
      ∧ r.toNat = leBytesToNat s.val := by
  unfold crypto_bigint.uint.encoding.Uint.from_le_slice
  rw [if_pos hlen]
  refine ⟨_, rfl, Uint.toNat_ofNat ?_⟩
  have h := leBytesToNat_lt s.val
  rwa [hlen, show 8 * (8 * LIMBS.val) = 64 * LIMBS.val from by ring] at h

theorem Uint4.to_le_bytes_ok (u : Uint4) :
    ∃ bytes, Uint4.Insts.Crypto_bigintTraitsEncodingArrayU832.to_le_bytes u = ok bytes
      ∧ leBytesToNat bytes.val = u.toNat := by
  refine ⟨_, rfl, ?_⟩
  rw [Array.make_val, leBytesToNat_eq_digitsVal, List.map_ofFn]
  have hfn : (UScalar.val ∘ fun i : Fin 32 => byteOfNat (u.toNat >>> (8 * i.val)))
      = fun i : Fin 32 => (u.toNat >>> (8 * i.val)) % 2^8 := by
    funext i
    exact byteOfNat_val _
  rw [hfn, digitsVal_ofFn, show 8 * 32 = 256 from by norm_num,
      Nat.mod_eq_of_lt (Uint4.toNat_lt u)]

/-- `from_be_hex` on a valid hex string of the right length parses to `ofNat` of the value. -/
theorem Uint.from_be_hex_ok (LIMBS : Usize) (s : Str) (n : Nat)
    (hlen : s.val.length = 16 * LIMBS.val)
    (hparse : parseBeHex? s.val = some n) :
    crypto_bigint.uint.encoding.Uint.from_be_hex LIMBS s = ok (Uint.ofNat LIMBS n) := by
  unfold crypto_bigint.uint.encoding.Uint.from_be_hex
  rw [if_pos hlen, hparse]

/-! ## Spec lemmas: `subtle` operations -/

theorem Choice.not_ok (c : subtle.Choice) :
    subtle.Choice.Insts.CoreOpsBitNotChoice.not c = ok (!c) := rfl

theorem Choice.from_ok (u : Std.U8) :
    ∃ c, subtle.Choice.Insts.CoreConvertFromU8.from u = ok c
      ∧ (c = true ↔ u.val ≠ 0) :=
  ⟨_, rfl, by simp⟩

theorem CtOption.new_ok {T : Type} (v : T) (c : subtle.Choice) :
    subtle.CtOption.new v c = ok (v, c) := rfl

/-! ## The compile-time constants (hex literals)

The hex strings are parsed by the model's real big-endian parser; the parses are
evaluated by the kernel (`decide`) after rewriting away the well-founded
`ByteArray.toList` spelling. No `native_decide` anywhere. -/

section Constants

private theorem parse_MODULUS
    (h : ("7ffffffffffffffffffffffffffffffff735481d1969f317f9850b68df11df53" : String).toByteArray.size ≤ U32.max) :
    parseBeHex? ((toStr "7ffffffffffffffffffffffffffffffff735481d1969f317f9850b68df11df53" h).val)
      = some 57896044618658097711785492504343953926623305935230693509004809574567321395027 := by
  rw [toStr_val]; decide

private theorem len_MODULUS
    (h : ("7ffffffffffffffffffffffffffffffff735481d1969f317f9850b68df11df53" : String).toByteArray.size ≤ U32.max) :
    ((toStr "7ffffffffffffffffffffffffffffffff735481d1969f317f9850b68df11df53" h).val).length
      = 16 * (4#usize).val := by
  rw [toStr_val, usize4_val]; decide

/-- `field.MODULUS` is `ok` and its value is exactly the prime `p`. -/
theorem MODULUS_ok : ∃ m, field.MODULUS = ok m ∧ m.toNat = p := by
  refine ⟨Uint.ofNat 4#usize p, ?_, Uint4.toNat_ofNat p_lt⟩
  unfold field.MODULUS
  exact Uint.from_be_hex_ok _ _ _ (len_MODULUS _) (parse_MODULUS _)

private theorem parse_M255D
    (h : ("08cab7e2e6960ce8067af49720ee20ad" : String).toByteArray.size ≤ U32.max) :
    parseBeHex? ((toStr "08cab7e2e6960ce8067af49720ee20ad" h).val)
      = some 11686397589588510723982429389243424941 := by
  rw [toStr_val]; decide

private theorem len_M255D
    (h : ("08cab7e2e6960ce8067af49720ee20ad" : String).toByteArray.size ≤ U32.max) :
    ((toStr "08cab7e2e6960ce8067af49720ee20ad" h).val).length = 16 * (2#usize).val := by
  rw [toStr_val, usize2_val]; decide

/-- `MODULUS_255_DISTANCE` is `ok` with value `2^255 - p` (= 0x8cab7e2e6960ce8067af49720ee20ad). -/
theorem MODULUS_255_DISTANCE_ok :
    ∃ m, field.verified.MODULUS_255_DISTANCE = ok m ∧ m.toNat = 2^255 - p := by
  refine ⟨Uint.ofNat 2#usize 11686397589588510723982429389243424941, ?_, ?_⟩
  · unfold field.verified.MODULUS_255_DISTANCE
    exact Uint.from_be_hex_ok _ _ _ (len_M255D _) (parse_M255D _)
  · rw [Uint2.toNat_ofNat (by norm_num)]
    unfold p; norm_num

private theorem parse_2M255D
    (h : ("11956fc5cd2c19d00cf5e92e41dc415a" : String).toByteArray.size ≤ U32.max) :
    parseBeHex? ((toStr "11956fc5cd2c19d00cf5e92e41dc415a" h).val)
      = some 23372795179177021447964858778486849882 := by
  rw [toStr_val]; decide

private theorem len_2M255D
    (h : ("11956fc5cd2c19d00cf5e92e41dc415a" : String).toByteArray.size ≤ U32.max) :
    ((toStr "11956fc5cd2c19d00cf5e92e41dc415a" h).val).length = 16 * (2#usize).val := by
  rw [toStr_val, usize2_val]; decide

/-- `TWO_MODULUS_255_DISTANCE` is `ok` with value `2·(2^255 - p)` (= 2^256 - 2p). -/
theorem TWO_MODULUS_255_DISTANCE_ok :
    ∃ m, field.verified.red.TWO_MODULUS_255_DISTANCE = ok m ∧ m.toNat = 2 * (2^255 - p) := by
  refine ⟨Uint.ofNat 2#usize 23372795179177021447964858778486849882, ?_, ?_⟩
  · unfold field.verified.red.TWO_MODULUS_255_DISTANCE
    exact Uint.from_be_hex_ok _ _ _ (len_2M255D _) (parse_2M255D _)
  · rw [Uint2.toNat_ofNat (by norm_num)]
    unfold p; norm_num

private theorem parse_MX2M
    (h : ("80000000000000000000000000000000195fd8272bba15380a8f1db9613261f5" : String).toByteArray.size ≤ U32.max) :
    parseBeHex? ((toStr "80000000000000000000000000000000195fd8272bba15380a8f1db9613261f5" h).val)
      = some 57896044618658097711785492504343953926668720685020371267821459143285372248565 := by
  rw [toStr_val]; decide

private theorem len_MX2M
    (h : ("80000000000000000000000000000000195fd8272bba15380a8f1db9613261f5" : String).toByteArray.size ≤ U32.max) :
    ((toStr "80000000000000000000000000000000195fd8272bba15380a8f1db9613261f5" h).val).length
      = 16 * (4#usize).val := by
  rw [toStr_val, usize4_val]; decide

/-- `MODULUS_XOR_TWO_MODULUS` is `ok` with value `p XOR 2p` (2p < 2^256, so no truncation). -/
theorem MODULUS_XOR_TWO_MODULUS_ok :
    ∃ m, field.verified.invert.invert.step.MODULUS_XOR_TWO_MODULUS = ok m
      ∧ m.toNat = p ^^^ (2 * p) := by
  refine ⟨Uint.ofNat 4#usize 57896044618658097711785492504343953926668720685020371267821459143285372248565, ?_, ?_⟩
  · unfold field.verified.invert.invert.step.MODULUS_XOR_TWO_MODULUS
    exact Uint.from_be_hex_ok _ _ _ (len_MX2M _) (parse_MX2M _)
  · rw [Uint4.toNat_ofNat (by norm_num)]
    unfold p
    decide

end Constants

/-! ## `@[step]` Hoare-triple forms

Triple versions of the lemmas above, consumable by the `step` tactic on the
generated monadic code (`let x ← foo …`). -/

private theorem ok_spec {α : Type u} {x : α} {post : α → Prop} (h : post x) :
    (ok x : Result α) ⦃ v => post v ⦄ := by
  rw [Aeneas.Std.WP.spec_ok]
  exact h

private theorem spec_of_eq_ok {α : Type u} {m : Result α} {x : α} {post : α → Prop}
    (heq : m = ok x) (h : post x) : m ⦃ v => post v ⦄ := by
  rw [heq, Aeneas.Std.WP.spec_ok]
  exact h

@[step] theorem Limb.wrapping_add_spec (a b : Limb) :
    crypto_bigint.limb.add.Limb.wrapping_add a b
      ⦃ r => r.val = (a.val + b.val) % 2^64 ⦄ := by
  obtain ⟨r, heq, h⟩ := Limb.wrapping_add_ok a b
  exact spec_of_eq_ok heq h

@[step] theorem Limb.bitand_spec (a b : Limb) :
    Limb.Insts.CoreOpsBitBitAndLimbLimb.bitand a b
      ⦃ r => r.val = a.val &&& b.val ⦄ := by
  obtain ⟨r, heq, h⟩ := Limb.bitand_ok a b
  exact spec_of_eq_ok heq h

@[step] theorem Limb.bitor_spec (a b : Limb) :
    Limb.Insts.CoreOpsBitBitOrLimbLimb.bitor a b
      ⦃ r => r.val = a.val ||| b.val ⦄ := by
  obtain ⟨r, heq, h⟩ := Limb.bitor_ok a b
  exact spec_of_eq_ok heq h

@[step] theorem Limb.bitxor_spec (a b : Limb) :
    Limb.Insts.CoreOpsBitBitXorLimbLimb.bitxor a b
      ⦃ r => r.val = a.val ^^^ b.val ⦄ := by
  obtain ⟨r, heq, h⟩ := Limb.bitxor_ok a b
  exact spec_of_eq_ok heq h

@[step] theorem Limb.not_spec (a : Limb) :
    Limb.Insts.CoreOpsBitNotLimb.not a
      ⦃ r => r.val = 2^64 - 1 - a.val ⦄ := by
  obtain ⟨r, heq, h⟩ := Limb.not_ok a
  exact spec_of_eq_ok heq h

@[step] theorem Limb.wrapping_neg_spec (a : Limb) :
    crypto_bigint.limb.neg.Limb.wrapping_neg a
      ⦃ r => r.val = (2^64 - a.val) % 2^64 ⦄ := by
  obtain ⟨r, heq, h⟩ := Limb.wrapping_neg_ok a
  exact spec_of_eq_ok heq h

@[step] theorem Limb.ct_eq_spec (a b : Limb) :
    Limb.Insts.SubtleConstantTimeEq.ct_eq a b
      ⦃ c => c = true ↔ a.val = b.val ⦄ := by
  obtain ⟨c, heq, h⟩ := Limb.ct_eq_ok a b
  exact spec_of_eq_ok heq h

@[step] theorem Limb.mac_spec (a b c carry : Limb) :
    crypto_bigint.limb.mul.Limb.mac a b c carry
      ⦃ lo hi => lo.val + 2^64 * hi.val = a.val + b.val * c.val + carry.val ⦄ := by
  obtain ⟨lo, hi, heq, h, _, _⟩ := Limb.mac_ok a b c carry
  rw [heq, Aeneas.Std.WP.spec_ok]
  exact h

@[step] theorem Limb.shl_spec (a : Limb) (s : Usize) (hs : s.val < 64) :
    Limb.Insts.CoreOpsBitShlUsizeLimb.shl a s
      ⦃ r => r.val = (a.val <<< s.val) % 2^64 ⦄ := by
  obtain ⟨r, heq, h⟩ := Limb.shl_ok a s hs
  exact spec_of_eq_ok heq h

@[step] theorem Limb.shr_spec (a : Limb) (s : Usize) (hs : s.val < 64) :
    Limb.Insts.CoreOpsBitShrUsizeLimb.shr a s
      ⦃ r => r.val = a.val >>> s.val ⦄ := by
  obtain ⟨r, heq, h⟩ := Limb.shr_ok a s hs
  exact spec_of_eq_ok heq h

@[step] theorem Limb.clone_spec (a : Limb) :
    Limb.Insts.CoreCloneClone.clone a ⦃ r => r = a ⦄ :=
  spec_of_eq_ok (Limb.clone_ok a) rfl

@[step] theorem Limb.ZERO_spec : crypto_bigint.limb.Limb.ZERO ⦃ z => z.val = 0 ⦄ := by
  obtain ⟨z, heq, h⟩ := Limb.ZERO_ok
  exact spec_of_eq_ok heq h

@[step] theorem Limb.ONE_spec : crypto_bigint.limb.Limb.ONE ⦃ o => o.val = 1 ⦄ := by
  obtain ⟨o, heq, h⟩ := Limb.ONE_ok
  exact spec_of_eq_ok heq h

@[step] theorem Limb.MAX_spec : crypto_bigint.limb.Limb.MAX ⦃ m => m.val = 2^64 - 1 ⦄ := by
  obtain ⟨m, heq, h⟩ := Limb.MAX_ok
  exact spec_of_eq_ok heq h

@[step] theorem Limb.BITS_spec : crypto_bigint.limb.Limb.BITS ⦃ b => b.val = 64 ⦄ := by
  obtain ⟨b, heq, h⟩ := Limb.BITS_ok
  exact spec_of_eq_ok heq h

@[step] theorem Uint.wrapping_add_spec {LIMBS : Usize} (a b : Uint LIMBS) :
    crypto_bigint.uint.add.Uint.wrapping_add a b
      ⦃ r => r.toNat = (a.toNat + b.toNat) % 2^(64 * LIMBS.val) ⦄ := by
  obtain ⟨r, heq, h⟩ := Uint.wrapping_add_ok a b
  exact spec_of_eq_ok heq h

@[step] theorem Uint.wrapping_sub_spec {LIMBS : Usize} (a b : Uint LIMBS) :
    crypto_bigint.uint.sub.Uint.wrapping_sub a b
      ⦃ r => r.toNat = (a.toNat + 2^(64 * LIMBS.val) - b.toNat) % 2^(64 * LIMBS.val) ⦄ := by
  obtain ⟨r, heq, h⟩ := Uint.wrapping_sub_ok a b
  exact spec_of_eq_ok heq h

@[step] theorem Uint.sbb_spec {LIMBS : Usize} (a b : Uint LIMBS) (borrow : Limb) :
    crypto_bigint.uint.sub.Uint.sbb a b borrow
      ⦃ d bo => (if a.toNat < b.toNat + borrow.val >>> 63
                 then d.toNat + (b.toNat + borrow.val >>> 63) = a.toNat + 2^(64 * LIMBS.val)
                      ∧ bo.val = 2^64 - 1
                 else d.toNat + (b.toNat + borrow.val >>> 63) = a.toNat ∧ bo.val = 0) ⦄ := by
  obtain ⟨d, bo, heq, h⟩ := Uint.sbb_ok' a b borrow
  rw [heq, Aeneas.Std.WP.spec_ok]
  exact h

@[step] theorem Uint.mul_wide_spec {LIMBS HLIMBS : Usize} (a : Uint LIMBS) (b : Uint HLIMBS) :
    crypto_bigint.uint.mul.Uint.mul_wide a b
      ⦃ lo hi => lo.toNat + 2^(64 * LIMBS.val) * hi.toNat = a.toNat * b.toNat ⦄ := by
  obtain ⟨lo, hi, heq, h, _, _⟩ := Uint.mul_wide_ok a b
  rw [heq, Aeneas.Std.WP.spec_ok]
  exact h

@[step] theorem Uint.square_wide_spec {LIMBS : Usize} (a : Uint LIMBS) :
    crypto_bigint.uint.mul.Uint.square_wide a
      ⦃ lo hi => lo.toNat + 2^(64 * LIMBS.val) * hi.toNat = a.toNat * a.toNat ⦄ := by
  obtain ⟨lo, hi, heq, h, _, _⟩ := Uint.square_wide_ok a
  rw [heq, Aeneas.Std.WP.spec_ok]
  exact h

@[step] theorem Uint.shl_vartime_spec {LIMBS : Usize} (a : Uint LIMBS) (s : Usize)
    (hs : s.val < 64 * LIMBS.val) :
    crypto_bigint.uint.shl.Uint.shl_vartime a s
      ⦃ r => r.toNat = (a.toNat * 2^s.val) % 2^(64 * LIMBS.val) ⦄ := by
  obtain ⟨r, heq, h⟩ := Uint.shl_vartime_ok a s hs
  exact spec_of_eq_ok heq h

@[step] theorem Uint.shr_vartime_spec {LIMBS : Usize} (a : Uint LIMBS) (s : Usize)
    (hs : s.val < 64 * LIMBS.val) :
    crypto_bigint.uint.shr.Uint.shr_vartime a s
      ⦃ r => r.toNat = a.toNat / 2^s.val ⦄ := by
  obtain ⟨r, heq, h⟩ := Uint.shr_vartime_ok a s hs
  exact spec_of_eq_ok heq h

@[step] theorem Uint.as_limbs_spec {LIMBS : Usize} (u : Uint LIMBS) :
    crypto_bigint.uint.Uint.as_limbs u ⦃ l => l = u ⦄ :=
  spec_of_eq_ok (Uint.as_limbs_ok u) rfl

@[step] theorem Uint.as_limbs_mut_spec {LIMBS : Usize} (u : Uint LIMBS) :
    crypto_bigint.uint.Uint.as_limbs_mut u
      ⦃ l back => l = u ∧ back = (fun a => a) ⦄ := by
  rw [Uint.as_limbs_mut_ok, Aeneas.Std.WP.spec_ok]
  exact ⟨rfl, rfl⟩

@[step] theorem Uint.conditional_select_spec {LIMBS : Usize} (a b : Uint LIMBS)
    (c : subtle.Choice) :
    Uint.Insts.SubtleConditionallySelectable.conditional_select a b c
      ⦃ r => r = if c then b else a ⦄ :=
  spec_of_eq_ok (Uint.conditional_select_ok a b c) rfl

@[step] theorem Uint.ZERO_spec (LIMBS : Usize) :
    crypto_bigint.uint.Uint.ZERO LIMBS ⦃ z => z.toNat = 0 ⦄ := by
  obtain ⟨z, heq, h⟩ := Uint.ZERO_ok LIMBS
  exact spec_of_eq_ok heq h

@[step] theorem Uint.ONE_spec (LIMBS : Usize) (h : 0 < LIMBS.val) :
    crypto_bigint.uint.Uint.ONE LIMBS ⦃ o => o.toNat = 1 ⦄ := by
  obtain ⟨o, heq, ho⟩ := Uint.ONE_ok LIMBS h
  exact spec_of_eq_ok heq ho

@[step] theorem Uint.LIMBS_1_spec (LIMBS : Usize) :
    crypto_bigint.uint.Uint.LIMBS_1 LIMBS ⦃ l => l = LIMBS ⦄ :=
  spec_of_eq_ok (Uint.LIMBS_1_ok LIMBS) rfl

@[step] theorem Uint.from_le_slice_spec (LIMBS : Usize) (s : Slice Std.U8)
    (hlen : s.val.length = 8 * LIMBS.val) :
    crypto_bigint.uint.encoding.Uint.from_le_slice LIMBS s
      ⦃ r => r.toNat = leBytesToNat s.val ⦄ := by
  obtain ⟨r, heq, h⟩ := Uint.from_le_slice_ok LIMBS s hlen
  exact spec_of_eq_ok heq h

@[step] theorem Uint4.to_le_bytes_spec (u : Uint4) :
    Uint4.Insts.Crypto_bigintTraitsEncodingArrayU832.to_le_bytes u
      ⦃ bytes => leBytesToNat bytes.val = u.toNat ⦄ := by
  obtain ⟨bytes, heq, h⟩ := Uint4.to_le_bytes_ok u
  exact spec_of_eq_ok heq h

@[step] theorem Choice.not_spec (c : subtle.Choice) :
    subtle.Choice.Insts.CoreOpsBitNotChoice.not c ⦃ r => r = !c ⦄ :=
  spec_of_eq_ok (Choice.not_ok c) rfl

@[step] theorem Choice.from_spec (u : Std.U8) :
    subtle.Choice.Insts.CoreConvertFromU8.from u
      ⦃ c => c = true ↔ u.val ≠ 0 ⦄ := by
  obtain ⟨c, heq, h⟩ := Choice.from_ok u
  exact spec_of_eq_ok heq h

@[step] theorem CtOption.new_spec {T : Type} (v : T) (c : subtle.Choice) :
    subtle.CtOption.new v c ⦃ r => r = (v, c) ⦄ :=
  spec_of_eq_ok (CtOption.new_ok v c) rfl

@[step] theorem MODULUS_spec : field.MODULUS ⦃ m => m.toNat = p ⦄ := by
  obtain ⟨m, heq, h⟩ := MODULUS_ok
  exact spec_of_eq_ok heq h

@[step] theorem MODULUS_255_DISTANCE_spec :
    field.verified.MODULUS_255_DISTANCE ⦃ m => m.toNat = 2^255 - p ⦄ := by
  obtain ⟨m, heq, h⟩ := MODULUS_255_DISTANCE_ok
  exact spec_of_eq_ok heq h

@[step] theorem TWO_MODULUS_255_DISTANCE_spec :
    field.verified.red.TWO_MODULUS_255_DISTANCE ⦃ m => m.toNat = 2 * (2^255 - p) ⦄ := by
  obtain ⟨m, heq, h⟩ := TWO_MODULUS_255_DISTANCE_ok
  exact spec_of_eq_ok heq h

@[step] theorem MODULUS_XOR_TWO_MODULUS_spec :
    field.verified.invert.invert.step.MODULUS_XOR_TWO_MODULUS
      ⦃ m => m.toNat = p ^^^ (2 * p) ⦄ := by
  obtain ⟨m, heq, h⟩ := MODULUS_XOR_TWO_MODULUS_ok
  exact spec_of_eq_ok heq h

end HelioseleneSpec
