/- Correctness of the reduction pipeline and of field multiplication/squaring:

     `red256_ok`  : `field.verified.red.red256` reduces any 256-bit value mod `p`
     `red512_ok`  : `field.verified.red.red512` reduces any 512-bit value mod `p`
     `mul_ok`     : `HelioseleneField` multiplication computes `(a·b) mod p`
     `square_ok`  : `field.verified.square` computes `(a·a) mod p`

   Everything in this file is PROVED: no `sorry`, and none of the proofs below use
   `native_decide` or introduce axioms. (Like every Spec file, the statements
   transitively inherit the `_native.decide` axioms attached to the generated
   constants `field.MODULUS` / `MODULUS_255_DISTANCE` / `TWO_MODULUS_255_DISTANCE`
   in Funs.lean, whose `Aeneas.Std.toStr` autoParam is `by decide +native`.)

   Proof style: the generated loops all have concrete small ranges (≤ 4 iterations),
   so they are brute-unrolled with the `loop_step` helper below, driving each body
   through the `step` tactic; array states are tracked as literal 4/6/8-element
   limb lists, and the final value/congruence goals are discharged by `omega`
   (all products that appear are `variable · constant-limb` and hence linear). -/
import HelioseleneCore.Spec.Phi

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open Aeneas Aeneas.Std Result ControlFlow
open helioselene

namespace HelioseleneSpec

open crypto_bigint.uint crypto_bigint.limb HelioseleneModel

/-! ## Generic helpers -/

/-- One unfolding of the Aeneas `loop` combinator, in weakest-precondition form:
    to prove a spec of `loop body x` it suffices to run `body x` and, on `cont`,
    prove the spec of the restarted loop. Applying this lemma `k+1` times fully
    unrolls a `k`-iteration loop. -/
private theorem loop_step {α : Type u} {β : Type v} {body : α → Result (ControlFlow α β)}
    {x : α} {post : β → Prop}
    (h : Aeneas.Std.WP.spec (body x) (fun r => match r with
       | ControlFlow.cont x' => Aeneas.Std.WP.spec (Aeneas.Std.loop body x') post
       | ControlFlow.done y => post y)) :
    Aeneas.Std.WP.spec (Aeneas.Std.loop body x) post := by
  rw [Aeneas.Std.loop]
  cases hb : body x with
  | ok r =>
    rw [hb, Aeneas.Std.WP.spec_ok] at h
    cases r with
    | cont x' => exact h
    | done y => rw [Aeneas.Std.WP.spec_ok]; exact h
  | fail e => rw [hb, Aeneas.Std.WP.spec_fail] at h; exact h.elim
  | div => rw [hb, Aeneas.Std.WP.spec_div] at h; exact h.elim

/-- `spec` of an `ok` computation from its postcondition; `exact spec_ok_of h`
    unifies through `let`/`match`-on-constructor redexes (whnf), which
    `simp only [spec_ok]` does not. -/
private theorem spec_ok_of {α : Type u} {x : α} {post : α → Prop} (h : post x) :
    Aeneas.Std.WP.spec (ok x) post := (Aeneas.Std.WP.spec_ok x).mpr h

/-! ### Destructuring fixed-length limb vectors into literal lists -/

private theorem List.exists_len2 {α : Type u} : ∀ (l : List α), l.length = 2 →
    ∃ a b, l = [a, b]
  | [a, b], _ => ⟨a, b, rfl⟩

private theorem List.exists_len4 {α : Type u} : ∀ (l : List α), l.length = 4 →
    ∃ a b c d, l = [a, b, c, d]
  | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

private theorem List.exists_len8 {α : Type u} : ∀ (l : List α), l.length = 8 →
    ∃ a b c d e f g h, l = [a, b, c, d, e, f, g, h]
  | [a, b, c, d, e, f, g, h], _ => ⟨a, b, c, d, e, f, g, h, rfl⟩

private theorem Uint2.exists_limbs (u : Uint2) : ∃ a b, u.val = [a, b] :=
  List.exists_len2 u.val (by rw [Aeneas.Std.Array.length_eq]; simp)

private theorem Uint4.exists_limbs (u : Uint4) : ∃ a b c d, u.val = [a, b, c, d] :=
  List.exists_len4 u.val (by rw [Aeneas.Std.Array.length_eq]; simp)

/-- `toNat` of a 4-limb vector with a known limb list. -/
private theorem toNat_limbs4 (u : Uint4) {e0 e1 e2 e3 : Limb} (h : u.val = [e0, e1, e2, e3]) :
    u.toNat = e0.val + 2^64 * e1.val + 2^128 * e2.val + 2^192 * e3.val := by
  unfold crypto_bigint.uint.Uint.toNat
  rw [h]
  simp [List.foldr]
  ring

/-- `toNat` of a 2-limb vector with a known limb list. -/
private theorem toNat_limbs2 (u : Uint2) {e0 e1 : Limb} (h : u.val = [e0, e1]) :
    u.toNat = e0.val + 2^64 * e1.val := by
  unfold crypto_bigint.uint.Uint.toNat
  rw [h]
  simp [List.foldr]
  ring

/-! ### Step wrappers for the pure operations appearing in the reduction code -/

private theorem fromU64Bool_val (b : Bool) :
    (core.convert.num.FromU64Bool.from b).val = if b then 1 else 0 := by
  cases b <;> simp [core.convert.num.FromU64Bool.from]

@[step] private theorem FromU64Bool_spec (b : Bool) :
    (lift (core.convert.num.FromU64Bool.from b) : Result Std.U64)
      ⦃ r => r = core.convert.num.FromU64Bool.from b ⦄ := by
  simp only [Aeneas.Std.lift, Aeneas.Std.WP.spec_ok]

@[step] private theorem U64or_spec (a b : Std.U64) :
    (lift (a ||| b) : Result Std.U64) ⦃ r => r.val = a.val ||| b.val ⦄ := by
  simp only [Aeneas.Std.lift, Aeneas.Std.WP.spec_ok]
  exact BitVec.toNat_or a.bv b.bv

private theorem usize_size_cases :
    UScalar.size .Usize = 2^32 ∨ UScalar.size .Usize = 2^64 := by
  rw [UScalar.size_def]
  rcases System.Platform.numBits_eq with h | h <;>
    rw [UScalarTy.Usize_numBits_eq, h]
  · left; rfl
  · right; rfl

@[step] private theorem Usize_wrapping_sub_spec (x y : Usize) (h : y.val ≤ x.val) :
    (lift (Std.Usize.wrapping_sub x y) : Result Usize) ⦃ r => r.val = x.val - y.val ⦄ := by
  simp only [Aeneas.Std.lift, Aeneas.Std.WP.spec_ok, Usize.wrapping_sub_val_eq]
  have hx : x.val < UScalar.size .Usize := by
    have := x.hBounds
    rw [UScalar.size_def]
    omega
  rcases usize_size_cases with hs | hs <;> rw [hs] at hx ⊢ <;> omega

@[step] private theorem Usize_wrapping_add_spec (x y : Usize) (h : x.val + y.val < 2^32) :
    (lift (Std.Usize.wrapping_add x y) : Result Usize) ⦃ r => r.val = x.val + y.val ⦄ := by
  simp only [Aeneas.Std.lift, Aeneas.Std.WP.spec_ok, Usize.wrapping_add_val_eq]
  rcases usize_size_cases with hs | hs <;> rw [hs] <;> omega

/-- `overflowing_add` in linear-equation form: the carry is exposed as a bounded
    natural number `cv` (omega-friendly), linked to the boolean flag through
    `FromU64Bool.from` (which is exactly how the generated code consumes it). -/
@[step] private theorem U64_oadd_spec (x y : Std.U64) :
    (lift (core.num.U64.overflowing_add x y) : Result (Std.U64 × Bool))
      ⦃ z c => ∃ cv : ℕ, cv ≤ 1 ∧ z.val + 2^64 * cv = x.val + y.val
          ∧ (core.convert.num.FromU64Bool.from c).val = cv ⦄ := by
  simp only [Aeneas.Std.lift, Aeneas.Std.WP.spec_ok]
  refine ⟨(core.convert.num.FromU64Bool.from (core.num.U64.overflowing_add x y).2).val,
    ?_, ?_, rfl⟩
  · rw [fromU64Bool_val]; split <;> omega
  · rw [fromU64Bool_val]; exact U64.overflowing_add_val x y

@[step] private theorem Array_to_slice_spec {α : Type} {n : Usize} (a : Aeneas.Std.Array α n) :
    (lift (Aeneas.Std.Array.to_slice a) : Result (Slice α)) ⦃ s => s.val = a.val ⦄ := by
  simp only [Aeneas.Std.lift, Aeneas.Std.WP.spec_ok, Aeneas.Std.Array.val_to_slice]

/-! ### Small `Nat` bit-arithmetic helpers -/

/-- AND with an all-zeros/all-ones mask, resolved by an `if` on the mask value. -/
private theorem mask_and (m x : ℕ) (hx : x < 2^64) (hm : m = 0 ∨ m = 2^64 - 1) :
    m &&& x = if m = 0 then 0 else x := by
  rcases hm with h | h
  · rw [h, if_pos rfl]
    simp
  · rw [h, if_neg (by norm_num)]
    rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]

/-! ## Specs of the small helioselene helper functions -/

/-- `select_word x y c` with an all-zeros/all-ones mask `c` selects `x`/`y`. -/
private theorem select_word_spec (x y c : Limb)
    (hb : c.val = 0 ∨ c.val = 2^64 - 1) :
    field.verified.select_word x y c
      ⦃ r => r.val = if c.val = 0 then x.val else y.val ⦄ := by
  unfold field.verified.select_word
  step as ⟨t, ht⟩
  step as ⟨t1, ht1⟩
  step as ⟨r, hr⟩
  rcases hb with hb | hb
  · rw [hb, Nat.and_zero] at ht1
    rw [ht1, Nat.xor_zero] at hr
    simp [hb, hr]
  · rw [hb] at ht1
    have htlt : t.val < 2^64 := t.hBounds
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt htlt] at ht1
    rw [ht1, ht] at hr
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at hr
    simp [hb, hr]

/-- `add_with_bounded_overflow` is an exact full adder with a 0/1 carry. -/
private theorem awbo_spec (a b c : Limb) (hc : c.val ≤ 1) :
    field.verified.add_with_bounded_overflow a b c
      ⦃ s cout => s.val + 2^64 * cout.val = a.val + b.val + c.val ∧ cout.val ≤ 1 ⦄ := by
  unfold field.verified.add_with_bounded_overflow
  step as ⟨limb, carry1, cv1, hcv1le, hcv1, hlink1⟩
  step as ⟨limb1, carry2, cv2, hcv2le, hcv2, hlink2⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  rw [hi, hi1, hlink1, hlink2] at hi2
  have ha : a.val < 2^64 := a.hBounds
  have hb : b.val < 2^64 := b.hBounds
  have hl : limb.val < 2^64 := limb.hBounds
  have hl1 : limb1.val < 2^64 := limb1.hBounds
  have hboth : ¬(cv1 = 1 ∧ cv2 = 1) := by
    rintro ⟨h1, h2⟩
    rw [h1] at hcv1
    rw [h2] at hcv2
    omega
  have hor : cv1 ||| cv2 = cv1 + cv2 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcv1le with h1 | h1 <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcv2le with h2 | h2
    · rw [h1, h2]; decide
    · rw [h1, h2]; decide
    · rw [h1, h2]; decide
    · exact absurd ⟨h1, h2⟩ hboth
  rw [hor] at hi2
  constructor
  · rw [hi2]; omega
  · omega

/-- `sub_value a b` = `sbb a b 0`: exact 256-bit subtraction with the borrow
    reported as an all-zeros/all-ones limb. -/
private theorem sub_value_spec (a b : Uint4) :
    field.verified.sub_value a b
      ⦃ d bo => (if a.toNat < b.toNat
                 then d.toNat + b.toNat = a.toNat + 2^256 ∧ bo.val = 2^64 - 1
                 else d.toNat + b.toNat = a.toNat ∧ bo.val = 0) ⦄ := by
  unfold field.verified.sub_value
  step as ⟨z, hz⟩
  have hz63 : z.val >>> 63 = 0 := by rw [hz]; simp
  step as ⟨d, bo, hsbb⟩
  rw [hz63] at hsbb
  split at hsbb <;> split <;> omega

/-! ## Limb decompositions of the reduction constants -/

/-- The two 64-bit limbs of `MODULUS_255_DISTANCE` = 2^255 - p. -/
private theorem M255D_limbs_spec :
    field.verified.MODULUS_255_DISTANCE
      ⦃ m => ∃ d0 d1, m.val = [d0, d1]
          ∧ d0.val = 466954441315983533 ∧ d1.val = 633520882758061288 ⦄ := by
  obtain ⟨m, heq, hm⟩ := MODULUS_255_DISTANCE_ok
  rw [heq, Aeneas.Std.WP.spec_ok]
  obtain ⟨d0, d1, hval⟩ := Uint2.exists_limbs m
  have hsum := toNat_limbs2 m hval
  rw [hm] at hsum
  have h0 : d0.val < 2^64 := d0.hBounds
  have h1 : d1.val < 2^64 := d1.hBounds
  unfold p at hsum
  norm_num at hsum
  exact ⟨d0, d1, hval, by omega, by omega⟩

/-- The two 64-bit limbs of `TWO_MODULUS_255_DISTANCE` = 2·(2^255 - p) = 2^256 - 2p. -/
private theorem TWO_M255D_limbs_spec :
    field.verified.red.TWO_MODULUS_255_DISTANCE
      ⦃ m => ∃ e0 e1, m.val = [e0, e1]
          ∧ e0.val = 933908882631967066 ∧ e1.val = 1267041765516122576 ⦄ := by
  obtain ⟨m, heq, hm⟩ := TWO_MODULUS_255_DISTANCE_ok
  rw [heq, Aeneas.Std.WP.spec_ok]
  obtain ⟨e0, e1, hval⟩ := Uint2.exists_limbs m
  have hsum := toNat_limbs2 m hval
  rw [hm] at hsum
  have h0 : e0.val < 2^64 := e0.hBounds
  have h1 : e1.val < 2^64 := e1.hBounds
  unfold p at hsum
  norm_num at hsum
  exact ⟨e0, e1, hval, by omega, by omega⟩

/-! ## `red1`: one conditional subtraction of the modulus

`red1_ok` also lives (independently proved) in `Spec.Linear`; the copy here is
`private` to avoid a name clash — `Reduction` may not import `Linear`. -/

/-- The conditional-move loop of `red1`: with an all-zeros mask it returns the
    `reduced` limbs, with an all-ones mask the original limbs. -/
private theorem red1_loop_spec (iter : core.ops.range.Range Usize)
    (a reduced : Uint4) (borrow : Limb) (out : Uint4)
    (a0 a1 a2 a3 r0 r1 r2 r3 z0 z1 z2 z3 : Limb)
    (hs : iter.start.val = 0) (he : iter.«end».val = 4)
    (haval : a.val = [a0, a1, a2, a3]) (hrval : reduced.val = [r0, r1, r2, r3])
    (hzval : out.val = [z0, z1, z2, z3])
    (hb : borrow.val = 0 ∨ borrow.val = 2^64 - 1) :
    field.verified.red1_loop iter a reduced borrow out ⦃ o =>
      ∃ w0 w1 w2 w3, o.val = [w0, w1, w2, w3]
        ∧ w0.val = (if borrow.val = 0 then r0.val else a0.val)
        ∧ w1.val = (if borrow.val = 0 then r1.val else a1.val)
        ∧ w2.val = (if borrow.val = 0 then r2.val else a2.val)
        ∧ w3.val = (if borrow.val = 0 then r3.val else a3.val) ⦄ := by
  unfold field.verified.red1_loop
  -- iteration 1 : j = 0
  apply loop_step
  unfold field.verified.red1_loop.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨ra, hra⟩
  step as ⟨l, hl⟩
  step as ⟨aa, haa⟩
  step as ⟨l1, hl1⟩
  step with (select_word_spec l l1 borrow hb) as ⟨w0, hw0⟩
  step as ⟨ob, back, hob, hback⟩
  step as ⟨o1, ho1⟩
  simp only [hra, hrval, hs] at hl
  simp at hl
  simp only [haa, haval, hs] at hl1
  simp at hl1
  have hoval1 : o1.val = [w0, z1, z2, z3] := by
    rw [ho1, Array.set_val_eq, hob, hzval, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback]
  -- iteration 2 : j = 1
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨ra2, hra2⟩
  step as ⟨l2, hl2⟩
  step as ⟨aa2, haa2⟩
  step as ⟨l3, hl3⟩
  step with (select_word_spec l2 l3 borrow hb) as ⟨w1, hw1⟩
  step as ⟨ob2, back2, hob2, hback2⟩
  step as ⟨o2', ho2'⟩
  simp only [hra2, hrval, hs1, hs] at hl2
  simp at hl2
  simp only [haa2, haval, hs1, hs] at hl3
  simp at hl3
  have hoval2 : o2'.val = [w0, w1, z2, z3] := by
    rw [ho2', Array.set_val_eq, hob2, hoval1, hs1, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback2]
  -- iteration 3 : j = 2
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨ra3, hra3⟩
  step as ⟨l4, hl4⟩
  step as ⟨aa3, haa3⟩
  step as ⟨l5, hl5⟩
  step with (select_word_spec l4 l5 borrow hb) as ⟨w2, hw2⟩
  step as ⟨ob3, back3, hob3, hback3⟩
  step as ⟨o3', ho3'⟩
  simp only [hra3, hrval, hs2, hs1, hs] at hl4
  simp at hl4
  simp only [haa3, haval, hs2, hs1, hs] at hl5
  simp at hl5
  have hoval3 : o3'.val = [w0, w1, w2, z3] := by
    rw [ho3', Array.set_val_eq, hob3, hoval2, hs2, hs1, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback3]
  -- iteration 4 : j = 3
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter3 (by
      simp only [he3, he2, he1]; omega))
  intro ⟨o4, iter4⟩ ⟨ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨ra4, hra4⟩
  step as ⟨l6, hl6⟩
  step as ⟨aa4, haa4⟩
  step as ⟨l7, hl7⟩
  step with (select_word_spec l6 l7 borrow hb) as ⟨w3, hw3⟩
  step as ⟨ob4, back4, hob4, hback4⟩
  step as ⟨o4', ho4'⟩
  simp only [hra4, hrval, hs3, hs2, hs1, hs] at hl6
  simp at hl6
  simp only [haa4, haval, hs3, hs2, hs1, hs] at hl7
  simp at hl7
  have hoval4 : o4'.val = [w0, w1, w2, w3] := by
    rw [ho4', Array.set_val_eq, hob4, hoval3, hs3, hs2, hs1, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback4]
  -- iteration 5 : exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter4 (by
      simp only [he4, he3, he2, he1]; omega))
  intro ⟨o5, iter5⟩ ⟨ho5, hi5⟩
  simp only [ho5]
  refine spec_ok_of ⟨w0, w1, w2, w3, hoval4, ?_, ?_, ?_, ?_⟩
  · rw [hw0, hl, hl1]
  · rw [hw1, hl2, hl3]
  · rw [hw2, hl4, hl5]
  · rw [hw3, hl6, hl7]

/-- `red1` on an input `< 2p` returns the canonical representative mod `p`.
    (A copy of this spec is proved independently in `Spec.Linear`; kept private
    here because `Reduction` may not import that file.) -/
private theorem red1_spec (a : Uint4) (hlt : a.toNat < 2 * p) :
    field.verified.red1 a ⦃ r => r.toNat = a.toNat % p ⦄ := by
  unfold field.verified.red1
  step as ⟨m, hm⟩
  apply Aeneas.Std.WP.spec_bind (sub_value_spec a m)
  intro ⟨reduced, borrow⟩ hsub
  simp only [Aeneas.Std.WP.uncurry'_pair] at hsub
  step as ⟨z, hz⟩
  step as ⟨i, hi⟩
  obtain ⟨a0, a1, a2, a3, haval⟩ := Uint4.exists_limbs a
  obtain ⟨r0, r1, r2, r3, hrval⟩ := Uint4.exists_limbs reduced
  obtain ⟨z0, z1, z2, z3, hzval⟩ := Uint4.exists_limbs z
  have hbz : borrow.val = 0 ∨ borrow.val = 2^64 - 1 := by
    split at hsub <;> [exact Or.inr hsub.2; exact Or.inl hsub.2]
  rw [hi]
  apply Aeneas.Std.WP.spec_mono
    (red1_loop_spec { start := 0#usize, «end» := 4#usize } a reduced borrow z
      a0 a1 a2 a3 r0 r1 r2 r3 z0 z1 z2 z3 (by simp) (by simp)
      haval hrval hzval hbz)
  intro o ⟨w0, w1, w2, w3, hoval, hw0, hw1, hw2, hw3⟩
  have hosum := toNat_limbs4 o hoval
  have hasum := toNat_limbs4 a haval
  have hrsum := toNat_limbs4 reduced hrval
  have hppos := p_pos
  by_cases hab : a.toNat < m.toNat
  · -- a < p : borrow is all-ones, the original limbs are selected
    rw [if_pos hab] at hsub
    obtain ⟨heq, hbv⟩ := hsub
    rw [hbv] at hw0 hw1 hw2 hw3
    norm_num at hw0 hw1 hw2 hw3
    rw [hm] at hab
    rw [hosum, hw0, hw1, hw2, hw3, ← hasum, Nat.mod_eq_of_lt hab]
  · -- a ≥ p : borrow is zero, the reduced limbs are selected
    rw [if_neg hab] at hsub
    obtain ⟨heq, hbv⟩ := hsub
    rw [hbv] at hw0 hw1 hw2 hw3
    norm_num at hw0 hw1 hw2 hw3
    rw [hm] at heq hab
    have hred : reduced.toNat = a.toNat - p := by omega
    have hmod : a.toNat % p = a.toNat - p := by
      have h1 : a.toNat - p < p := by omega
      have h2 : a.toNat % p = (a.toNat - p) % p := by
        conv_lhs => rw [show a.toNat = (a.toNat - p) + 1 * p from by omega]
        rw [Nat.add_mul_mod_self_right]
      rw [h2, Nat.mod_eq_of_lt h1]
    rw [hosum, hw0, hw1, hw2, hw3, ← hrsum, hred, hmod]

/-! ## `red256`: reduction of an arbitrary 256-bit value -/

/-- First loop of `red256`: masked addition of `MODULUS_255_DISTANCE` into
    limbs 0-1, with a carry chain. The masked addends are reported as raw
    `&&&`-terms, resolved by the caller via `mask_and`. -/
private theorem red256_loop0_spec (iter : core.ops.range.Range Usize) (a : Uint4)
    (mask carry : Limb) (l0 l1 l2 l3 : Limb)
    (hs : iter.start.val = 0) (he : iter.«end».val = 2)
    (hval : a.val = [l0, l1, l2, l3]) (hc : carry.val = 0) :
    field.verified.red.red256_loop0 iter a mask carry ⦃ a' c' =>
      ∃ s0 s1, a'.val = [s0, s1, l2, l3] ∧ c'.val ≤ 1 ∧
        s0.val + 2^64 * s1.val + 2^128 * c'.val
          = l0.val + 2^64 * l1.val + (mask.val &&& 466954441315983533)
            + 2^64 * (mask.val &&& 633520882758061288) ⦄ := by
  unfold field.verified.red.red256_loop0
  -- iteration 1 : j = 0
  apply loop_step
  unfold field.verified.red.red256_loop0.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨a1, ha1⟩
  step with M255D_limbs_spec as ⟨u, d0, d1, huval, hd0, hd1⟩
  step as ⟨l, hl⟩
  step as ⟨ua, hua⟩
  step as ⟨ld, hld⟩
  step as ⟨l2m, hl2m⟩
  step with (awbo_spec l l2m carry (by omega)) as ⟨s0, c1, hsum1, hc1⟩
  step as ⟨a2, back, ha2, hback⟩
  step as ⟨a3, ha3⟩
  simp only [ha1, hval, hs] at hl
  simp at hl
  simp only [hua, huval, hs] at hld
  simp at hld
  have ha3val : a3.val = [s0, l1, l2, l3] := by
    rw [ha3, Array.set_val_eq, ha2, hval, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback]
  -- iteration 2 : j = 1
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨a1', ha1'⟩
  step with M255D_limbs_spec as ⟨u', d0', d1', huval', hd0', hd1'⟩
  step as ⟨l', hl'⟩
  step as ⟨ua', hua'⟩
  step as ⟨ld', hld'⟩
  step as ⟨l2m', hl2m'⟩
  step with (awbo_spec l' l2m' c1 hc1) as ⟨s1, c2, hsum2, hc2⟩
  step as ⟨a2', back', ha2', hback'⟩
  step as ⟨a3', ha3'⟩
  simp only [ha1', ha3val, hs1, hs] at hl'
  simp at hl'
  simp only [hua', huval', hs1, hs] at hld'
  simp at hld'
  have ha3val' : a3'.val = [s0, s1, l2, l3] := by
    rw [ha3', Array.set_val_eq, ha2', ha3val, hs1, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback']
  -- iteration 3 : exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hi3⟩
  simp only [ho3]
  refine spec_ok_of ⟨s0, s1, ha3val', hc2, ?_⟩
  rw [hl2m, hld, hd0] at hsum1
  rw [hl2m', hld', hd1'] at hsum2
  rw [hl] at hsum1
  rw [hl'] at hsum2
  rw [hc] at hsum1
  omega

/-- Second loop of `red256`: carry propagation through limbs 2-3
    (the final carry out of limb 3 is dropped by the code and reported here). -/
private theorem red256_loop1_spec (iter : core.ops.range.Range Usize) (a : Uint4)
    (carry : Limb) (l0 l1 l2 l3 : Limb)
    (hs : iter.start.val = 2) (he : iter.«end».val = 4)
    (hval : a.val = [l0, l1, l2, l3]) :
    field.verified.red.red256_loop1 iter a carry ⦃ a' =>
      ∃ s2 s3 c4, a'.val = [l0, l1, s2, s3] ∧ c4 ≤ 1 ∧
        s2.val + 2^64 * s3.val + 2^128 * c4 = l2.val + 2^64 * l3.val + carry.val ⦄ := by
  unfold field.verified.red.red256_loop1
  -- iteration 1 : j = 2
  apply loop_step
  unfold field.verified.red.red256_loop1.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨a1, ha1⟩
  step as ⟨l, hl⟩
  step as ⟨limb, carry_bool, cv, hcv1, hcv, hlink⟩
  step as ⟨i, hi⟩
  step as ⟨a2, back, ha2, hback⟩
  step as ⟨a3, ha3⟩
  simp only [ha1, hval, hs] at hl
  simp at hl
  have hi' : i.val = cv := by rw [hi]; exact hlink
  have hval3 : a3.val = [l0, l1, limb, l3] := by
    rw [ha3, Array.set_val_eq, ha2, hval, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback]
  -- iteration 2 : j = 3
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨b1, hb1⟩
  step as ⟨m, hm⟩
  step as ⟨limb2, carry_bool2, cw, hcw1, hcw, hlink2⟩
  step as ⟨i2, hi2⟩
  step as ⟨b2, back2, hb2, hback2⟩
  step as ⟨b3, hb3⟩
  simp only [hb1, hval3, hs1, hs] at hm
  simp at hm
  have hi2' : i2.val = cw := by rw [hi2]; exact hlink2
  have hval4 : b3.val = [l0, l1, limb, limb2] := by
    rw [hb3, Array.set_val_eq, hb2, hval3, hs1, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback2]
  -- iteration 3 : exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hi3⟩
  simp only [ho3]
  refine spec_ok_of ⟨limb, limb2, cw, hval4, hcw1, ?_⟩
  rw [hl] at hcv
  rw [hm, hi'] at hcw
  omega

/-- `red256` computes the canonical representative mod `p` of any 256-bit input. -/
private theorem red256_spec (a : Uint4) :
    field.verified.red.red256 a ⦃ r => r.toNat = a.toNat % p ⦄ := by
  have hp : p = 57896044618658097711785492504343953926623305935230693509004809574567321395027 := rfl
  obtain ⟨x0, x1, x2, x3, hxval⟩ := Uint4.exists_limbs a
  have hx0 : x0.val < 2^64 := x0.hBounds
  have hx1 : x1.val < 2^64 := x1.hBounds
  have hx2 : x2.val < 2^64 := x2.hBounds
  have hx3 : x3.val < 2^64 := x3.hBounds
  have hasum := toNat_limbs4 a hxval
  unfold field.verified.red.red256
  step as ⟨a1, ha1⟩
  step as ⟨i, hi⟩
  simp only [hi]
  step as ⟨i1, hi1⟩
  step as ⟨l, hl⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  step as ⟨l1, hl1⟩
  step as ⟨high_bit, hhb⟩
  step as ⟨i4, hi4⟩
  step as ⟨l2, hl2⟩
  step as ⟨l3, hl3⟩
  step as ⟨l4, hl4⟩
  step as ⟨l5, hl5⟩
  step as ⟨a2, back, ha2, hback⟩
  step as ⟨i5, hi5⟩
  step as ⟨a3, ha3⟩
  step as ⟨carry, hcz⟩
  step as ⟨i6, hi6⟩
  simp only [hi6, hback]
  -- the top limb and the cleared top bit
  simp only [ha1, hxval, hi1] at hl
  simp at hl
  simp only [ha1, hxval, hi4] at hl2
  simp at hl2
  have hl1v : l1.val = x3.val >>> 63 := by
    rw [hl1, hl, hi3, hi2]
  have hbit : x3.val >>> 63 ≤ 1 := shiftRight63_le_one x3
  have hx3split : x3.val = 2^63 * (x3.val >>> 63) + x3.val % 2^63 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hl4v : l4.val = 2^63 - 1 := by
    rw [hl4, hl3]
    norm_num [Nat.shiftRight_eq_div_pow]
  have hl5v : l5.val = x3.val % 2^63 := by
    rw [hl5, hl2, hl4v, Nat.and_two_pow_sub_one_eq_mod]
  have ha3val : a3.val = [x0, x1, x2, l5] := by
    rw [ha3, Array.set_val_eq, ha2, hxval, hi5]
    rfl
  -- run the two loops
  apply Aeneas.Std.WP.spec_bind
    (red256_loop0_spec _ a3 high_bit carry x0 x1 x2 l5 (by simp) (by simp)
      ha3val hcz)
  intro ⟨a4, carry1⟩ ⟨s0, s1, hval4, hc1, hsum1⟩
  apply Aeneas.Std.WP.spec_bind
    (red256_loop1_spec _ a4 carry1 s0 s1 x2 l5 (by simp) (by simp) hval4)
  intro a5 ⟨s2, s3, c4, hval5, hc4, hsum2⟩
  have hs0 : s0.val < 2^64 := s0.hBounds
  have hs1' : s1.val < 2^64 := s1.hBounds
  have hs2 : s2.val < 2^64 := s2.hBounds
  have hs3 : s3.val < 2^64 := s3.hBounds
  have hl5b : l5.val < 2^64 := l5.hBounds
  have ha5sum := toNat_limbs4 a5 hval5
  -- resolve the mask
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbit with hbv | hbv
  · -- top bit clear : the mask is zero, nothing is added
    have hmask : high_bit.val = 0 := by
      rw [hhb, hl1v, hbv]
      norm_num
    rw [hmask] at hsum1
    simp only [Nat.zero_and] at hsum1
    -- value is unchanged and stays < 2^255
    have hval_eq : a5.toNat = a.toNat := by
      rw [ha5sum, hasum]
      omega
    have hlt : a5.toNat < 2 * p := by
      rw [hval_eq, hasum, hp]
      omega
    apply Aeneas.Std.WP.spec_bind (red1_spec a5 hlt)
    intro r hr
    exact spec_ok_of (by rw [hr, hval_eq])
  · -- top bit set : the all-ones mask adds 2^255 - p back in
    have hmask : high_bit.val = 2^64 - 1 := by
      rw [hhb, hl1v, hbv]
      norm_num
    rw [hmask,
        mask_and _ _ (by norm_num) (Or.inr rfl),
        mask_and _ _ (by norm_num) (Or.inr rfl),
        if_neg (by norm_num), if_neg (by norm_num)] at hsum1
    -- a5 = a - p, which is < 2p
    have hval_eq : a5.toNat + p = a.toNat := by
      rw [ha5sum, hasum, hp]
      omega
    have hlt : a5.toNat < 2 * p := by
      have := Uint4.toNat_lt a
      rw [hp] at hval_eq ⊢
      omega
    apply Aeneas.Std.WP.spec_bind (red1_spec a5 hlt)
    intro r hr
    exact spec_ok_of (by rw [hr, ← hval_eq, Nat.add_mod_right])

/-- Contract shape : `red256_ok`. -/
theorem red256_ok (a : Uint4) :
    ∃ r, field.verified.red.red256 a = .ok r ∧ r.toNat = a.toNat % p :=
  Aeneas.Std.WP.spec_imp_exists (red256_spec a)


/-! ## `red512`: Crandall reduction of a 512-bit value

The 8-limb working array is tracked as a literal list `[m0, …, m7]`; the two
mac passes fold the high limbs down against `D = TWO_MODULUS_255_DISTANCE`
(limbs `933908882631967066`, `1267041765516122576`), all products being
`variable · constant` and hence omega-linear. -/

/-- Nested mac loop of the first pass, row 2: one `j = 1` iteration acting on
    `limbs[3] += limbs[6] · D₁ + carry`. -/
private theorem red512_l0l0_row2_spec (i : Usize) (u : Uint2)
    (iter : core.ops.range.Range Usize) (limbs : Aeneas.Std.Array Limb 8#usize)
    (carry : Limb) (row : Usize)
    (m0 m1 m2 m3 m4 m5 m6 m7 e0 e1 : Limb)
    (hlimbs : limbs.val = [m0, m1, m2, m3, m4, m5, m6, m7]) (huval : u.val = [e0, e1])
    (hi : i.val = 4) (hrow : row.val = 2)
    (hs : iter.start.val = 1) (he : iter.«end».val = 2) :
    field.verified.red.red512_loop0_loop0 i u iter limbs carry row ⦃ out c' =>
      ∃ s, out.val = [m0, m1, m2, s, m4, m5, m6, m7] ∧
        s.val + 2^64 * c'.val = m3.val + m6.val * e1.val + carry.val ⦄ := by
  unfold field.verified.red.red512_loop0_loop0
  apply loop_step
  unfold field.verified.red.red512_loop0_loop0.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨i2, hi2⟩
  step as ⟨l, hl⟩
  step as ⟨i3, hi3⟩
  step as ⟨l1, hl1⟩
  step as ⟨ua, hua⟩
  step as ⟨l2, hl2⟩
  step as ⟨l3, c1, hmac⟩
  step as ⟨i4, hi4⟩
  step as ⟨a1, ha1⟩
  simp only [hlimbs, hi2, hs, hrow] at hl
  simp at hl
  simp only [hlimbs, hi3, hi, hrow] at hl1
  simp at hl1
  simp only [hua, huval, hs] at hl2
  simp at hl2
  have ha1val : a1.val = [m0, m1, m2, l3, m4, m5, m6, m7] := by
    rw [ha1, Array.set_val_eq, hlimbs, hi4, hs, hrow]
    rfl
  -- exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hi2'⟩
  simp only [ho2]
  refine spec_ok_of ⟨l3, ha1val, ?_⟩
  rw [hl, hl1, hl2] at hmac
  omega

/-- Nested mac loop of the first pass, row 3: `limbs[4] += limbs[7] · D₁ + carry`. -/
private theorem red512_l0l0_row3_spec (i : Usize) (u : Uint2)
    (iter : core.ops.range.Range Usize) (limbs : Aeneas.Std.Array Limb 8#usize)
    (carry : Limb) (row : Usize)
    (m0 m1 m2 m3 m4 m5 m6 m7 e0 e1 : Limb)
    (hlimbs : limbs.val = [m0, m1, m2, m3, m4, m5, m6, m7]) (huval : u.val = [e0, e1])
    (hi : i.val = 4) (hrow : row.val = 3)
    (hs : iter.start.val = 1) (he : iter.«end».val = 2) :
    field.verified.red.red512_loop0_loop0 i u iter limbs carry row ⦃ out c' =>
      ∃ s, out.val = [m0, m1, m2, m3, s, m5, m6, m7] ∧
        s.val + 2^64 * c'.val = m4.val + m7.val * e1.val + carry.val ⦄ := by
  unfold field.verified.red.red512_loop0_loop0
  apply loop_step
  unfold field.verified.red.red512_loop0_loop0.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨i2, hi2⟩
  step as ⟨l, hl⟩
  step as ⟨i3, hi3⟩
  step as ⟨l1, hl1⟩
  step as ⟨ua, hua⟩
  step as ⟨l2, hl2⟩
  step as ⟨l3, c1, hmac⟩
  step as ⟨i4, hi4⟩
  step as ⟨a1, ha1⟩
  simp only [hlimbs, hi2, hs, hrow] at hl
  simp at hl
  simp only [hlimbs, hi3, hi, hrow] at hl1
  simp at hl1
  simp only [hua, huval, hs] at hl2
  simp at hl2
  have ha1val : a1.val = [m0, m1, m2, m3, l3, m5, m6, m7] := by
    rw [ha1, Array.set_val_eq, hlimbs, hi4, hs, hrow]
    rfl
  -- exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hi2'⟩
  simp only [ho2]
  refine spec_ok_of ⟨l3, ha1val, ?_⟩
  rw [hl, hl1, hl2] at hmac
  omega

/-- First mac pass of `red512` (rows 2 and 3): folds `limbs[6..8]` down by
    `D = 2^256 - 2p`, 128 bits lower, saving the row carries in `carries[4..6]`. -/
private theorem red512_loop0_spec (l : Limb) (i i1 : Usize)
    (iter : core.ops.range.Range Usize) (limbs : Aeneas.Std.Array Limb 8#usize)
    (carries : Aeneas.Std.Array Limb 6#usize)
    (m0 m1 m2 m3 m4 m5 m6 m7 c0 c1 c2 c3 c4 c5 : Limb)
    (hl : l.val = 0) (hi : i.val = 4) (hi1 : i1.val = 2)
    (hs : iter.start.val = 2) (he : iter.«end».val = 4)
    (hlimbs : limbs.val = [m0, m1, m2, m3, m4, m5, m6, m7])
    (hcarr : carries.val = [c0, c1, c2, c3, c4, c5]) :
    field.verified.red.red512_loop0 l i i1 iter limbs carries ⦃ limbs' carries' =>
      ∃ t2 t3 t4 u4 u5, limbs'.val = [m0, m1, t2, t3, t4, m5, m6, m7]
        ∧ carries'.val = [c0, c1, c2, c3, u4, u5]
        ∧ t2.val + 2^64 * t3.val + 2^128 * t4.val + 2^128 * u4.val + 2^192 * u5.val
            = m2.val + 2^64 * m3.val + 2^128 * m4.val
              + m6.val * 933908882631967066 + 2^64 * (m6.val * 1267041765516122576)
              + 2^64 * (m7.val * 933908882631967066)
              + 2^128 * (m7.val * 1267041765516122576) ⦄ := by
  unfold field.verified.red.red512_loop0
  -- row 2
  apply loop_step
  unfold field.verified.red.red512_loop0.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨l1, hl1⟩
  step as ⟨i3, hi3⟩
  step with TWO_M255D_limbs_spec as ⟨e0, e1, u2, huval, he0, he1x⟩
  step as ⟨l2, hl2⟩
  step as ⟨ua, hua⟩
  step as ⟨l3, hl3⟩
  step as ⟨l4, cy, hmac⟩
  step as ⟨a1, ha1⟩
  simp only [hlimbs, hs] at hl1
  simp at hl1
  simp only [hlimbs, hi3, hi, hs] at hl2
  simp at hl2
  simp only [hua, huval] at hl3
  simp at hl3
  have ha1val : a1.val = [m0, m1, l4, m3, m4, m5, m6, m7] := by
    rw [ha1, Array.set_val_eq, hlimbs, hs]
    rfl
  apply Aeneas.Std.WP.spec_bind
    (red512_l0l0_row2_spec i u2 _ a1 cy _ m0 m1 l4 m3 m4 m5 m6 m7 e0 e1
      ha1val huval hi hs (by simp) hi1)
  intro ⟨limbs1, cyr2⟩ ⟨y3, hlimbs1, heqn2⟩
  step as ⟨i4, hi4⟩
  step as ⟨carr1, hcarr1⟩
  have hcarr1val : carr1.val = [c0, c1, c2, c3, cyr2, c5] := by
    rw [hcarr1, Array.set_val_eq, hcarr, hi4, hs, hi1]
    rfl
  -- row 3
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨l1', hl1'⟩
  step as ⟨i3', hi3'⟩
  step with TWO_M255D_limbs_spec as ⟨e0', e1', u2', huval', he0', he1x'⟩
  step as ⟨l2', hl2'⟩
  step as ⟨ua', hua'⟩
  step as ⟨l3', hl3'⟩
  step as ⟨l4', cy', hmac'⟩
  step as ⟨a1', ha1'⟩
  simp only [hlimbs1, hs1, hs] at hl1'
  simp at hl1'
  simp only [hlimbs1, hi3', hi, hs1, hs] at hl2'
  simp at hl2'
  simp only [hua', huval'] at hl3'
  simp at hl3'
  have ha1val' : a1'.val = [m0, m1, l4, l4', m4, m5, m6, m7] := by
    rw [ha1', Array.set_val_eq, hlimbs1, hs1, hs]
    rfl
  apply Aeneas.Std.WP.spec_bind
    (red512_l0l0_row3_spec i u2' _ a1' cy' _ m0 m1 l4 l4' m4 m5 m6 m7 e0' e1'
      ha1val' huval' hi (by rw [hs1, hs]) (by simp) hi1)
  intro ⟨limbs2, cyr3⟩ ⟨y4, hlimbs2, heqn3⟩
  step as ⟨i4', hi4'⟩
  step as ⟨carr2, hcarr2⟩
  have hcarr2val : carr2.val = [c0, c1, c2, c3, cyr2, cyr3] := by
    rw [hcarr2, Array.set_val_eq, hcarr1val, hi4', hs1, hs, hi1]
    rfl
  -- exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hi5⟩
  simp only [ho3]
  refine spec_ok_of ⟨l4, l4', y4, cyr2, cyr3, hlimbs2, hcarr2val, ?_⟩
  rw [hl1, hl2, hl3] at hmac
  rw [hl1', hl2', hl3'] at hmac'
  rw [hl, he0] at hmac
  rw [hl, he0'] at hmac'
  rw [he1x] at heqn2
  rw [he1x'] at heqn3
  omega

/-- Nested mac loop of the second pass, row 0: `limbs[1] += limbs[4] · D₁ + carry`. -/
private theorem red512_l4l0_row0_spec (i : Usize) (u : Uint2)
    (iter : core.ops.range.Range Usize) (limbs : Aeneas.Std.Array Limb 8#usize)
    (carry : Limb) (row : Usize)
    (m0 m1 m2 m3 m4 m5 m6 m7 e0 e1 : Limb)
    (hlimbs : limbs.val = [m0, m1, m2, m3, m4, m5, m6, m7]) (huval : u.val = [e0, e1])
    (hi : i.val = 4) (hrow : row.val = 0)
    (hs : iter.start.val = 1) (he : iter.«end».val = 2) :
    field.verified.red.red512_loop4_loop0 i u iter limbs carry row ⦃ out c' =>
      ∃ s, out.val = [m0, s, m2, m3, m4, m5, m6, m7] ∧
        s.val + 2^64 * c'.val = m1.val + m4.val * e1.val + carry.val ⦄ := by
  unfold field.verified.red.red512_loop4_loop0
  apply loop_step
  unfold field.verified.red.red512_loop4_loop0.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨i2, hi2⟩
  step as ⟨l, hl⟩
  step as ⟨i3, hi3⟩
  step as ⟨l1, hl1⟩
  step as ⟨ua, hua⟩
  step as ⟨l2, hl2⟩
  step as ⟨l3, c1, hmac⟩
  step as ⟨i4, hi4⟩
  step as ⟨a1, ha1⟩
  simp only [hlimbs, hi2, hs, hrow] at hl
  simp at hl
  simp only [hlimbs, hi3, hi, hrow] at hl1
  simp at hl1
  simp only [hua, huval, hs] at hl2
  simp at hl2
  have ha1val : a1.val = [m0, l3, m2, m3, m4, m5, m6, m7] := by
    rw [ha1, Array.set_val_eq, hlimbs, hi4, hs, hrow]
    rfl
  -- exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hi2'⟩
  simp only [ho2]
  refine spec_ok_of ⟨l3, ha1val, ?_⟩
  rw [hl, hl1, hl2] at hmac
  omega

/-- Nested mac loop of the second pass, row 1: `limbs[2] += limbs[5] · D₁ + carry`. -/
private theorem red512_l4l0_row1_spec (i : Usize) (u : Uint2)
    (iter : core.ops.range.Range Usize) (limbs : Aeneas.Std.Array Limb 8#usize)
    (carry : Limb) (row : Usize)
    (m0 m1 m2 m3 m4 m5 m6 m7 e0 e1 : Limb)
    (hlimbs : limbs.val = [m0, m1, m2, m3, m4, m5, m6, m7]) (huval : u.val = [e0, e1])
    (hi : i.val = 4) (hrow : row.val = 1)
    (hs : iter.start.val = 1) (he : iter.«end».val = 2) :
    field.verified.red.red512_loop4_loop0 i u iter limbs carry row ⦃ out c' =>
      ∃ s, out.val = [m0, m1, s, m3, m4, m5, m6, m7] ∧
        s.val + 2^64 * c'.val = m2.val + m5.val * e1.val + carry.val ⦄ := by
  unfold field.verified.red.red512_loop4_loop0
  apply loop_step
  unfold field.verified.red.red512_loop4_loop0.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨i2, hi2⟩
  step as ⟨l, hl⟩
  step as ⟨i3, hi3⟩
  step as ⟨l1, hl1⟩
  step as ⟨ua, hua⟩
  step as ⟨l2, hl2⟩
  step as ⟨l3, c1, hmac⟩
  step as ⟨i4, hi4⟩
  step as ⟨a1, ha1⟩
  simp only [hlimbs, hi2, hs, hrow] at hl
  simp at hl
  simp only [hlimbs, hi3, hi, hrow] at hl1
  simp at hl1
  simp only [hua, huval, hs] at hl2
  simp at hl2
  have ha1val : a1.val = [m0, m1, l3, m3, m4, m5, m6, m7] := by
    rw [ha1, Array.set_val_eq, hlimbs, hi4, hs, hrow]
    rfl
  -- exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hi2'⟩
  simp only [ho2]
  refine spec_ok_of ⟨l3, ha1val, ?_⟩
  rw [hl, hl1, hl2] at hmac
  omega

/-- Second mac pass of `red512` (rows 0 and 1): folds `limbs[4..6]` down by
    `D`, 256 bits lower, saving the row carries in `carries[2..4]`. -/
private theorem red512_loop4_spec (l : Limb) (i i1 : Usize)
    (iter : core.ops.range.Range Usize) (limbs : Aeneas.Std.Array Limb 8#usize)
    (carries : Aeneas.Std.Array Limb 6#usize) (cin : Limb)
    (m0 m1 m2 m3 m4 m5 m6 m7 c0 c1 c2 c3 c4 c5 : Limb)
    (hl : l.val = 0) (hi : i.val = 4) (hi1 : i1.val = 2)
    (hs : iter.start.val = 0) (he : iter.«end».val = 2)
    (hlimbs : limbs.val = [m0, m1, m2, m3, m4, m5, m6, m7])
    (hcarr : carries.val = [c0, c1, c2, c3, c4, c5]) :
    field.verified.red.red512_loop4 l i i1 iter limbs carries cin ⦃ limbs' carries' =>
      ∃ w0 w1 w2 u2 u3, limbs'.val = [w0, w1, w2, m3, m4, m5, m6, m7]
        ∧ carries'.val = [c0, c1, u2, u3, c4, c5]
        ∧ w0.val + 2^64 * w1.val + 2^128 * w2.val + 2^128 * u2.val + 2^192 * u3.val
            = m0.val + 2^64 * m1.val + 2^128 * m2.val
              + m4.val * 933908882631967066 + 2^64 * (m4.val * 1267041765516122576)
              + 2^64 * (m5.val * 933908882631967066)
              + 2^128 * (m5.val * 1267041765516122576) ⦄ := by
  unfold field.verified.red.red512_loop4
  -- row 0
  apply loop_step
  unfold field.verified.red.red512_loop4.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨l1, hl1⟩
  step as ⟨i3, hi3⟩
  step with TWO_M255D_limbs_spec as ⟨e0, e1, u2, huval, he0, he1x⟩
  step as ⟨l2, hl2⟩
  step as ⟨ua, hua⟩
  step as ⟨l3, hl3⟩
  step as ⟨l4, cy, hmac⟩
  step as ⟨a1, ha1⟩
  simp only [hlimbs, hs] at hl1
  simp at hl1
  simp only [hlimbs, hi3, hi, hs] at hl2
  simp at hl2
  simp only [hua, huval] at hl3
  simp at hl3
  have ha1val : a1.val = [l4, m1, m2, m3, m4, m5, m6, m7] := by
    rw [ha1, Array.set_val_eq, hlimbs, hs]
    rfl
  apply Aeneas.Std.WP.spec_bind
    (red512_l4l0_row0_spec i u2 _ a1 cy _ l4 m1 m2 m3 m4 m5 m6 m7 e0 e1
      ha1val huval hi hs (by simp) hi1)
  intro ⟨limbs1, cyr0⟩ ⟨y1, hlimbs1, heqn0⟩
  step as ⟨i4, hi4⟩
  step as ⟨carr1, hcarr1⟩
  have hcarr1val : carr1.val = [c0, c1, cyr0, c3, c4, c5] := by
    rw [hcarr1, Array.set_val_eq, hcarr, hi4, hs, hi1]
    rfl
  -- row 1
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨l1', hl1'⟩
  step as ⟨i3', hi3'⟩
  step with TWO_M255D_limbs_spec as ⟨e0', e1', u2', huval', he0', he1x'⟩
  step as ⟨l2', hl2'⟩
  step as ⟨ua', hua'⟩
  step as ⟨l3', hl3'⟩
  step as ⟨l4', cy', hmac'⟩
  step as ⟨a1', ha1'⟩
  simp only [hlimbs1, hs1, hs] at hl1'
  simp at hl1'
  simp only [hlimbs1, hi3', hi, hs1, hs] at hl2'
  simp at hl2'
  simp only [hua', huval'] at hl3'
  simp at hl3'
  have ha1val' : a1'.val = [l4, l4', m2, m3, m4, m5, m6, m7] := by
    rw [ha1', Array.set_val_eq, hlimbs1, hs1, hs]
    rfl
  apply Aeneas.Std.WP.spec_bind
    (red512_l4l0_row1_spec i u2' _ a1' cy' _ l4 l4' m2 m3 m4 m5 m6 m7 e0' e1'
      ha1val' huval' hi (by rw [hs1, hs]) (by simp) hi1)
  intro ⟨limbs2, cyr1⟩ ⟨y2, hlimbs2, heqn1⟩
  step as ⟨i4', hi4'⟩
  step as ⟨carr2, hcarr2⟩
  have hcarr2val : carr2.val = [c0, c1, cyr0, cyr1, c4, c5] := by
    rw [hcarr2, Array.set_val_eq, hcarr1val, hi4', hs1, hs, hi1]
    rfl
  -- exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hi5⟩
  simp only [ho3]
  refine spec_ok_of ⟨l4, l4', y2, cyr0, cyr1, hlimbs2, hcarr2val, ?_⟩
  rw [hl1, hl2, hl3] at hmac
  rw [hl1', hl2', hl3'] at hmac'
  rw [hl, he0] at hmac
  rw [hl, he0'] at hmac'
  rw [he1x] at heqn0
  rw [he1x'] at heqn1
  omega

/-- First carries fold of `red512`: adds `carries[4..6]` into `limbs[4..6]`. -/
private theorem red512_loop1_spec (iter : core.ops.range.Range Usize)
    (limbs : Aeneas.Std.Array Limb 8#usize) (carries : Aeneas.Std.Array Limb 6#usize)
    (cin : Limb)
    (m0 m1 m2 m3 m4 m5 m6 m7 c0 c1 c2 c3 c4 c5 : Limb)
    (hs : iter.start.val = 4) (he : iter.«end».val = 6)
    (hlimbs : limbs.val = [m0, m1, m2, m3, m4, m5, m6, m7])
    (hcarr : carries.val = [c0, c1, c2, c3, c4, c5])
    (hcin : cin.val = 0) :
    field.verified.red.red512_loop1 iter limbs carries cin ⦃ limbs' c' =>
      ∃ v4 v5, limbs'.val = [m0, m1, m2, m3, v4, v5, m6, m7] ∧ c'.val ≤ 1 ∧
        v4.val + 2^64 * v5.val + 2^128 * c'.val
          = m4.val + c4.val + 2^64 * (m5.val + c5.val) ⦄ := by
  unfold field.verified.red.red512_loop1
  -- j = 4
  apply loop_step
  unfold field.verified.red.red512_loop1.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨l, hl⟩
  step as ⟨l1, hl1⟩
  step with (awbo_spec l l1 cin (by omega)) as ⟨v4, k1, heq1, hk1⟩
  step as ⟨a1, ha1⟩
  simp only [hlimbs, hs] at hl
  simp at hl
  simp only [hcarr, hs] at hl1
  simp at hl1
  have ha1val : a1.val = [m0, m1, m2, m3, v4, m5, m6, m7] := by
    rw [ha1, Array.set_val_eq, hlimbs, hs]
    rfl
  -- j = 5
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨l', hl'⟩
  step as ⟨l1', hl1'⟩
  step with (awbo_spec l' l1' k1 hk1) as ⟨v5, k2, heq2, hk2⟩
  step as ⟨a2, ha2⟩
  simp only [ha1val, hs1, hs] at hl'
  simp at hl'
  simp only [hcarr, hs1, hs] at hl1'
  simp at hl1'
  have ha2val : a2.val = [m0, m1, m2, m3, v4, v5, m6, m7] := by
    rw [ha2, Array.set_val_eq, ha1val, hs1, hs]
    rfl
  -- exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hi3⟩
  simp only [ho3]
  refine spec_ok_of ⟨v4, v5, ha2val, hk2, ?_⟩
  rw [hl, hl1, hcin] at heq1
  rw [hl', hl1'] at heq2
  omega

/-- Second carries fold of `red512`: adds `carries[2..4]` into `limbs[2..4]`. -/
private theorem red512_loop5_spec (iter : core.ops.range.Range Usize)
    (limbs : Aeneas.Std.Array Limb 8#usize) (carries : Aeneas.Std.Array Limb 6#usize)
    (cin : Limb)
    (m0 m1 m2 m3 m4 m5 m6 m7 c0 c1 c2 c3 c4 c5 : Limb)
    (hs : iter.start.val = 2) (he : iter.«end».val = 4)
    (hlimbs : limbs.val = [m0, m1, m2, m3, m4, m5, m6, m7])
    (hcarr : carries.val = [c0, c1, c2, c3, c4, c5])
    (hcin : cin.val = 0) :
    field.verified.red.red512_loop5 iter limbs carries cin ⦃ limbs' c' =>
      ∃ v2 v3, limbs'.val = [m0, m1, v2, v3, m4, m5, m6, m7] ∧ c'.val ≤ 1 ∧
        v2.val + 2^64 * v3.val + 2^128 * c'.val
          = m2.val + c2.val + 2^64 * (m3.val + c3.val) ⦄ := by
  unfold field.verified.red.red512_loop5
  -- j = 2
  apply loop_step
  unfold field.verified.red.red512_loop5.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨l, hl⟩
  step as ⟨l1, hl1⟩
  step with (awbo_spec l l1 cin (by omega)) as ⟨v2, k1, heq1, hk1⟩
  step as ⟨a1, ha1⟩
  simp only [hlimbs, hs] at hl
  simp at hl
  simp only [hcarr, hs] at hl1
  simp at hl1
  have ha1val : a1.val = [m0, m1, v2, m3, m4, m5, m6, m7] := by
    rw [ha1, Array.set_val_eq, hlimbs, hs]
    rfl
  -- j = 3
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨l', hl'⟩
  step as ⟨l1', hl1'⟩
  step with (awbo_spec l' l1' k1 hk1) as ⟨v3, k2, heq2, hk2⟩
  step as ⟨a2, ha2⟩
  simp only [ha1val, hs1, hs] at hl'
  simp at hl'
  simp only [hcarr, hs1, hs] at hl1'
  simp at hl1'
  have ha2val : a2.val = [m0, m1, v2, v3, m4, m5, m6, m7] := by
    rw [ha2, Array.set_val_eq, ha1val, hs1, hs]
    rfl
  -- exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hi3⟩
  simp only [ho3]
  refine spec_ok_of ⟨v2, v3, ha2val, hk2, ?_⟩
  rw [hl, hl1, hcin] at heq1
  rw [hl', hl1'] at heq2
  omega

/-- 384th-bit reduction loop of `red512`: masked addition of `D` at limbs 2-3. -/
private theorem red512_loop2_spec (i : Usize) (iter : core.ops.range.Range Usize)
    (limbs : Aeneas.Std.Array Limb 8#usize) (mask cin : Limb)
    (m0 m1 m2 m3 m4 m5 m6 m7 : Limb)
    (hi : i.val = 2) (hs : iter.start.val = 0) (he : iter.«end».val = 2)
    (hlimbs : limbs.val = [m0, m1, m2, m3, m4, m5, m6, m7])
    (hcin : cin.val = 0) :
    field.verified.red.red512_loop2 i iter limbs mask cin ⦃ limbs' c' =>
      ∃ w2 w3, limbs'.val = [m0, m1, w2, w3, m4, m5, m6, m7] ∧ c'.val ≤ 1 ∧
        w2.val + 2^64 * w3.val + 2^128 * c'.val
          = m2.val + 2^64 * m3.val + (mask.val &&& 933908882631967066)
            + 2^64 * (mask.val &&& 1267041765516122576) ⦄ := by
  unfold field.verified.red.red512_loop2
  -- j = 0
  apply loop_step
  unfold field.verified.red.red512_loop2.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨i1, hi1⟩
  step with TWO_M255D_limbs_spec as ⟨e0, e1, u2, huval, he0, he1x⟩
  step as ⟨l, hl⟩
  step as ⟨ua, hua⟩
  step as ⟨l1, hl1⟩
  step as ⟨l2, hl2⟩
  step with (awbo_spec l l2 cin (by omega)) as ⟨w2, k1, heq1, hk1⟩
  step as ⟨i2, hi2⟩
  step as ⟨a1, ha1⟩
  simp only [hlimbs, hi1, hi, hs] at hl
  simp at hl
  simp only [hua, huval, hs] at hl1
  simp at hl1
  have ha1val : a1.val = [m0, m1, w2, m3, m4, m5, m6, m7] := by
    rw [ha1, Array.set_val_eq, hlimbs, hi2, hi, hs]
    rfl
  -- j = 1
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨i1', hi1'⟩
  step with TWO_M255D_limbs_spec as ⟨e0', e1', u2', huval', he0', he1x'⟩
  step as ⟨l', hl'⟩
  step as ⟨ua', hua'⟩
  step as ⟨l1', hl1'⟩
  step as ⟨l2', hl2'⟩
  step with (awbo_spec l' l2' k1 hk1) as ⟨w3, k2, heq2, hk2⟩
  step as ⟨i2', hi2'⟩
  step as ⟨a2, ha2⟩
  simp only [ha1val, hi1', hi, hs1, hs] at hl'
  simp at hl'
  simp only [hua', huval', hs1, hs] at hl1'
  simp at hl1'
  have ha2val : a2.val = [m0, m1, w2, w3, m4, m5, m6, m7] := by
    rw [ha2, Array.set_val_eq, ha1val, hi2', hi, hs1, hs]
    rfl
  -- exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hi3⟩
  simp only [ho3]
  refine spec_ok_of ⟨w2, w3, ha2val, hk2, ?_⟩
  rw [hl, hl2, hl1, he0, hcin] at heq1
  rw [hl', hl2', hl1', he1x'] at heq2
  omega

/-- 256th-bit reduction loop of `red512`: masked addition of `D` at limbs 0-1. -/
private theorem red512_loop6_spec (iter : core.ops.range.Range Usize)
    (limbs : Aeneas.Std.Array Limb 8#usize) (mask cin : Limb)
    (m0 m1 m2 m3 m4 m5 m6 m7 : Limb)
    (hs : iter.start.val = 0) (he : iter.«end».val = 2)
    (hlimbs : limbs.val = [m0, m1, m2, m3, m4, m5, m6, m7])
    (hcin : cin.val = 0) :
    field.verified.red.red512_loop6 iter limbs mask cin ⦃ limbs' c' =>
      ∃ w0 w1, limbs'.val = [w0, w1, m2, m3, m4, m5, m6, m7] ∧ c'.val ≤ 1 ∧
        w0.val + 2^64 * w1.val + 2^128 * c'.val
          = m0.val + 2^64 * m1.val + (mask.val &&& 933908882631967066)
            + 2^64 * (mask.val &&& 1267041765516122576) ⦄ := by
  unfold field.verified.red.red512_loop6
  -- i = 0
  apply loop_step
  unfold field.verified.red.red512_loop6.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step with TWO_M255D_limbs_spec as ⟨e0, e1, u2, huval, he0, he1x⟩
  step as ⟨l, hl⟩
  step as ⟨ua, hua⟩
  step as ⟨l1, hl1⟩
  step as ⟨l2, hl2⟩
  step with (awbo_spec l l2 cin (by omega)) as ⟨w0, k1, heq1, hk1⟩
  step as ⟨a1, ha1⟩
  simp only [hlimbs, hs] at hl
  simp at hl
  simp only [hua, huval, hs] at hl1
  simp at hl1
  have ha1val : a1.val = [w0, m1, m2, m3, m4, m5, m6, m7] := by
    rw [ha1, Array.set_val_eq, hlimbs, hs]
    rfl
  -- i = 1
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step with TWO_M255D_limbs_spec as ⟨e0', e1', u2', huval', he0', he1x'⟩
  step as ⟨l', hl'⟩
  step as ⟨ua', hua'⟩
  step as ⟨l1', hl1'⟩
  step as ⟨l2', hl2'⟩
  step with (awbo_spec l' l2' k1 hk1) as ⟨w1, k2, heq2, hk2⟩
  step as ⟨a2, ha2⟩
  simp only [ha1val, hs1, hs] at hl'
  simp at hl'
  simp only [hua', huval', hs1, hs] at hl1'
  simp at hl1'
  have ha2val : a2.val = [w0, w1, m2, m3, m4, m5, m6, m7] := by
    rw [ha2, Array.set_val_eq, ha1val, hs1, hs]
    rfl
  -- exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hi3⟩
  simp only [ho3]
  refine spec_ok_of ⟨w0, w1, ha2val, hk2, ?_⟩
  rw [hl, hl2, hl1, he0, hcin] at heq1
  rw [hl', hl2', hl1', he1x'] at heq2
  omega

/-- Carry-ripple loop after the 384th-bit reduction: adds the carry through
    limbs 4-5 (adding the constant zero limb `l`). -/
private theorem red512_loop3_spec (l : Limb) (i : Usize)
    (iter : core.ops.range.Range Usize) (limbs : Aeneas.Std.Array Limb 8#usize)
    (cin : Limb)
    (m0 m1 m2 m3 m4 m5 m6 m7 : Limb)
    (hl : l.val = 0) (hi : i.val = 2)
    (hs : iter.start.val = 2) (he : iter.«end».val = 4)
    (hlimbs : limbs.val = [m0, m1, m2, m3, m4, m5, m6, m7])
    (hcin : cin.val ≤ 1) :
    field.verified.red.red512_loop3 l i iter limbs cin ⦃ limbs' c' =>
      ∃ v4 v5, limbs'.val = [m0, m1, m2, m3, v4, v5, m6, m7] ∧ c'.val ≤ 1 ∧
        v4.val + 2^64 * v5.val + 2^128 * c'.val
          = m4.val + 2^64 * m5.val + cin.val ⦄ := by
  unfold field.verified.red.red512_loop3
  -- j = 2
  apply loop_step
  unfold field.verified.red.red512_loop3.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨i1, hi1⟩
  step as ⟨l1, hl1⟩
  step with (awbo_spec l1 l cin hcin) as ⟨v4, k1, heq1, hk1⟩
  step as ⟨i2, hi2⟩
  step as ⟨a1, ha1⟩
  simp only [hlimbs, hi1, hi, hs] at hl1
  simp at hl1
  have ha1val : a1.val = [m0, m1, m2, m3, v4, m5, m6, m7] := by
    rw [ha1, Array.set_val_eq, hlimbs, hi2, hi, hs]
    rfl
  -- j = 3
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨i1', hi1'⟩
  step as ⟨l1', hl1'⟩
  step with (awbo_spec l1' l k1 hk1) as ⟨v5, k2, heq2, hk2⟩
  step as ⟨i2', hi2'⟩
  step as ⟨a2, ha2⟩
  simp only [ha1val, hi1', hi, hs1, hs] at hl1'
  simp at hl1'
  have ha2val : a2.val = [m0, m1, m2, m3, v4, v5, m6, m7] := by
    rw [ha2, Array.set_val_eq, ha1val, hi2', hi, hs1, hs]
    rfl
  -- exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hi3⟩
  simp only [ho3]
  refine spec_ok_of ⟨v4, v5, ha2val, hk2, ?_⟩
  rw [hl1, hl] at heq1
  rw [hl1', hl] at heq2
  omega

/-- Final carry-ripple loop of `red512`: propagates the 256th-bit reduction
    carry through limbs 2-3 with plain `overflowing_add`s. -/
private theorem red512_loop7_spec (iter : core.ops.range.Range Usize)
    (limbs : Aeneas.Std.Array Limb 8#usize) (cin : Limb)
    (m0 m1 m2 m3 m4 m5 m6 m7 : Limb)
    (hs : iter.start.val = 2) (he : iter.«end».val = 4)
    (hlimbs : limbs.val = [m0, m1, m2, m3, m4, m5, m6, m7])
    (hcin : cin.val ≤ 1) :
    field.verified.red.red512_loop7 iter limbs cin ⦃ limbs' =>
      ∃ v2 v3 cend, limbs'.val = [m0, m1, v2, v3, m4, m5, m6, m7] ∧ cend ≤ 1 ∧
        v2.val + 2^64 * v3.val + 2^128 * cend
          = m2.val + 2^64 * m3.val + cin.val ⦄ := by
  unfold field.verified.red.red512_loop7
  -- i = 2
  apply loop_step
  unfold field.verified.red.red512_loop7.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨l, hl⟩
  step as ⟨v2, cb, cv1, hcv1le, hcv1, hlink1⟩
  step as ⟨i1, hi1⟩
  step as ⟨a1, ha1⟩
  simp only [hlimbs, hs] at hl
  simp at hl
  have hi1v : i1.val = cv1 := by rw [hi1]; exact hlink1
  have ha1val : a1.val = [m0, m1, v2, m3, m4, m5, m6, m7] := by
    rw [ha1, Array.set_val_eq, hlimbs, hs]
    rfl
  -- i = 3
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨l', hl'⟩
  step as ⟨v3, cb2, cv2, hcv2le, hcv2, hlink2⟩
  step as ⟨i1', hi1'⟩
  step as ⟨a2, ha2⟩
  simp only [ha1val, hs1, hs] at hl'
  simp at hl'
  have hi1v' : i1'.val = cv2 := by rw [hi1']; exact hlink2
  have ha2val : a2.val = [m0, m1, v2, v3, m4, m5, m6, m7] := by
    rw [ha2, Array.set_val_eq, ha1val, hs1, hs]
    rfl
  -- exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hi3⟩
  simp only [ho3]
  refine spec_ok_of ⟨v2, v3, cv2, ha2val, hcv2le, ?_⟩
  rw [hl] at hcv1
  rw [hl', hi1v] at hcv2
  omega

/-- The 256th-bit carry dropped at the very end of `red512` is zero
    (pass-2 subsystem only; standalone so that `omega` sees a minimal context). -/
private theorem red512_cend_zero (x0 x1 w2 w3 r4 r5 : ℕ)
    (w0 w1 w2n u2 u3 v2 v3 z0 z1 z2 z3 : ℕ) (cyL5 k6 cend : ℕ)
    (hx0 : x0 < 2^64) (hx1 : x1 < 2^64)
    (hw2 : w2 < 2^64) (hw3 : w3 < 2^64)
    (hr4 : r4 < 2^64) (hr5 : r5 < 2^64)
    (hw0 : w0 < 2^64) (hw1 : w1 < 2^64) (hw2n : w2n < 2^64)
    (hu2 : u2 < 2^64) (hu3 : u3 < 2^64)
    (hv2 : v2 < 2^64) (hv3 : v3 < 2^64)
    (hz0 : z0 < 2^64) (hz1 : z1 < 2^64) (hz2 : z2 < 2^64) (hz3 : z3 < 2^64)
    (hcyL5 : cyL5 ≤ 1) (hk6 : k6 ≤ 1) (hcend : cend ≤ 1)
    (heq4 : w0 + 2^64 * w1 + 2^128 * w2n + 2^128 * u2 + 2^192 * u3
        = x0 + 2^64 * x1 + 2^128 * w2
          + r4 * 933908882631967066 + 2^64 * (r4 * 1267041765516122576)
          + 2^64 * (r5 * 933908882631967066) + 2^128 * (r5 * 1267041765516122576))
    (heq5 : v2 + 2^64 * v3 + 2^128 * cyL5 = w2n + u2 + 2^64 * (w3 + u3))
    (heq6 : z0 + 2^64 * z1 + 2^128 * k6
        = w0 + 2^64 * w1 + cyL5 * 933908882631967066
          + 2^64 * (cyL5 * 1267041765516122576))
    (heq7 : z2 + 2^64 * z3 + 2^128 * cend = v2 + 2^64 * v3 + k6) :
    cend = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcyL5 with h | h <;> omega

/-- The exact multiple-of-`p` identity between the 512-bit input value and the
    reduced output of `red512`'s folding phase (standalone for a minimal
    `omega` context). -/
private theorem red512_key_identity (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ)
    (t2 t3 t4 u4 u5 v4 v5 w2 w3 r4 r5 : ℕ)
    (w0 w1 w2n u2 u3 v2 v3 z0 z1 z2 z3 : ℕ)
    (cyL1 k2 cy3 cyL5 k6 cend : ℕ)
    (hx0 : x0 < 2^64) (hx1 : x1 < 2^64) (hx2 : x2 < 2^64) (hx3 : x3 < 2^64)
    (hx4 : x4 < 2^64) (hx5 : x5 < 2^64) (hx6 : x6 < 2^64) (hx7 : x7 < 2^64)
    (ht2 : t2 < 2^64) (ht3 : t3 < 2^64) (ht4 : t4 < 2^64)
    (hu4 : u4 < 2^64) (hu5 : u5 < 2^64)
    (hv4 : v4 < 2^64) (hv5 : v5 < 2^64)
    (hw2 : w2 < 2^64) (hw3 : w3 < 2^64)
    (hr4 : r4 < 2^64) (hr5 : r5 < 2^64)
    (hw0 : w0 < 2^64) (hw1 : w1 < 2^64) (hw2n : w2n < 2^64)
    (hu2 : u2 < 2^64) (hu3 : u3 < 2^64)
    (hv2 : v2 < 2^64) (hv3 : v3 < 2^64)
    (hz0 : z0 < 2^64) (hz1 : z1 < 2^64) (hz2 : z2 < 2^64) (hz3 : z3 < 2^64)
    (hcyL1 : cyL1 ≤ 1) (hk2 : k2 ≤ 1) (hcy3 : cy3 ≤ 1) (hcyL5 : cyL5 ≤ 1)
    (hk6 : k6 ≤ 1) (hcend : cend ≤ 1)
    (heq0 : t2 + 2^64 * t3 + 2^128 * t4 + 2^128 * u4 + 2^192 * u5
        = x2 + 2^64 * x3 + 2^128 * x4
          + x6 * 933908882631967066 + 2^64 * (x6 * 1267041765516122576)
          + 2^64 * (x7 * 933908882631967066) + 2^128 * (x7 * 1267041765516122576))
    (heq1 : v4 + 2^64 * v5 + 2^128 * cyL1 = t4 + u4 + 2^64 * (x5 + u5))
    (heq2 : w2 + 2^64 * w3 + 2^128 * k2
        = t2 + 2^64 * t3 + cyL1 * 933908882631967066
          + 2^64 * (cyL1 * 1267041765516122576))
    (heq3 : r4 + 2^64 * r5 + 2^128 * cy3 = v4 + 2^64 * v5 + k2)
    (heq4 : w0 + 2^64 * w1 + 2^128 * w2n + 2^128 * u2 + 2^192 * u3
        = x0 + 2^64 * x1 + 2^128 * w2
          + r4 * 933908882631967066 + 2^64 * (r4 * 1267041765516122576)
          + 2^64 * (r5 * 933908882631967066) + 2^128 * (r5 * 1267041765516122576))
    (heq5 : v2 + 2^64 * v3 + 2^128 * cyL5 = w2n + u2 + 2^64 * (w3 + u3))
    (heq6 : z0 + 2^64 * z1 + 2^128 * k6
        = w0 + 2^64 * w1 + cyL5 * 933908882631967066
          + 2^64 * (cyL5 * 1267041765516122576))
    (heq7 : z2 + 2^64 * z3 + 2^128 * cend = v2 + 2^64 * v3 + k6)
    (hcy3z : cy3 = 0) (hcendz : cend = 0) :
    x0 + 2^64 * x1 + 2^128 * x2 + 2^192 * x3
      + 2^256 * (x4 + 2^64 * x5 + 2^128 * x6 + 2^192 * x7)
      = (z0 + 2^64 * z1 + 2^128 * z2 + 2^192 * z3)
        + 57896044618658097711785492504343953926623305935230693509004809574567321395027
          * (2 * (2^128 * x6 + 2^192 * x7 + 2^128 * cyL1
                  + r4 + 2^64 * r5 + cyL5)) := by
  omega

/-- A `wrapping_neg`-of-carry mask ANDed with a small constant equals
    `carry · constant` — the omega-friendly form of the conditional add. -/
private theorem mask_and_carry (cv m x : ℕ) (hc : cv ≤ 1)
    (hm : m = (2^64 - cv) % 2^64) (hx : x < 2^64) : m &&& x = cv * x := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h <;> subst h
  · have hm0 : m = 0 := by omega
    subst hm0
    simp
  · have hm1 : m = 2^64 - 1 := by omega
    subst hm1
    rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx, Nat.one_mul]

/-- `red512` computes the canonical representative mod `p` of any 512-bit value
    (given as its two 256-bit halves). -/
private theorem red512_spec (lo hi : Uint4) :
    field.verified.red.red512 (lo, hi) ⦃ r =>
      r.toNat = (lo.toNat + 2^256 * hi.toNat) % p ⦄ := by
  have hp : p = 57896044618658097711785492504343953926623305935230693509004809574567321395027 := rfl
  obtain ⟨x0, x1, x2, x3, hloval⟩ := Uint4.exists_limbs lo
  obtain ⟨x4, x5, x6, x7, hhival⟩ := Uint4.exists_limbs hi
  have hlosum := toNat_limbs4 lo hloval
  have hhisum := toNat_limbs4 hi hhival
  have hx0 : x0.val < 2^64 := x0.hBounds
  have hx1 : x1.val < 2^64 := x1.hBounds
  have hx2 : x2.val < 2^64 := x2.hBounds
  have hx3 : x3.val < 2^64 := x3.hBounds
  have hx4 : x4.val < 2^64 := x4.hBounds
  have hx5 : x5.val < 2^64 := x5.hBounds
  have hx6 : x6.val < 2^64 := x6.hBounds
  have hx7 : x7.val < 2^64 := x7.hBounds
  unfold field.verified.red.red512
  step as ⟨l, hlz⟩
  step as ⟨i, hi4s⟩
  simp only [hi4s]
  step as ⟨s, back0, hsval, hslen, hback0⟩
  try simp only []
  step as ⟨a, haeq⟩
  step as ⟨s1, hs1v⟩
  have hs1val : s1.val = [x0, x1, x2, x3] := by
    rw [hs1v, haeq, hloval]
  have hsval' : s.val = [l, l, l, l] := by
    rw [hsval, Aeneas.Std.Array.repeat_val]
    simp [List.replicate, List.slice]
  apply Aeneas.Std.WP.spec_bind
    (core.slice.Slice.copy_from_slice.step_spec _ s s1 (by
      show s.val.length = s1.val.length
      rw [hsval', hs1val]
      rfl))

  intro s2 hs2
  try simp only []
  step as ⟨s3, back1, hs3val, hs3len, hback1⟩
  step as ⟨a1, ha1eq⟩
  step as ⟨s4, hs4v⟩
  have hs4val : s4.val = [x4, x5, x6, x7] := by
    rw [hs4v, ha1eq, hhival]
  have hlimbs1val : (back0 s2).val = [x0, x1, x2, x3, l, l, l, l] := by
    rw [hback0 s2, hs2, Aeneas.Std.Array.repeat_val, hs1val]
    simp [List.replicate, List.setSlice!]
  have hs3val' : s3.val = [l, l, l, l] := by
    rw [hs3val, hlimbs1val]
    simp
  apply Aeneas.Std.WP.spec_bind
    (core.slice.Slice.copy_from_slice.step_spec _ s3 s4 (by
      show s3.val.length = s4.val.length
      rw [hs3val', hs4val]
      rfl))
  intro s5 hs5
  try simp only []
  step as ⟨i1, hi2s⟩
  simp only [hi2s]
  have hlimbs2val : (back1 s5).val = [x0, x1, x2, x3, x4, x5, x6, x7] := by
    rw [hback1 s5, hs5, hlimbs1val, hs4val]
    simp [List.setSlice!]
  have hcarrval : (Aeneas.Std.Array.repeat 6#usize l).val = [l, l, l, l, l, l] := by
    rw [Aeneas.Std.Array.repeat_val]
    simp [List.replicate]
  -- pass 1 : fold limbs 6-7 down by D
  apply Aeneas.Std.WP.spec_bind
    (red512_loop0_spec l _ _ _ _ _ x0 x1 x2 x3 x4 x5 x6 x7 l l l l l l
      hlz (by simp) (by simp) (by simp) (by simp) hlimbs2val hcarrval)
  intro ⟨limbs3, carries1⟩ ⟨t2, t3, t4, u4, u5, hlimbs3, hcarr1, heq0⟩
  step as ⟨i2, hi2v⟩
  apply Aeneas.Std.WP.spec_bind
    (red512_loop1_spec _ _ _ _ x0 x1 t2 t3 t4 x5 x6 x7 l l l l u4 u5
      (by simp) (by omega) hlimbs3 hcarr1 hlz)
  intro ⟨limbs4, cyL1⟩ ⟨v4, v5, hlimbs4, hcyL1, heq1⟩
  step as ⟨m384, hm384⟩
  -- 384th-bit masked reduction
  apply Aeneas.Std.WP.spec_bind
    (red512_loop2_spec _ _ _ m384 _ x0 x1 t2 t3 v4 v5 x6 x7
      (by simp) (by simp) (by simp) hlimbs4 hlz)
  intro ⟨limbs5, k2⟩ ⟨w2, w3, hlimbs5, hk2, heq2⟩
  apply Aeneas.Std.WP.spec_bind
    (red512_loop3_spec l _ _ _ _ x0 x1 w2 w3 v4 v5 x6 x7
      hlz (by simp) (by simp) (by simp) hlimbs5 hk2)
  intro ⟨limbs6, cy3⟩ ⟨r4, r5, hlimbs6, hcy3, heq3⟩
  -- pass 2 : fold limbs 4-5 down by D
  apply Aeneas.Std.WP.spec_bind
    (red512_loop4_spec l _ _ _ _ _ _ x0 x1 w2 w3 r4 r5 x6 x7 l l l l u4 u5
      hlz (by simp) (by simp) (by simp) (by simp) hlimbs6 hcarr1)
  intro ⟨limbs7, carries2⟩ ⟨w0, w1, w2n, u2, u3, hlimbs7, hcarr2, heq4⟩
  apply Aeneas.Std.WP.spec_bind
    (red512_loop5_spec _ _ _ _ w0 w1 w2n w3 r4 r5 x6 x7 l l u2 u3 u4 u5
      (by simp) (by simp) hlimbs7 hcarr2 hlz)
  intro ⟨limbs8, cyL5⟩ ⟨v2, v3, hlimbs8, hcyL5, heq5⟩
  step as ⟨m256, hm256⟩
  -- 256th-bit masked reduction
  apply Aeneas.Std.WP.spec_bind
    (red512_loop6_spec _ _ m256 _ w0 w1 v2 v3 r4 r5 x6 x7
      (by simp) (by simp) hlimbs8 hlz)
  intro ⟨limbs9, k6⟩ ⟨z0, z1, hlimbs9, hk6, heq6⟩
  apply Aeneas.Std.WP.spec_bind
    (red512_loop7_spec _ _ _ z0 z1 v2 v3 r4 r5 x6 x7
      (by simp) (by simp) hlimbs9 hk6)
  intro limbs10 ⟨z2, z3, cend, hlimbs10, hcend, heq7⟩
  -- epilogue : copy the low four limbs out and reduce with red256
  step as ⟨res, hres⟩
  obtain ⟨q0, q1, q2, q3, hqval⟩ := Uint4.exists_limbs res
  step as ⟨a2, backr, ha2eq, hbackr⟩
  step as ⟨s6, backs, hs6val, hbacks⟩
  try simp only [Aeneas.Std.Array.index_SliceIndexRangeToUsizeSlice]
  apply Aeneas.Std.WP.spec_bind
    (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec _ limbs10.to_slice (by
      show (4#usize).val ≤ limbs10.to_slice.val.length
      rw [Aeneas.Std.Array.val_to_slice, hlimbs10]
      simp))
  intro s7 ⟨hs7val, hs7len⟩
  have hs7val' : s7.val = [z0, z1, z2, z3] := by
    rw [hs7val, Aeneas.Std.Array.val_to_slice, hlimbs10]
    simp [List.slice]
  have hs6val' : s6.val = [q0, q1, q2, q3] := by
    rw [hs6val, ha2eq, hqval]
  apply Aeneas.Std.WP.spec_bind
    (core.slice.Slice.copy_from_slice.step_spec _ s6 s7 (by
      show s6.val.length = s7.val.length
      rw [hs6val', hs7val']
      rfl))
  intro s8 hs8
  simp only [hbacks, hbackr]
  have hfinal : (Aeneas.Std.Array.from_slice a2 s8).val = [z0, z1, z2, z3] := by
    rw [Aeneas.Std.Array.from_slice_val _ _ (by
      rw [hs8, hs7val']
      simp [ha2eq])]
    rw [hs8, hs7val']
  -- masked-add link : the wrapping_neg masks are carry · D-limb
  have hM384_0 : m384.val &&& 933908882631967066 = cyL1.val * 933908882631967066 :=
    mask_and_carry cyL1.val m384.val _ hcyL1 hm384 (by norm_num)
  have hM384_1 : m384.val &&& 1267041765516122576 = cyL1.val * 1267041765516122576 :=
    mask_and_carry cyL1.val m384.val _ hcyL1 hm384 (by norm_num)
  have hM256_0 : m256.val &&& 933908882631967066 = cyL5.val * 933908882631967066 :=
    mask_and_carry cyL5.val m256.val _ hcyL5 hm256 (by norm_num)
  have hM256_1 : m256.val &&& 1267041765516122576 = cyL5.val * 1267041765516122576 :=
    mask_and_carry cyL5.val m256.val _ hcyL5 hm256 (by norm_num)
  rw [hM384_0, hM384_1] at heq2
  rw [hM256_0, hM256_1] at heq6
  -- limb bounds for the final omega
  have ht2 : t2.val < 2^64 := t2.hBounds
  have ht3 : t3.val < 2^64 := t3.hBounds
  have ht4 : t4.val < 2^64 := t4.hBounds
  have hu4 : u4.val < 2^64 := u4.hBounds
  have hu5 : u5.val < 2^64 := u5.hBounds
  have hv4 : v4.val < 2^64 := v4.hBounds
  have hv5 : v5.val < 2^64 := v5.hBounds
  have hw2 : w2.val < 2^64 := w2.hBounds
  have hw3 : w3.val < 2^64 := w3.hBounds
  have hr4 : r4.val < 2^64 := r4.hBounds
  have hr5 : r5.val < 2^64 := r5.hBounds
  have hw0 : w0.val < 2^64 := w0.hBounds
  have hw1 : w1.val < 2^64 := w1.hBounds
  have hw2n : w2n.val < 2^64 := w2n.hBounds
  have hu2 : u2.val < 2^64 := u2.hBounds
  have hu3 : u3.val < 2^64 := u3.hBounds
  have hv2 : v2.val < 2^64 := v2.hBounds
  have hv3 : v3.val < 2^64 := v3.hBounds
  have hz0 : z0.val < 2^64 := z0.hBounds
  have hz1 : z1.val < 2^64 := z1.hBounds
  have hz2 : z2.val < 2^64 := z2.hBounds
  have hz3 : z3.val < 2^64 := z3.hBounds
  apply Aeneas.Std.WP.spec_mono (red256_spec _)
  intro r hr
  rw [hr, toNat_limbs4 _ hfinal, hlosum, hhisum, hp]
  -- the carries dropped by the code (bit 384 after the masked add, bit 256 at
  -- the very end) are in fact zero; established by case analysis on the masks
  -- (each `omega` below is scoped with `clear` to just the relevant equations:
  -- with the full 8-equation system in context the elimination blows up)
  have hcy3z : cy3.val = 0 := by
    clear hr hm256 hM256_0 hM256_1 heq4 heq5 heq6 heq7 hk6 hcend
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcyL1 with h | h <;> omega
  have hcendz : cend = 0 :=
    red512_cend_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hx0 hx1 hw2 hw3 hr4 hr5 hw0 hw1 hw2n hu2 hu3 hv2 hv3 hz0 hz1 hz2 hz3
      hcyL5 hk6 hcend heq4 heq5 heq6 heq7
  -- exact multiple-of-p identity relating input and output values
  have hkey : x0.val + 2^64 * x1.val + 2^128 * x2.val + 2^192 * x3.val
      + 2^256 * (x4.val + 2^64 * x5.val + 2^128 * x6.val + 2^192 * x7.val)
      = (z0.val + 2^64 * z1.val + 2^128 * z2.val + 2^192 * z3.val)
        + 57896044618658097711785492504343953926623305935230693509004809574567321395027
          * (2 * (2^128 * x6.val + 2^192 * x7.val + 2^128 * cyL1.val
                  + r4.val + 2^64 * r5.val + cyL5.val)) :=
    red512_key_identity _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7
      ht2 ht3 ht4 hu4 hu5 hv4 hv5 hw2 hw3 hr4 hr5
      hw0 hw1 hw2n hu2 hu3 hv2 hv3 hz0 hz1 hz2 hz3
      hcyL1 hk2 hcy3 hcyL5 hk6 hcend
      heq0 heq1 heq2 heq3 heq4 heq5 heq6 heq7 hcy3z hcendz
  rw [hkey, Nat.add_mul_mod_self_left]

/-- Contract shape : `red512_ok`. -/
theorem red512_ok (lo hi : Uint4) :
    ∃ r, field.verified.red.red512 (lo, hi) = .ok r
      ∧ r.toNat = (lo.toNat + 2^256 * hi.toNat) % p :=
  Aeneas.Std.WP.spec_imp_exists (red512_spec lo hi)

/-! ## Field multiplication and squaring -/

/-- `HelioseleneField` multiplication computes `(a·b) mod p`. No reducedness
    precondition is needed: `mul_wide` is exact and `red512` is total. -/
theorem mul_ok (a b : Uint4) :
    ∃ r, field.HelioseleneField.Insts.CoreOpsArithMulHelioseleneFieldHelioseleneField.mul
        a b = .ok r
      ∧ r.toNat = (a.toNat * b.toNat) % p := by
  apply Aeneas.Std.WP.spec_imp_exists
  unfold field.HelioseleneField.Insts.CoreOpsArithMulHelioseleneFieldHelioseleneField.mul
  step as ⟨pw, hwide⟩
  obtain ⟨plo, phi⟩ := pw
  simp only [Aeneas.Std.WP.uncurry'_pair] at hwide
  apply Aeneas.Std.WP.spec_mono (red512_spec plo phi)
  intro r hr
  rw [hr]
  clear hr
  congr 1 <;> omega

/-- `field.verified.square` computes `(a·a) mod p`. -/
theorem square_ok (a : Uint4) :
    ∃ r, field.verified.square a = .ok r ∧ r.toNat = (a.toNat * a.toNat) % p := by
  apply Aeneas.Std.WP.spec_imp_exists
  unfold field.verified.square
  step as ⟨pw, hwide⟩
  obtain ⟨plo, phi⟩ := pw
  simp only [Aeneas.Std.WP.uncurry'_pair] at hwide
  apply Aeneas.Std.WP.spec_mono (red512_spec plo phi)
  intro r hr
  rw [hr]
  clear hr
  congr 1 <;> omega

end HelioseleneSpec
