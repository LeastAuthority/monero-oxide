/- Spec lemmas for the byte-encoding functions `from_repr` / `to_repr`.

   Everything in this file is PROVED (no `sorry`, no new axioms, no `native_decide`);
   exported lemmas that mention the generated hex-string constants transitively inherit
   the pre-existing `<const>._native.decide.ax_1` axioms baked into Funs.lean
   (see README §5c). -/
import HelioseleneCore.Spec.Phi
import Mathlib.Data.Nat.Bitwise

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std Result
open helioselene

namespace HelioseleneSpec

open crypto_bigint.uint crypto_bigint.limb HelioseleneModel

/-! ## Auxiliary lemmas (namespaced to avoid clashes with sibling Spec files) -/

namespace ReprAux

/-- `2^255 - p` (the value added by `from_repr`'s range check) fits in 128 bits. -/
theorem dist_lt_2_128 : 2^255 - p < 2^128 := by unfold p; norm_num

/-! ### Limb decompositions of `Uint2` / `Uint4` -/

/-- The two limbs of a `Uint2`. -/
theorem Uint2.exists_limbs (u : Uint2) :
    ∃ x0 x1 : Std.U64, u.val = [x0, x1] ∧ u.toNat = x0.val + 2^64 * x1.val := by
  obtain ⟨l, hl⟩ := u
  rw [usize2_val] at hl
  match l, hl with
  | [x0, x1], _ =>
    refine ⟨x0, x1, rfl, ?_⟩
    unfold crypto_bigint.uint.Uint.toNat
    simp [List.foldr]
    ring

/-- The four limbs of a `Uint4`. -/
theorem Uint4.exists_limbs (u : Uint4) :
    ∃ x0 x1 x2 x3 : Std.U64, u.val = [x0, x1, x2, x3]
      ∧ u.toNat = x0.val + 2^64 * x1.val + 2^128 * x2.val + 2^192 * x3.val := by
  obtain ⟨l, hl⟩ := u
  rw [usize4_val] at hl
  match l, hl with
  | [x0, x1, x2, x3], _ =>
    refine ⟨x0, x1, x2, x3, rfl, ?_⟩
    unfold crypto_bigint.uint.Uint.toNat
    simp [List.foldr]
    ring

/-! ### The full-adder helper `add_with_bounded_overflow` -/

/-- Unfolding equation for `add_with_bounded_overflow` (the do-chain is pure). -/
theorem add_with_bounded_overflow_eq (a b c : Std.U64) :
    field.verified.add_with_bounded_overflow a b c
      = ok ((core.num.U64.overflowing_add (core.num.U64.overflowing_add a b).1 c).1,
            core.convert.num.FromU64Bool.from (core.num.U64.overflowing_add a b).2
              ||| core.convert.num.FromU64Bool.from
                    (core.num.U64.overflowing_add
                      (core.num.U64.overflowing_add a b).1 c).2) := rfl

/-- `add_with_bounded_overflow` is an exact full adder when the carry-in is a bit:
    `s + 2^64·d = a + b + c` with a 0/1 carry-out `d`. -/
theorem add_with_bounded_overflow_ok (a b c : Std.U64) (hc : c.val ≤ 1) :
    ∃ s d, field.verified.add_with_bounded_overflow a b c = ok (s, d)
      ∧ d.val ≤ 1 ∧ s.val + 2^64 * d.val = a.val + b.val + c.val := by
  refine ⟨_, _, add_with_bounded_overflow_eq a b c, ?_⟩
  have h1 := U64.overflowing_add_val a b
  have h2 := U64.overflowing_add_val (core.num.U64.overflowing_add a b).1 c
  have ha : a.val < 2^64 := a.hBounds
  have hb : b.val < 2^64 := b.hBounds
  have hl : (core.num.U64.overflowing_add a b).1.val < 2^64 := UScalar.hBounds _
  have hs : (core.num.U64.overflowing_add
      (core.num.U64.overflowing_add a b).1 c).1.val < 2^64 := UScalar.hBounds _
  rw [UScalar.val_or]
  cases hc1 : (core.num.U64.overflowing_add a b).2 <;>
    cases hc2 : (core.num.U64.overflowing_add
        (core.num.U64.overflowing_add a b).1 c).2 <;>
    rw [hc1] at h1 <;> rw [hc2] at h2 <;>
    simp only [core.convert.num.FromU64Bool.from] <;>
    norm_num at h1 h2 ⊢ <;> omega

/-- Hoare-triple form of `add_with_bounded_overflow_ok` (for `step`). -/
@[step] theorem add_with_bounded_overflow_spec (a b c : Std.U64) (hc : c.val ≤ 1) :
    field.verified.add_with_bounded_overflow a b c
      ⦃ s d => d.val ≤ 1 ∧ s.val + 2^64 * d.val = a.val + b.val + c.val ⦄ := by
  obtain ⟨s, d, heq, h⟩ := add_with_bounded_overflow_ok a b c hc
  rw [heq, Aeneas.Std.WP.spec_ok]
  exact h

/-! ### The final bit test of `reduced` -/

/-- `(s &&& 2^63) ||| c = 0` iff bit 63 of `s` is clear and `c = 0`. -/
theorem flag_iff (s c : Nat) (hs : s < 2^64) (hc : c ≤ 1) :
    ((s &&& 2^63) ||| c) = 0 ↔ (s < 2^63 ∧ c = 0) := by
  have hand : s &&& 2^63 = s / 2^63 % 2 * 2^63 := by
    rw [Nat.and_two_pow, Nat.toNat_testBit]
  constructor
  · intro h
    have h1 : s &&& 2^63 = 0 := Nat.le_zero.mp (h ▸ Nat.left_le_or)
    have h2 : c = 0 := Nat.le_zero.mp (h ▸ Nat.right_le_or)
    rw [hand] at h1
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    subst h2
    rw [Nat.or_zero, hand]
    have : s / 2^63 = 0 := Nat.div_eq_of_lt h1
    omega

/-! ### The carry-chain loop of `from_repr.reduced`

The loop adds `d = 2^255 - p` (a 2-limb constant, zero-padded to 4 limbs) to the
4-limb input `a`, keeping only the latest sum limb and the running 0/1 carry.
After the last iteration `last` is the top limb of `a + d` and `carry` is bit 256. -/

theorem reduced_loop_spec (z0 : Std.U64) (hz0 : z0.val = 0) (a : Uint4) :
    field.verified.from_repr.reduced_loop z0
        { start := 0#usize, «end» := 4#usize } a z0 z0
      ⦃ last carry => carry.val ≤ 1 ∧ ∃ lo, lo < 2^192 ∧
          a.toNat + (2^255 - p) = lo + 2^192 * last.val + 2^256 * carry.val ⦄ := by
  obtain ⟨w0, w1, w2, w3, ha, hanat⟩ := ReprAux.Uint4.exists_limbs a
  unfold field.verified.from_repr.reduced_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun st => 4 - st.1.start.val)
    (inv := fun (st : core.ops.range.Range Std.Usize × Std.U64 × Std.U64) =>
      st.1.«end» = 4#usize ∧ st.2.2.val ≤ 1 ∧
      ( (st.1.start.val = 0 ∧ st.2.1.val = 0 ∧ st.2.2.val = 0)
      ∨ (st.1.start.val = 1 ∧
          w0.val + (2^255 - p) % 2^64 = st.2.1.val + 2^64 * st.2.2.val)
      ∨ (st.1.start.val = 2 ∧ ∃ lo, lo < 2^64 ∧
          w0.val + 2^64 * w1.val + (2^255 - p)
            = lo + 2^64 * st.2.1.val + 2^128 * st.2.2.val)
      ∨ (st.1.start.val = 3 ∧ ∃ lo, lo < 2^128 ∧
          w0.val + 2^64 * w1.val + 2^128 * w2.val + (2^255 - p)
            = lo + 2^128 * st.2.1.val + 2^192 * st.2.2.val)
      ∨ (st.1.start.val = 4 ∧ ∃ lo, lo < 2^192 ∧
          w0.val + 2^64 * w1.val + 2^128 * w2.val + 2^192 * w3.val + (2^255 - p)
            = lo + 2^192 * st.2.1.val + 2^256 * st.2.2.val) ))
  · -- the loop body preserves the invariant
    rintro ⟨iter, last, carry⟩ hinv
    obtain ⟨hend, hcle, hcase⟩ := hinv
    dsimp only at hend hcle hcase ⊢
    show Aeneas.Std.WP.spec
      (field.verified.from_repr.reduced_loop.body z0 a iter last carry) _
    unfold field.verified.from_repr.reduced_loop.body
    rcases hcase with ⟨hk, hlast0, hcarry0⟩ | ⟨hk, heqk⟩ | ⟨hk, lo, hlo, heqk⟩
      | ⟨hk, lo, hlo, heqk⟩ | ⟨hk, lo, hlo, heqk⟩
    · -- iteration 0: add limb 0 of MODULUS_255_DISTANCE
      obtain ⟨⟨o, iter1⟩, hnext, ho, hst, hend1⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (core.iter.range.IteratorRange.next_Usize_some_spec iter
            (by rw [hend]; scalar_tac))
      subst ho
      rw [hnext]
      show Aeneas.Std.WP.spec
        ((do
          let b ← if iter.start < 2#usize then do
              let u ← field.verified.MODULUS_255_DISTANCE
              let a1 ← crypto_bigint.uint.Uint.as_limbs u
              Aeneas.Std.Array.index_usize a1 iter.start
            else ok z0
          let a1 ← crypto_bigint.uint.Uint.as_limbs a
          let l ← Aeneas.Std.Array.index_usize a1 iter.start
          let (last2, carry1) ←
            field.verified.add_with_bounded_overflow l b carry
          ok (ControlFlow.cont (iter1, last2, carry1))) :
          Result (ControlFlow
            (core.ops.range.Range Std.Usize × Std.U64 × Std.U64)
            (Std.U64 × Std.U64))) _
      rw [if_pos (show iter.start < 2#usize by scalar_tac)]
      obtain ⟨m, hmeq, hm⟩ := MODULUS_255_DISTANCE_ok
      obtain ⟨x0, x1, hmval, hmnat⟩ := ReprAux.Uint2.exists_limbs m
      rw [hmeq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [Uint.as_limbs_ok]
      simp only [Aeneas.Std.bind_tc_ok]
      obtain ⟨b, hbeq, hbv⟩ := Aeneas.Std.WP.spec_imp_exists
        (Aeneas.Std.Array.index_usize_spec m iter.start (by scalar_tac))
      simp only [hmval, hk, List.getElem_cons_zero] at hbv
      rw [hbv] at hbeq
      rw [hbeq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [Uint.as_limbs_ok]
      simp only [Aeneas.Std.bind_tc_ok]
      obtain ⟨l, hleq, hlv⟩ := Aeneas.Std.WP.spec_imp_exists
        (Aeneas.Std.Array.index_usize_spec a iter.start (by scalar_tac))
      simp only [ha, hk, List.getElem_cons_zero] at hlv
      rw [hlv] at hleq
      rw [hleq]
      simp only [Aeneas.Std.bind_tc_ok]
      obtain ⟨s', d', haw, hdle, hsum⟩ :=
        ReprAux.add_with_bounded_overflow_ok w0 x0 carry hcle
      rw [haw]
      show Aeneas.Std.WP.spec
        (ok (ControlFlow.cont (iter1, s', d')) :
          Result (ControlFlow
            (core.ops.range.Range Std.Usize × Std.U64 × Std.U64)
            (Std.U64 × Std.U64))) _
      rw [Aeneas.Std.WP.spec_ok]
      have hx0 : x0.val < 2^64 := x0.hBounds
      have hx1 : x1.val < 2^64 := x1.hBounds
      have hdd : 2^255 - p < 2^128 := ReprAux.dist_lt_2_128
      exact ⟨⟨hend1.trans hend, hdle,
        Or.inr (Or.inl ⟨show iter1.start.val = 1 by omega,
          show w0.val + (2^255 - p) % 2^64 = s'.val + 2^64 * d'.val by
            omega⟩)⟩,
        show 4 - iter1.start.val < 4 - iter.start.val by omega⟩
    · -- iteration 1: add limb 1 of MODULUS_255_DISTANCE
      obtain ⟨⟨o, iter1⟩, hnext, ho, hst, hend1⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (core.iter.range.IteratorRange.next_Usize_some_spec iter
            (by rw [hend]; scalar_tac))
      subst ho
      rw [hnext]
      show Aeneas.Std.WP.spec
        ((do
          let b ← if iter.start < 2#usize then do
              let u ← field.verified.MODULUS_255_DISTANCE
              let a1 ← crypto_bigint.uint.Uint.as_limbs u
              Aeneas.Std.Array.index_usize a1 iter.start
            else ok z0
          let a1 ← crypto_bigint.uint.Uint.as_limbs a
          let l ← Aeneas.Std.Array.index_usize a1 iter.start
          let (last2, carry1) ←
            field.verified.add_with_bounded_overflow l b carry
          ok (ControlFlow.cont (iter1, last2, carry1))) :
          Result (ControlFlow
            (core.ops.range.Range Std.Usize × Std.U64 × Std.U64)
            (Std.U64 × Std.U64))) _
      rw [if_pos (show iter.start < 2#usize by scalar_tac)]
      obtain ⟨m, hmeq, hm⟩ := MODULUS_255_DISTANCE_ok
      obtain ⟨x0, x1, hmval, hmnat⟩ := ReprAux.Uint2.exists_limbs m
      rw [hmeq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [Uint.as_limbs_ok]
      simp only [Aeneas.Std.bind_tc_ok]
      obtain ⟨b, hbeq, hbv⟩ := Aeneas.Std.WP.spec_imp_exists
        (Aeneas.Std.Array.index_usize_spec m iter.start (by scalar_tac))
      simp [hmval, hk] at hbv
      rw [hbv] at hbeq
      rw [hbeq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [Uint.as_limbs_ok]
      simp only [Aeneas.Std.bind_tc_ok]
      obtain ⟨l, hleq, hlv⟩ := Aeneas.Std.WP.spec_imp_exists
        (Aeneas.Std.Array.index_usize_spec a iter.start (by scalar_tac))
      simp [ha, hk] at hlv
      rw [hlv] at hleq
      rw [hleq]
      simp only [Aeneas.Std.bind_tc_ok]
      obtain ⟨s', d', haw, hdle, hsum⟩ :=
        ReprAux.add_with_bounded_overflow_ok w1 x1 carry hcle
      rw [haw]
      show Aeneas.Std.WP.spec
        (ok (ControlFlow.cont (iter1, s', d')) :
          Result (ControlFlow
            (core.ops.range.Range Std.Usize × Std.U64 × Std.U64)
            (Std.U64 × Std.U64))) _
      rw [Aeneas.Std.WP.spec_ok]
      have hx0 : x0.val < 2^64 := x0.hBounds
      have hx1 : x1.val < 2^64 := x1.hBounds
      have hlast : last.val < 2^64 := last.hBounds
      have hdd : 2^255 - p < 2^128 := ReprAux.dist_lt_2_128
      exact ⟨⟨hend1.trans hend, hdle,
        Or.inr (Or.inr (Or.inl ⟨show iter1.start.val = 2 by omega,
          ⟨last.val, show last.val < 2^64 from hlast,
           show w0.val + 2^64 * w1.val + (2^255 - p)
               = last.val + 2^64 * s'.val + 2^128 * d'.val by omega⟩⟩))⟩,
        show 4 - iter1.start.val < 4 - iter.start.val by omega⟩
    · -- iteration 2: add the zero padding limb
      obtain ⟨⟨o, iter1⟩, hnext, ho, hst, hend1⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (core.iter.range.IteratorRange.next_Usize_some_spec iter
            (by rw [hend]; scalar_tac))
      subst ho
      rw [hnext]
      show Aeneas.Std.WP.spec
        ((do
          let b ← if iter.start < 2#usize then do
              let u ← field.verified.MODULUS_255_DISTANCE
              let a1 ← crypto_bigint.uint.Uint.as_limbs u
              Aeneas.Std.Array.index_usize a1 iter.start
            else ok z0
          let a1 ← crypto_bigint.uint.Uint.as_limbs a
          let l ← Aeneas.Std.Array.index_usize a1 iter.start
          let (last2, carry1) ←
            field.verified.add_with_bounded_overflow l b carry
          ok (ControlFlow.cont (iter1, last2, carry1))) :
          Result (ControlFlow
            (core.ops.range.Range Std.Usize × Std.U64 × Std.U64)
            (Std.U64 × Std.U64))) _
      rw [if_neg (show ¬ iter.start < 2#usize by scalar_tac)]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [Uint.as_limbs_ok]
      simp only [Aeneas.Std.bind_tc_ok]
      obtain ⟨l, hleq, hlv⟩ := Aeneas.Std.WP.spec_imp_exists
        (Aeneas.Std.Array.index_usize_spec a iter.start (by scalar_tac))
      simp [ha, hk] at hlv
      rw [hlv] at hleq
      rw [hleq]
      simp only [Aeneas.Std.bind_tc_ok]
      obtain ⟨s', d', haw, hdle, hsum⟩ :=
        ReprAux.add_with_bounded_overflow_ok w2 z0 carry hcle
      rw [haw]
      show Aeneas.Std.WP.spec
        (ok (ControlFlow.cont (iter1, s', d')) :
          Result (ControlFlow
            (core.ops.range.Range Std.Usize × Std.U64 × Std.U64)
            (Std.U64 × Std.U64))) _
      rw [Aeneas.Std.WP.spec_ok]
      have hlast : last.val < 2^64 := last.hBounds
      exact ⟨⟨hend1.trans hend, hdle,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨show iter1.start.val = 3 by omega,
          ⟨lo + 2^64 * last.val, show lo + 2^64 * last.val < 2^128 by omega,
           show w0.val + 2^64 * w1.val + 2^128 * w2.val + (2^255 - p)
               = (lo + 2^64 * last.val) + 2^128 * s'.val + 2^192 * d'.val by
             omega⟩⟩)))⟩,
        show 4 - iter1.start.val < 4 - iter.start.val by omega⟩
    · -- iteration 3: add the zero padding limb
      obtain ⟨⟨o, iter1⟩, hnext, ho, hst, hend1⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (core.iter.range.IteratorRange.next_Usize_some_spec iter
            (by rw [hend]; scalar_tac))
      subst ho
      rw [hnext]
      show Aeneas.Std.WP.spec
        ((do
          let b ← if iter.start < 2#usize then do
              let u ← field.verified.MODULUS_255_DISTANCE
              let a1 ← crypto_bigint.uint.Uint.as_limbs u
              Aeneas.Std.Array.index_usize a1 iter.start
            else ok z0
          let a1 ← crypto_bigint.uint.Uint.as_limbs a
          let l ← Aeneas.Std.Array.index_usize a1 iter.start
          let (last2, carry1) ←
            field.verified.add_with_bounded_overflow l b carry
          ok (ControlFlow.cont (iter1, last2, carry1))) :
          Result (ControlFlow
            (core.ops.range.Range Std.Usize × Std.U64 × Std.U64)
            (Std.U64 × Std.U64))) _
      rw [if_neg (show ¬ iter.start < 2#usize by scalar_tac)]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [Uint.as_limbs_ok]
      simp only [Aeneas.Std.bind_tc_ok]
      obtain ⟨l, hleq, hlv⟩ := Aeneas.Std.WP.spec_imp_exists
        (Aeneas.Std.Array.index_usize_spec a iter.start (by scalar_tac))
      simp [ha, hk] at hlv
      rw [hlv] at hleq
      rw [hleq]
      simp only [Aeneas.Std.bind_tc_ok]
      obtain ⟨s', d', haw, hdle, hsum⟩ :=
        ReprAux.add_with_bounded_overflow_ok w3 z0 carry hcle
      rw [haw]
      show Aeneas.Std.WP.spec
        (ok (ControlFlow.cont (iter1, s', d')) :
          Result (ControlFlow
            (core.ops.range.Range Std.Usize × Std.U64 × Std.U64)
            (Std.U64 × Std.U64))) _
      rw [Aeneas.Std.WP.spec_ok]
      have hlast : last.val < 2^64 := last.hBounds
      exact ⟨⟨hend1.trans hend, hdle,
        Or.inr (Or.inr (Or.inr (Or.inr ⟨show iter1.start.val = 4 by omega,
          ⟨lo + 2^128 * last.val, show lo + 2^128 * last.val < 2^192 by omega,
           show w0.val + 2^64 * w1.val + 2^128 * w2.val + 2^192 * w3.val
                 + (2^255 - p)
               = (lo + 2^128 * last.val) + 2^192 * s'.val + 2^256 * d'.val by
             omega⟩⟩)))⟩,
        show 4 - iter1.start.val < 4 - iter.start.val by omega⟩
    · -- the range is exhausted: return (last, carry)
      obtain ⟨⟨o, iter1⟩, hnext, ho, hiter1⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (core.iter.range.IteratorRange.next_Usize_none_spec iter
            (by rw [hend]; scalar_tac))
      subst ho
      rw [hnext]
      show Aeneas.Std.WP.spec
        (ok (ControlFlow.done (last, carry)) :
          Result (ControlFlow
            (core.ops.range.Range Std.Usize × Std.U64 × Std.U64)
            (Std.U64 × Std.U64))) _
      rw [Aeneas.Std.WP.spec_ok]
      exact ⟨hcle, ⟨lo, hlo,
        show a.toNat + (2^255 - p)
            = lo + 2^192 * last.val + 2^256 * carry.val by omega⟩⟩
  · -- the invariant holds at entry
    dsimp only
    exact ⟨rfl, by omega, Or.inl ⟨by simp, hz0, hz0⟩⟩

/-! ### The canonicity check `from_repr.reduced` -/

/-- `reduced` returns the constant-time comparison `a < p`. -/
theorem reduced_ok (a : Uint4) :
    ∃ c, field.verified.from_repr.reduced a = ok c ∧ (c = true ↔ a.toNat < p) := by
  unfold field.verified.from_repr.reduced
  simp only [crypto_bigint.limb.Limb.ZERO, crypto_bigint.uint.Uint.LIMBS_1,
    Aeneas.Std.bind_tc_ok]
  obtain ⟨⟨last1, carry⟩, hloop, hcle, lo, hlo, hsum⟩ :=
    Aeneas.Std.WP.spec_imp_exists (reduced_loop_spec 0#u64 (by simp) a)
  rw [hloop]
  show ∃ c, (do
      let l1 ← Limb.Insts.CoreOpsBitShlUsizeLimb.shl 1#u64
        (Std.Usize.wrapping_sub 64#usize 1#usize)
      let l2 ← Limb.Insts.CoreOpsBitBitAndLimbLimb.bitand last1 l1
      let l3 ← Limb.Insts.CoreOpsBitBitOrLimbLimb.bitor l2 carry
      Limb.Insts.SubtleConstantTimeEq.ct_eq l3 0#u64)
      = ok c ∧ (c = true ↔ a.toNat < p)
  have hi2 : (Std.Usize.wrapping_sub 64#usize 1#usize).val = 63 := by
    rw [Std.Usize.wrapping_sub_val_eq]
    have h1 : (64#usize).val = 64 := by simp
    have h2 : (1#usize).val = 1 := by simp
    have h3 : UScalar.size .Usize = 2^System.Platform.numBits := by
      rw [UScalar.size_UScalarTyUsize, Usize.size_def, Usize.numBits_def,
        UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;>
      rw [h] at h3 <;> rw [h1, h2, h3] <;> norm_num
  obtain ⟨l1, hl1eq, hl1⟩ := Limb.shl_ok 1#u64
    (Std.Usize.wrapping_sub 64#usize 1#usize) (by omega)
  rw [hl1eq]
  simp only [Aeneas.Std.bind_tc_ok]
  have hl1v : l1.val = 2^63 := by
    rw [hl1, hi2]
    norm_num [Nat.shiftLeft_eq]
  obtain ⟨l2, hl2eq, hl2⟩ := Limb.bitand_ok last1 l1
  rw [hl2eq]
  simp only [Aeneas.Std.bind_tc_ok]
  obtain ⟨l3, hl3eq, hl3⟩ := Limb.bitor_ok l2 carry
  rw [hl3eq]
  simp only [Aeneas.Std.bind_tc_ok]
  obtain ⟨c, hceq, hc⟩ := Limb.ct_eq_ok l3 0#u64
  rw [hceq]
  refine ⟨c, rfl, ?_⟩
  have hl3' : l3.val = (last1.val &&& 2^63) ||| carry.val := by
    rw [hl3, hl2, hl1v]
  have hflag := flag_iff last1.val carry.val last1.hBounds hcle
  have h0 : (0#u64).val = 0 := by simp
  rw [hc, h0, hl3', hflag]
  have hp255 : p < 2^255 := p_lt_two_pow_255
  have hlast1 : last1.val < 2^64 := last1.hBounds
  constructor
  · intro h
    omega
  · intro h
    omega

end ReprAux

/-! ## The Spec contract: `from_repr` / `to_repr` -/

/-- `from_repr` decodes the little-endian bytes exactly and flags canonicity
    (`is_some ↔ value < p`). -/
theorem from_repr_ok (bytes : Aeneas.Std.Array Std.U8 32#usize) :
    ∃ v flag, field.verified.from_repr bytes = ok (v, flag)
      ∧ v.toNat = leVal bytes ∧ (flag = true ↔ leVal bytes < p) := by
  unfold field.verified.from_repr
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok]
  have hlen : (Aeneas.Std.Array.to_slice bytes).val.length = 8 * (4#usize).val := by
    rw [Aeneas.Std.Array.val_to_slice, Aeneas.Std.Array.length_eq]
    simp
  obtain ⟨res, hreseq, hres⟩ :=
    Uint.from_le_slice_ok 4#usize (Aeneas.Std.Array.to_slice bytes) hlen
  rw [hreseq]
  simp only [Aeneas.Std.bind_tc_ok]
  obtain ⟨flag, hflageq, hflag⟩ := ReprAux.reduced_ok res
  rw [hflageq]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [CtOption.new_ok]
  refine ⟨res, flag, rfl, ?_, ?_⟩
  · rw [hres, Aeneas.Std.Array.val_to_slice]
    rfl
  · rw [hflag, hres, Aeneas.Std.Array.val_to_slice]
    exact Iff.rfl

/-- `to_repr` emits the canonical little-endian encoding of the value. -/
theorem to_repr_ok (a : Uint4) :
    ∃ bytes, field.verified.to_repr a = ok bytes ∧ leVal bytes = a.toNat := by
  obtain ⟨bytes, heq, h⟩ := Uint4.to_le_bytes_ok a
  exact ⟨bytes, heq, h⟩

end HelioseleneSpec
