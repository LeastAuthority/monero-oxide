/- Specification of `field.verified.invert.invert` — constant-time modular inversion by
   binary GCD (Algorithm 1 of "Optimized Binary GCD for Modular Inversion",
   https://eprint.iacr.org/2020/972), 510 fixed iterations of the branch-free `step`.

   Exported contract lemma (namespace `HelioseleneSpec`): `invert_ok`.

   Proof status: PROVED with no `sorry` in the inversion dependency cone.
   This includes `sub_with_bounded_overflow_spec`,
     `add_with_bounded_overflow_spec`, `select_word_spec`/`select_loop_spec`/`select_spec`
     (the masked 4-limb select), totality of every inner loop of `step`
     (`step_loop0_total` … `step_loop4_total`), exact value-level specs of all five
     inner loops (`step_loop0_value_spec` … `step_loop4_value_spec`), totality +
     zero-propagation of `step` itself (`step_basic_spec`, `step_total`), and the
     local `sub_value_spec`, `red1_loop_spec`, `red1_spec`, `is_zero_loop_spec`,
     `is_zero_spec` specs.  `step_congruence` proves every Algorithm-1 invariant
     conjunct from the machine-level ledger: both congruences, oddness of `b`, all four
     range bounds, gcd preservation and the potential halving `2·a'·b' ≤ a·b`.

   The Rust source now includes `add_two_modulus` in the high-half carry chain. This
   replaces the former top-bit OR and removes its conditional `UVWindow` obligation;
   the selected 0/p/2p addend is exact for every state.

   Note on `#print axioms`: everything here additionally reports
   `helioselene.field.MODULUS._native.decide.ax_1` (and the analogous axiom for
   `MODULUS_XOR_TWO_MODULUS`).  Those axioms are embedded in the *generated definitions*
   in Funs.lean — Aeneas' `toStr` fills its length side-condition with `decide +native` —
   and are shared by every Spec lemma that mentions those constants (e.g. the
   pre-existing `HelioseleneSpec.MODULUS_ok`); no proof in this file uses
   `native_decide`. -/
import HelioseleneCore.Spec.Phi
import HelioseleneCore.Spec.Prime

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

open Aeneas Aeneas.Std Result
open helioselene

namespace HelioseleneSpec

open crypto_bigint.uint crypto_bigint.limb HelioseleneModel

namespace Invert

/-! ## Small helpers: 0/1 flags and 0/all-ones masks -/

/-- Value of the `Bool → U64` conversion used for carry/borrow flags. -/
@[step] theorem fromU64Bool_spec (b : Bool) :
    lift (core.convert.num.FromU64Bool.from b) ⦃ x => x.val = if b then 1 else 0 ⦄ := by
  simp only [Aeneas.Std.lift, WP.spec_ok, core.convert.num.FromU64Bool.from]
  cases b <;> simp

theorem fromBool_or_val (x y : Bool) :
    ((core.convert.num.FromU64Bool.from x ||| core.convert.num.FromU64Bool.from y) :
      Std.U64).val = if x || y then 1 else 0 := by
  cases x <;> cases y <;> rfl

/-- A limb is a constant-time selection mask: all-zeros or all-ones. -/
def IsMask (x : Limb) : Prop := x.val = 0 ∨ x.val = 2^64 - 1

theorem isMask_of_wrapping_neg {x m : Limb} (hx : x.val ≤ 1)
    (hm : m.val = (2^64 - x.val) % 2^64) : IsMask m := by
  unfold IsMask; omega

theorem isMask_and {x y r : Limb} (hx : IsMask x) (hy : IsMask y)
    (hr : r.val = x.val &&& y.val) : IsMask r := by
  unfold IsMask at *
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    rw [hx, hy] at hr <;>
    simp only [Nat.zero_and, Nat.and_zero, Nat.and_self] at hr <;> omega

/-- Value of a non-underflowing `Usize.wrapping_sub`. -/
theorem usize_wrapping_sub_val {x y : Std.Usize} (hy : y.val ≤ x.val) :
    (Std.Usize.wrapping_sub x y).val = x.val - y.val := by
  rw [Usize.wrapping_sub_val_eq, UScalar.size_def]
  have hnb : UScalarTy.Usize.numBits = System.Platform.numBits := rfl
  have hb := x.hBounds
  rw [hnb]
  rw [hnb] at hb
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> rw [h] at hb <;> omega

/-- Value of a non-overflowing `Usize.wrapping_mul` (bound `2^32` fits both platforms). -/
theorem usize_wrapping_mul_val {x y : Std.Usize} (h : x.val * y.val < 2^32) :
    (Std.Usize.wrapping_mul x y).val = x.val * y.val := by
  rw [Usize.wrapping_mul_val_eq, UScalar.size_def]
  have hnb : UScalarTy.Usize.numBits = System.Platform.numBits := rfl
  rw [hnb]
  rcases System.Platform.numBits_eq with hh | hh <;> rw [hh] <;>
    [exact Nat.mod_eq_of_lt (by omega); exact Nat.mod_eq_of_lt (by omega)]

/-! ## `sub_with_bounded_overflow` / `add_with_bounded_overflow` (task item 2: proved)

Cf. the Veridise Dafny proofs of the same helper:
https://github.com/VeridiseAuditing/helioselene-dafny-proofs
  /blob/9da40f40d62776d380f4423124ae7ca6b956f12b/src/crypto_bigint_0_5_5/Limb.dfy#L342-L355 -/

/-- Full-subtractor: `d = a - b - c` with a borrow normalized to 0/1.
    Exact identity: `d + b + c = a + 2^64·bo`. -/
@[step] theorem sub_with_bounded_overflow_spec (a b c : Limb) (hc : c.val ≤ 1) :
    field.verified.invert.sub_with_bounded_overflow a b c
      ⦃ d bo => d.val + b.val + c.val = a.val + 2^64 * bo.val ∧ bo.val ≤ 1 ⦄ := by
  unfold field.verified.invert.sub_with_bounded_overflow
  step as ⟨limb, borrow1, h1⟩
  step as ⟨limb1, borrow2, h2⟩
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, WP.spec_ok]
  split at h1 <;> split at h2 <;>
    obtain ⟨he1, hb1⟩ := h1 <;> obtain ⟨he2, hb2⟩ := h2 <;> subst hb1 hb2 <;>
    simp only [WP.uncurry'_pair, fromBool_or_val, Bool.or_self, Bool.true_or, Bool.or_true,
      Bool.or_false, Bool.false_or, if_true, if_false, Bool.false_eq_true,
      Bool.true_eq_false] <;>
    constructor <;> scalar_tac

/-- Full-adder: `s = a + b + c` with a carry normalized to 0/1.
    Exact identity: `s + 2^64·co = a + b + c`. -/
@[step] theorem add_with_bounded_overflow_spec (a b c : Limb) (hc : c.val ≤ 1) :
    field.verified.add_with_bounded_overflow a b c
      ⦃ s co => s.val + 2^64 * co.val = a.val + b.val + c.val ∧ co.val ≤ 1 ⦄ := by
  unfold field.verified.add_with_bounded_overflow
  step as ⟨limb, carry1, h1⟩
  step as ⟨limb1, carry2, h2⟩
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, WP.spec_ok]
  split at h1 <;> split at h2 <;>
    obtain ⟨he1, hb1⟩ := h1 <;> obtain ⟨he2, hb2⟩ := h2 <;> subst hb1 hb2 <;>
    simp only [WP.uncurry'_pair, fromBool_or_val, Bool.or_self, Bool.true_or, Bool.or_true,
      Bool.or_false, Bool.false_or, if_true, if_false, Bool.false_eq_true,
      Bool.true_eq_false] <;>
    constructor <;> scalar_tac

/-! ## `select_word` and the masked 4-limb `select` (task item 1: proved)

Cf. the Veridise Dafny select lemma:
https://github.com/VeridiseAuditing/helioselene-dafny-proofs
  /blob/9da40f40d62776d380f4423124ae7ca6b956f12b/src/helioselene/field/Base.dfy#L238-L264 -/

/-- `select_word a b choice` = `a` for the zero mask, `b` for the all-ones mask. -/
theorem select_word_spec (a b choice : Limb) (hc : IsMask choice) :
    field.verified.select_word a b choice
      ⦃ r => r = if choice.val = 0 then a else b ⦄ := by
  unfold field.verified.select_word
  step as ⟨l, hl⟩
  step as ⟨l1, hl1⟩
  step as ⟨r, hr⟩
  rw [hl] at hl1
  split
  · next hc0 =>
    rw [hc0, Nat.and_zero] at hl1
    rw [hl1, Nat.xor_zero] at hr
    exact UScalar.val_eq_imp _ _ hr
  · next hc0 =>
    rcases hc with hc | hc; · exact absurd hc hc0
    rw [hc, Nat.and_two_pow_sub_one_of_lt_two_pow
      (Nat.xor_lt_two_pow (by scalar_tac) (by scalar_tac))] at hl1
    rw [hl1, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at hr
    exact UScalar.val_eq_imp _ _ hr

/-- The masked 4-limb select loop writes `(if choice = 0 then a else b)` into `res`. -/
theorem select_loop_spec (a b : Uint4) (choice : Limb) (hc : IsMask choice)
    (iter : core.ops.range.Range Std.Usize) (res : Uint4)
    (hend : iter.«end» = 4#usize) (hstart : iter.start.val ≤ 4)
    (hres : ∀ l : ℕ, l < iter.start.val →
      res[l]! = (if choice.val = 0 then a else b)[l]!) :
    field.verified.invert.invert.step.select_loop iter a b choice res
      ⦃ r => r = if choice.val = 0 then a else b ⦄ := by
  unfold field.verified.invert.invert.step.select_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (s : (core.ops.range.Range Std.Usize) × Uint4) =>
      s.1.«end».val - s.1.start.val)
    (inv := fun s =>
      s.1.«end» = 4#usize ∧ s.1.start.val ≤ 4 ∧
      ∀ l : ℕ, l < s.1.start.val →
        s.2[l]! = (if choice.val = 0 then a else b)[l]!)
  · rintro ⟨it, r⟩ ⟨hend', hstart', hres'⟩
    try simp only at hend' hstart' hres'
    unfold field.verified.invert.invert.step.select_loop.body
    step as ⟨o, iter1, ho, hoe⟩
    have hendval : it.«end».val = 4 := by rw [hend']; simp
    rcases o with _ | l
    · -- done branch
      split at ho
      · simp at ho
      · next hge =>
        try simp only [WP.spec_ok]
        have hstart4 : it.start.val = 4 := by omega
        apply Subtype.ext
        apply List.ext_getElem! (by simp [Aeneas.Std.Array.length_eq])
        intro n
        by_cases hn : n < 4
        · have := hres' n (by omega)
          simpa [Array.getElem!_Nat_eq] using this
        · rw [getElem!_neg _ _ (by scalar_tac), getElem!_neg _ _ (by scalar_tac)]
    · -- continue branch
      split at ho
      · next hlt =>
        obtain ⟨hosome, hst1⟩ := ho
        have hleq : l = it.start := by injection hosome
        subst hleq
        have hbound : it.start.val < 4 := by omega
        step as ⟨a1, ha1⟩
        subst ha1
        step as ⟨l1, hl1⟩
        step as ⟨a2, ha2⟩
        subst ha2
        step as ⟨l2, hl2⟩
        step with select_word_spec as ⟨l3, hl3⟩
        step as ⟨a3, back, ha3, hback⟩
        subst ha3
        step as ⟨a4, ha4⟩
        subst ha4
        simp only [hback, WP.spec_ok]
        have hoev : iter1.«end».val = 4 := by rw [hoe, hend']; simp
        refine ⟨by rw [hoe, hend'], by omega, ?_, by omega⟩
        intro k hk
        rw [hst1] at hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
        · rw [Array.getElem!_Nat_set_ne _ _ _ _ (by omega)]
          exact hres' k hk
        · subst hk
          rw [Array.getElem!_Nat_set_eq _ _ _ _
            ⟨rfl, by simp [Aeneas.Std.Array.length_eq, hbound]⟩]
          rw [hl3, hl1, hl2]
          split <;> simp [Array.getElem!_Nat_eq, getElem!_pos, Aeneas.Std.Array.length_eq,
            hbound]
      · simp at ho
  · exact ⟨hend, hstart, hres⟩

/-- **Task item 1 (proved).** `invert.step.select a b choice` returns `a` for the zero
    mask and `b` for the all-ones mask. -/
theorem select_spec (a b : Uint4) (choice : Limb) (hc : IsMask choice) :
    field.verified.invert.invert.step.select a b choice
      ⦃ r => r = if choice.val = 0 then a else b ⦄ := by
  unfold field.verified.invert.invert.step.select
  step as ⟨res, hres⟩
  step as ⟨i, hi⟩
  exact select_loop_spec a b choice hc _ res hi (by simp) (by simp)

/-! ## Totality of the five inner loops of `step`

For the Field-instance wrapper we mainly need that `step` never fails; along the way we
keep the borrow/carry flags normalized (`≤ 1`), which is also what makes the wrapping
negations of those flags legitimate 0/all-ones masks. -/

/-- Totality of the `a - b` borrow-chain loop (`for l in 0..4`); the final borrow is 0/1. -/
@[step] theorem step_loop0_total (iter : core.ops.range.Range Std.Usize)
    (a b : Uint4) (borrow : Limb) (d : Uint4)
    (hend : iter.«end».val ≤ 4) (hb : borrow.val ≤ 1) :
    field.verified.invert.invert.step_loop0 iter a b borrow d
      ⦃ bo _d => bo.val ≤ 1 ⦄ := by
  unfold field.verified.invert.invert.step_loop0
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (s : (core.ops.range.Range Std.Usize) × Limb × Uint4) =>
      s.1.«end».val - s.1.start.val)
    (inv := fun s => s.1.«end».val ≤ 4 ∧ s.2.1.val ≤ 1)
  · rintro ⟨it, bor, dd⟩ ⟨hend', hb'⟩
    unfold field.verified.invert.invert.step_loop0.body
    step as ⟨o, iter1, ho, hoe⟩
    rcases o with _ | l
    · split at ho
      · simp at ho
      · simp only [WP.spec_ok] <;> scalar_tac
    · split at ho
      · next hlt =>
        obtain ⟨hosome, hst1⟩ := ho
        have hleq : l = it.start := by injection hosome
        subst hleq
        step as ⟨a1, ha1⟩
        subst ha1
        step as ⟨l1, hl1⟩
        step as ⟨a2, ha2⟩
        subst ha2
        step as ⟨l2, hl2⟩
        step as ⟨l3, borrow1, hsub, hb1⟩
        step as ⟨a3, back, ha3, hback⟩
        subst ha3
        step as ⟨a4, ha4⟩
        scalar_tac
      · simp at ho
  · exact ⟨hend, hb⟩

/-- Totality of the conditional-negation loop (`for l in 0..4`). -/
@[step] theorem step_loop1_total (iter : core.ops.range.Range Std.Usize)
    (a_sub_b : Uint4) (a_lt_b carry : Limb) (d : Uint4)
    (hend : iter.«end».val ≤ 4) :
    field.verified.invert.invert.step_loop1 iter a_sub_b a_lt_b carry d
      ⦃ _r => True ⦄ := by
  unfold field.verified.invert.invert.step_loop1
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (s : (core.ops.range.Range Std.Usize) × Limb × Uint4) =>
      s.1.«end».val - s.1.start.val)
    (inv := fun s => s.1.«end».val ≤ 4)
  · rintro ⟨it, car, dd⟩ hend'
    unfold field.verified.invert.invert.step_loop1.body
    step as ⟨o, iter1, ho, hoe⟩
    rcases o with _ | l
    · split at ho
      · simp at ho
      · simp only [WP.spec_ok] <;> scalar_tac
    · split at ho
      · next hlt =>
        obtain ⟨hosome, hst1⟩ := ho
        have hleq : l = it.start := by injection hosome
        subst hleq
        step as ⟨a1, ha1⟩
        subst ha1
        step as ⟨l1, hl1⟩
        step as ⟨l2, hl2⟩
        step as ⟨limb, carry_bool, hadd⟩
        step as ⟨i, hi⟩
        step as ⟨a2, back, ha2, hback⟩
        subst ha2
        step as ⟨a3, ha3⟩
        scalar_tac
      · simp at ho
  · exact hend

/-- Totality of the `u - (v & a_is_odd)` borrow-chain loop; the final borrow is 0/1. -/
@[step] theorem step_loop2_total (iter : core.ops.range.Range Std.Usize)
    (u v : Uint4) (a_is_odd borrow : Limb) (d : Uint4)
    (hend : iter.«end».val ≤ 4) (hb : borrow.val ≤ 1) :
    field.verified.invert.invert.step_loop2 iter u v a_is_odd borrow d
      ⦃ bo _d => bo.val ≤ 1 ⦄ := by
  unfold field.verified.invert.invert.step_loop2
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (s : (core.ops.range.Range Std.Usize) × Limb × Uint4) =>
      s.1.«end».val - s.1.start.val)
    (inv := fun s => s.1.«end».val ≤ 4 ∧ s.2.1.val ≤ 1)
  · rintro ⟨it, bor, dd⟩ ⟨hend', hb'⟩
    unfold field.verified.invert.invert.step_loop2.body
    step as ⟨o, iter1, ho, hoe⟩
    rcases o with _ | l
    · split at ho
      · simp at ho
      · simp only [WP.spec_ok] <;> scalar_tac
    · split at ho
      · next hlt =>
        obtain ⟨hosome, hst1⟩ := ho
        have hleq : l = it.start := by injection hosome
        subst hleq
        step as ⟨a1, ha1⟩
        subst ha1
        step as ⟨l1, hl1⟩
        step as ⟨a2, ha2⟩
        subst ha2
        step as ⟨l2, hl2⟩
        step as ⟨l3, hl3⟩
        step as ⟨l4, borrow1, hsub, hb1⟩
        step as ⟨a3, back, ha3, hback⟩
        subst ha3
        step as ⟨a4, ha4⟩
        scalar_tac
      · simp at ho
  · exact ⟨hend, hb⟩

/-- Totality of the low-half fused negate-and-add-modulus loop (`for l in 0..2`);
    the final carry is 0/1. -/
@[step] theorem step_loop3_total (iter : core.ops.range.Range Std.Usize)
    (u u_sub_v : Uint4) (should_negate add_two_modulus add_one_modulus carry : Limb)
    (hend : iter.«end».val ≤ 4) (hc : carry.val ≤ 1) :
    field.verified.invert.invert.step_loop3 iter u u_sub_v should_negate
      add_two_modulus add_one_modulus carry
      ⦃ _u co => co.val ≤ 1 ⦄ := by
  unfold field.verified.invert.invert.step_loop3
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (s : (core.ops.range.Range Std.Usize) × Uint4 × Limb) =>
      s.1.«end».val - s.1.start.val)
    (inv := fun s => s.1.«end».val ≤ 4 ∧ s.2.2.val ≤ 1)
  · rintro ⟨it, uu, car⟩ ⟨hend', hc'⟩
    unfold field.verified.invert.invert.step_loop3.body
    step as ⟨o, iter1, ho, hoe⟩
    rcases o with _ | l
    · split at ho
      · simp at ho
      · simp only [WP.spec_ok, WP.uncurry'_pair] <;> scalar_tac
    · split at ho
      · next hlt =>
        obtain ⟨hosome, hst1⟩ := ho
        have hleq : l = it.start := by injection hosome
        subst hleq
        step as ⟨m, hm⟩
        step as ⟨a1, ha1⟩
        subst ha1
        step as ⟨l1, hl1⟩
        step as ⟨l2, hl2⟩
        step as ⟨mx, hmx⟩
        step as ⟨a2, ha2⟩
        subst ha2
        step as ⟨l3, hl3⟩
        step as ⟨l4, hl4⟩
        step as ⟨mi, hmi⟩
        step as ⟨a3, ha3⟩
        subst ha3
        step as ⟨l5, hl5⟩
        step as ⟨l6, hl6⟩
        step as ⟨l7, hl7⟩
        step as ⟨limb, carry_bool, hadd⟩
        step as ⟨i, hi⟩
        step as ⟨a4, back, ha4, hback⟩
        subst ha4
        step as ⟨a5, ha5⟩
        have hile : i.val ≤ 1 := by rw [hi]; split <;> omega
        scalar_tac
      · simp at ho
  · exact ⟨hend, hc⟩

/-- Totality of the high-half negate-and-add-modulus loop (`for l in 2..4`). -/
@[step] theorem step_loop4_total (iter : core.ops.range.Range Std.Usize)
    (u u_sub_v : Uint4) (should_negate add_two_modulus add_one_modulus carry : Limb)
    (hend : iter.«end».val ≤ 4) (hc : carry.val ≤ 1) :
    field.verified.invert.invert.step_loop4 iter u u_sub_v should_negate
      add_two_modulus add_one_modulus carry
      ⦃ _u => True ⦄ := by
  unfold field.verified.invert.invert.step_loop4
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (s : (core.ops.range.Range Std.Usize) × Uint4 × Limb) =>
      s.1.«end».val - s.1.start.val)
    (inv := fun s => s.1.«end».val ≤ 4 ∧ s.2.2.val ≤ 1)
  · rintro ⟨it, uu, car⟩ ⟨hend', hc'⟩
    unfold field.verified.invert.invert.step_loop4.body
    step as ⟨o, iter1, ho, hoe⟩
    rcases o with _ | l
    · split at ho
      · simp at ho
      · simp only [WP.spec_ok] <;> scalar_tac
    · split at ho
      · next hlt =>
        obtain ⟨hosome, hst1⟩ := ho
        have hleq : l = it.start := by injection hosome
        subst hleq
        step as ⟨m, hm⟩
        step as ⟨a1, ha1⟩
        subst ha1
        step as ⟨l1, hl1⟩
        step as ⟨l2, hl2⟩
        step as ⟨mx, hmx⟩
        step as ⟨a2, ha2⟩
        subst ha2
        step as ⟨l3, hl3⟩
        step as ⟨l4, hl4⟩
        step as ⟨mi, hmi⟩
        step as ⟨a3, ha3⟩
        subst ha3
        step as ⟨l5, hl5⟩
        step as ⟨l6, hl6⟩
        step as ⟨l7, carry1, hadd, hc1⟩
        step as ⟨a4, back, ha4, hback⟩
        subst ha4
        step as ⟨a5, ha5⟩
        scalar_tac
      · simp at ho
  · exact ⟨hend, hc⟩

/-! ## 4-limb decomposition helpers -/

theorem Uint4.exists_four_limbs (u : Uint4) :
    ∃ x0 x1 x2 x3 : Limb, u.val = [x0, x1, x2, x3] :=
  List.length_eq_four.mp (by simpa using Aeneas.Std.Array.length_eq (a := u))

theorem Uint4.toNat_of_limbs {u : Uint4} {x0 x1 x2 x3 : Limb}
    (h : u.val = [x0, x1, x2, x3]) :
    u.toNat = x0.val + 2^64 * x1.val + 2^128 * x2.val + 2^192 * x3.val := by
  simp only [crypto_bigint.uint.Uint.toNat, h, List.foldr_cons, List.foldr_nil]
  ring

/-- The low limb of a zero `Uint4` is zero. -/
theorem Uint4.limb0_of_toNat_zero {u : Uint4} (h : u.toNat = 0) :
    u.val[(0#usize).val].val = 0 := by
  obtain ⟨x0, x1, x2, x3, hu⟩ := Uint4.exists_four_limbs u
  rw [Uint4.toNat_of_limbs hu] at h
  simp only [hu]
  simp only [show (0#usize).val = 0 from by simp, List.getElem_cons_zero]
  omega

/-- Parity of a `Uint4` value is the parity of its low limb (higher limbs weigh `2^64`). -/
theorem Uint4.toNat_mod_two_eq_limb0 (u : Uint4) :
    u.toNat % 2 = u.val[(0#usize).val].val % 2 := by
  obtain ⟨x0, x1, x2, x3, hu⟩ := Uint4.exists_four_limbs u
  rw [Uint4.toNat_of_limbs hu]
  simp only [hu, show (0#usize).val = 0 from by simp, List.getElem_cons_zero]
  omega

/-! ## Totality of `step` + zero-propagation (task item 3, totality half: proved)

`step` never fails, and on the zero GCD state (`a = 0`, reached iff `value = 0`) it keeps
`a = 0` and leaves the Bezout accumulator `v` untouched — which is what makes
`invert 0 = (0, ⊥)` provable without the congruence invariant. -/

theorem step_basic_spec (a b u v : Uint4) :
    field.verified.invert.invert.step a b u v
      ⦃ s => a.toNat = 0 → s.1.toNat = 0 ∧ s.2.2.2 = v ⦄ := by
  unfold field.verified.invert.invert.step
  step as ⟨a1, ha1⟩
  step as ⟨l, hl⟩
  rw [ha1] at hl
  step as ⟨a_is_odd, hodd, hoddbv⟩
  step as ⟨a_is_odd1, hodd1⟩
  step as ⟨borrow, hborrow⟩
  step as ⟨a_sub_b, hasb⟩
  step as ⟨i, hi⟩
  have hi4 : i.val = 4 := by rw [hi]; simp
  have hodd_le : a_is_odd.val ≤ 1 := by
    rw [hodd]
    have h1 : ((1#u64) : Std.U64).val = 1 := by simp
    simp only [UScalar.val_and, h1, Nat.and_one_is_mod]
    omega
  have hmask_odd : IsMask a_is_odd1 := isMask_of_wrapping_neg hodd_le hodd1
  step as ⟨borrow1, a_sub_b1, hb1le⟩
  step as ⟨a_lt_b, hltb⟩
  have hmask_ltb : IsMask a_lt_b := isMask_of_wrapping_neg hb1le hltb
  step as ⟨both, hboth⟩
  have hmask_both : IsMask both := isMask_and hmask_odd hmask_ltb hboth
  step with select_spec as ⟨b1, hb1sel⟩
  step as ⟨l1, hl1⟩
  step as ⟨carry, hcarry⟩
  step as ⟨a_diff_b⟩
  step with select_spec as ⟨a2, ha2sel⟩
  step as ⟨borrow2, u_sub_v, hb2le⟩
  step as ⟨u_sub_v_neg, husvn⟩
  step as ⟨should_negate, hsn⟩
  have hmask_sn : IsMask should_negate := isMask_and hmask_odd hmask_ltb hsn
  step as ⟨v_u, hvu⟩
  step as ⟨a3, ha3⟩
  step as ⟨l2, hl2⟩
  step as ⟨l3, hl3⟩
  step as ⟨result_is_odd, hrio⟩
  step as ⟨l4, hl4⟩
  step as ⟨add_two, hat⟩
  step as ⟨add_one, hao⟩
  step as ⟨carry1, hcar1⟩
  have hcar1_le : carry1.val ≤ 1 := by
    rw [hcar1, hl1]
    exact Nat.and_le_left
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = 2 := by rw [hi1]; simp
  step as ⟨u1, carry2, hc2le⟩
  step as ⟨u2⟩
  step with select_spec as ⟨v1, hv1sel⟩
  step as ⟨a7, ha7⟩
  step as ⟨u4, hu4⟩
  -- final goal: the zero-propagation implication
  intro ha0
  have hl0 : l.val = 0 := by
    rw [hl]
    exact Uint4.limb0_of_toNat_zero ha0
  have hodd0 : a_is_odd.val = 0 := by
    rw [hodd]
    simp only [UScalar.val_and]
    rw [hl0]
    simp
  have hodd1_0 : a_is_odd1.val = 0 := by
    rw [hodd1, hodd0]
    omega
  have hboth0 : both.val = 0 := by
    rw [hboth, hodd1_0]
    simp [Nat.zero_and]
  constructor
  · -- a component: a7 = (select a a_diff_b a_is_odd1) >> 1 = a >> 1 = 0
    rw [ha2sel, if_pos hodd1_0] at ha7
    rw [ha7, ha0]
    simp
  · -- v component: v1 = select v u both = v
    rw [hv1sel, if_pos hboth0]

/-- `step` never fails (task item 3, totality). -/
theorem step_total (a b u v : Uint4) :
    ∃ s, field.verified.invert.invert.step a b u v = ok s :=
  match WP.spec_imp_exists (step_basic_spec a b u v) with
  | ⟨s, heq, _⟩ => ⟨s, heq⟩

/-! ## Local spec for `red1` (conditional subtraction of `p`)

`red1_ok` (input `< 2p`) is the contract of a sibling Spec file; `invert` only needs the
inputs-`≤ p` case, proved here self-containedly so this file does not depend on it. -/

theorem sub_value_spec (a b : Uint4) :
    field.verified.sub_value a b
      ⦃ d bo => (if a.toNat < b.toNat
                 then d.toNat + b.toNat = a.toNat + 2^256 ∧ bo.val = 2^64 - 1
                 else d.toNat + b.toNat = a.toNat ∧ bo.val = 0) ⦄ := by
  unfold field.verified.sub_value
  step as ⟨z, hz⟩
  have hsbb := Uint.sbb_spec a b z
  apply WP.spec_mono hsbb
  rintro ⟨d, bo⟩ h
  simp only [WP.uncurry'_pair] at h ⊢
  rw [hz] at h
  simp only [Nat.zero_shiftRight, Nat.add_zero] at h
  rw [show (64 * ((4#usize) : Std.Usize).val) = 256 from by simp] at h
  exact h

/-- The conditional-move loop of `red1`: same shape as `select_loop`. -/
theorem red1_loop_spec (a reduced : Uint4) (borrow : Limb) (hc : IsMask borrow)
    (iter : core.ops.range.Range Std.Usize) (out : Uint4)
    (hend : iter.«end» = 4#usize) (hstart : iter.start.val ≤ 4)
    (hres : ∀ l : ℕ, l < iter.start.val →
      out[l]! = (if borrow.val = 0 then reduced else a)[l]!) :
    field.verified.red1_loop iter a reduced borrow out
      ⦃ r => r = if borrow.val = 0 then reduced else a ⦄ := by
  unfold field.verified.red1_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (s : (core.ops.range.Range Std.Usize) × Uint4) =>
      s.1.«end».val - s.1.start.val)
    (inv := fun s =>
      s.1.«end» = 4#usize ∧ s.1.start.val ≤ 4 ∧
      ∀ l : ℕ, l < s.1.start.val →
        s.2[l]! = (if borrow.val = 0 then reduced else a)[l]!)
  · rintro ⟨it, r⟩ ⟨hend', hstart', hres'⟩
    try simp only at hend' hstart' hres'
    unfold field.verified.red1_loop.body
    step as ⟨o, iter1, ho, hoe⟩
    have hendval : it.«end».val = 4 := by rw [hend']; simp
    rcases o with _ | l
    · split at ho
      · simp at ho
      · next hge =>
        try simp only [WP.spec_ok]
        have hstart4 : it.start.val = 4 := by omega
        apply Subtype.ext
        apply List.ext_getElem! (by simp [Aeneas.Std.Array.length_eq])
        intro n
        by_cases hn : n < 4
        · have := hres' n (by omega)
          simpa [Array.getElem!_Nat_eq] using this
        · rw [getElem!_neg _ _ (by scalar_tac), getElem!_neg _ _ (by scalar_tac)]
    · split at ho
      · next hlt =>
        obtain ⟨hosome, hst1⟩ := ho
        have hleq : l = it.start := by injection hosome
        subst hleq
        have hbound : it.start.val < 4 := by omega
        step as ⟨a1, ha1⟩
        subst ha1
        step as ⟨l1, hl1⟩
        step as ⟨a2, ha2⟩
        subst ha2
        step as ⟨l2, hl2⟩
        step with select_word_spec as ⟨l3, hl3⟩
        step as ⟨a3, back, ha3, hback⟩
        subst ha3
        step as ⟨a4, ha4⟩
        subst ha4
        simp only [hback, WP.spec_ok]
        have hoev : iter1.«end».val = 4 := by rw [hoe, hend']; simp
        refine ⟨by rw [hoe, hend'], by omega, ?_, by omega⟩
        intro k hk
        rw [hst1] at hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
        · rw [Array.getElem!_Nat_set_ne _ _ _ _ (by omega)]
          exact hres' k hk
        · subst hk
          rw [Array.getElem!_Nat_set_eq _ _ _ _
            ⟨rfl, by simp [Aeneas.Std.Array.length_eq, hbound]⟩]
          rw [hl3, hl1, hl2]
          split <;> simp [Array.getElem!_Nat_eq, getElem!_pos, Aeneas.Std.Array.length_eq,
            hbound]
      · simp at ho
  · exact ⟨hend, hstart, hres⟩

/-- `red1` reduces any value `< 2p` to its canonical representative. -/
theorem red1_spec (a : Uint4) (h2p : a.toNat < 2 * p) :
    field.verified.red1 a ⦃ r => r.toNat = a.toNat % p ⦄ := by
  unfold field.verified.red1
  step as ⟨m, hm⟩
  step with sub_value_spec as ⟨reduced, borrow, hsub⟩
  rw [hm] at hsub
  step as ⟨out, hout⟩
  step as ⟨i, hi⟩
  have hmask : IsMask borrow := by
    unfold IsMask
    split at hsub
    · right; exact hsub.2
    · left; exact hsub.2
  have hloop := red1_loop_spec a reduced borrow hmask { start := 0#usize, «end» := i }
    out hi (by simp) (by simp)
  apply WP.spec_mono hloop
  intro r hr
  rw [hr]
  split at hsub
  · next hlt =>
    rw [if_neg (by rw [hsub.2]; norm_num)]
    exact (Nat.mod_eq_of_lt hlt).symm
  · next hge =>
    rw [if_pos hsub.2]
    have heq : reduced.toNat + p = a.toNat := hsub.1
    have hred : reduced.toNat < p := by omega
    rw [← heq, Nat.add_mod_right]
    exact (Nat.mod_eq_of_lt hred).symm

/-! ## Local spec for `is_zero` -/

theorem nat_or_eq_zero {x y : ℕ} : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hx : x ≤ x ||| y := Nat.left_le_or
    have hy : y ≤ x ||| y := Nat.right_le_or
    omega
  · rintro ⟨rfl, rfl⟩
    simp

theorem is_zero_loop_spec (value : Uint4) (iter : core.ops.range.Range Std.Usize)
    (all : Limb) (hend : iter.«end» = 4#usize) (hstart : iter.start.val ≤ 4)
    (hall : all.val = 0 ↔ ∀ l : ℕ, l < iter.start.val → value.val[l]!.val = 0) :
    field.verified.is_zero_loop iter value all
      ⦃ r => r.val = 0 ↔ value.toNat = 0 ⦄ := by
  unfold field.verified.is_zero_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (s : (core.ops.range.Range Std.Usize) × Uint4 × Limb) =>
      s.1.«end».val - s.1.start.val)
    (inv := fun s =>
      s.1.«end» = 4#usize ∧ s.1.start.val ≤ 4 ∧ s.2.1 = value ∧
      (s.2.2.val = 0 ↔ ∀ l : ℕ, l < s.1.start.val → value.val[l]!.val = 0))
  · rintro ⟨it, val1, acc⟩ ⟨hend', hstart', hval', hacc'⟩
    try simp only at hend' hstart' hval' hacc'
    unfold field.verified.is_zero_loop.body
    step as ⟨o, iter1, ho, hoe⟩
    have hendval : it.«end».val = 4 := by rw [hend']; simp
    rcases o with _ | l
    · split at ho
      · simp at ho
      · next hge =>
        try simp only [WP.spec_ok]
        have hstart4 : it.start.val = 4 := by omega
        rw [hstart4] at hacc'
        obtain ⟨x0, x1, x2, x3, hval⟩ := Uint4.exists_four_limbs value
        rw [hacc', Uint4.toNat_of_limbs hval]
        constructor
        · intro h
          have h0 := h 0 (by omega)
          have h1 := h 1 (by omega)
          have h2 := h 2 (by omega)
          have h3 := h 3 (by omega)
          rw [hval] at h0 h1 h2 h3
          simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at h0 h1 h2 h3
          omega
        · intro h l hl
          rw [hval]
          interval_cases l <;>
            simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] <;> omega
    · split at ho
      · next hlt =>
        obtain ⟨hosome, hst1⟩ := ho
        have hleq : l = it.start := by injection hosome
        subst hleq
        have hbound : it.start.val < 4 := by omega
        step as ⟨aa, haa⟩
        step as ⟨l1, hl1⟩
        step as ⟨all1, hall1⟩
        have hl1' : l1.val = value.val[it.start.val]!.val := by
          rw [hl1, haa, hval']
          rw [getElem!_pos _ _ (by scalar_tac)]
        refine ⟨by rw [hoe, hend'], by scalar_tac, hval', ?_, by scalar_tac⟩
        rw [hall1, nat_or_eq_zero, hacc']
        constructor
        · rintro ⟨hprev, hcur⟩ l hl
          rw [hst1] at hl
          rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
          · exact hprev l hl
          · subst hl
            rw [← hl1']
            exact hcur
        · intro h
          refine ⟨fun l hl => h l (by omega), ?_⟩
          rw [hl1']
          exact h it.start.val (by omega)
      · simp at ho
  · exact ⟨hend, hstart, rfl, hall⟩

theorem is_zero_spec (value : Uint4) :
    field.verified.is_zero value ⦃ c => c = true ↔ value.toNat = 0 ⦄ := by
  unfold field.verified.is_zero
  step as ⟨all, hall⟩
  step as ⟨i, hi⟩
  have hloop := is_zero_loop_spec value { start := 0#usize, «end» := i } all hi
    (by simp) (by simp [hall])
  step with hloop as ⟨all1, hall1⟩
  step as ⟨c, hc⟩
  rw [hc, hall]
  exact hall1

theorem ffield_is_zero_spec (value : Uint4) :
    field.HelioseleneField.Insts.FfField.is_zero value
      ⦃ c => c = true ↔ value.toNat = 0 ⦄ := by
  unfold field.HelioseleneField.Insts.FfField.is_zero
  exact is_zero_spec value

/-! ## Value-level specs of the five inner loops of `step`

The `@[step]`-tagged totality lemmas above remain in place for `step_basic_spec`;
`step_congruence` instead drives the loop calls with the exact-value lemmas below
(brute 4- resp. 2-iteration unrolls in the style of `Reduction.lean`). -/

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

private theorem spec_ok_of {α : Type u} {x : α} {post : α → Prop} (h : post x) :
    Aeneas.Std.WP.spec (ok x) post := (Aeneas.Std.WP.spec_ok x).mpr h

/-- Value-level spec of the `a - b` borrow chain (`step_loop0`):
    exact 256-bit identity plus 0/1 borrow. -/
theorem step_loop0_value_spec (iter : core.ops.range.Range Std.Usize)
    (a b : Uint4) (borrow : Limb) (d : Uint4)
    (hs : iter.start.val = 0) (he : iter.«end».val = 4)
    (hbor : borrow.val = 0) :
    field.verified.invert.invert.step_loop0 iter a b borrow d
      ⦃ bo o => bo.val ≤ 1 ∧ o.toNat + b.toNat = a.toNat + 2^256 * bo.val ⦄ := by
  obtain ⟨a0, a1, a2, a3, haval⟩ := Uint4.exists_four_limbs a
  obtain ⟨b0, b1, b2, b3, hbval⟩ := Uint4.exists_four_limbs b
  obtain ⟨z0, z1, z2, z3, hzval⟩ := Uint4.exists_four_limbs d
  unfold field.verified.invert.invert.step_loop0
  -- iteration 1 : l = 0
  apply loop_step
  unfold field.verified.invert.invert.step_loop0.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨ra, hra⟩
  step as ⟨l1, hl1⟩
  step as ⟨rb, hrb⟩
  step as ⟨l2, hl2⟩
  step as ⟨w0, c1, hsub0, hc1⟩
  step as ⟨od, back, hod, hback⟩
  step as ⟨o1, ho1⟩
  simp only [hra, haval, hs] at hl1
  simp at hl1
  simp only [hrb, hbval, hs] at hl2
  simp at hl2
  have hoval1 : o1.val = [w0, z1, z2, z3] := by
    rw [ho1, Array.set_val_eq, hod, hzval, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback]
  -- iteration 2 : l = 1
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨ra2, hra2⟩
  step as ⟨l3, hl3⟩
  step as ⟨rb2, hrb2⟩
  step as ⟨l4, hl4⟩
  step as ⟨w1, c2, hsub1, hc2⟩
  step as ⟨od2, back2, hod2, hback2⟩
  step as ⟨o2', ho2'⟩
  simp only [hra2, haval, hs1, hs] at hl3
  simp at hl3
  simp only [hrb2, hbval, hs1, hs] at hl4
  simp at hl4
  have hoval2 : o2'.val = [w0, w1, z2, z3] := by
    rw [ho2', Array.set_val_eq, hod2, hoval1, hs1, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback2]
  -- iteration 3 : l = 2
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨ra3, hra3⟩
  step as ⟨l5, hl5⟩
  step as ⟨rb3, hrb3⟩
  step as ⟨l6, hl6⟩
  step as ⟨w2, c3, hsub2, hc3⟩
  step as ⟨od3, back3, hod3, hback3⟩
  step as ⟨o3', ho3'⟩
  simp only [hra3, haval, hs2, hs1, hs] at hl5
  simp at hl5
  simp only [hrb3, hbval, hs2, hs1, hs] at hl6
  simp at hl6
  have hoval3 : o3'.val = [w0, w1, w2, z3] := by
    rw [ho3', Array.set_val_eq, hod3, hoval2, hs2, hs1, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback3]
  -- iteration 4 : l = 3
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter3 (by
      simp only [he3, he2, he1]; omega))
  intro ⟨o4, iter4⟩ ⟨ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨ra4, hra4⟩
  step as ⟨l7, hl7⟩
  step as ⟨rb4, hrb4⟩
  step as ⟨l8, hl8⟩
  step as ⟨w3, c4, hsub3, hc4⟩
  step as ⟨od4, back4, hod4, hback4⟩
  step as ⟨o4', ho4'⟩
  simp only [hra4, haval, hs3, hs2, hs1, hs] at hl7
  simp at hl7
  simp only [hrb4, hbval, hs3, hs2, hs1, hs] at hl8
  simp at hl8
  have hoval4 : o4'.val = [w0, w1, w2, w3] := by
    rw [ho4', Array.set_val_eq, hod4, hoval3, hs3, hs2, hs1, hs]
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
  apply spec_ok_of
  simp only [WP.uncurry'_pair]
  constructor
  · exact hc4
  · have hosum := Uint4.toNat_of_limbs hoval4
    have hasum := Uint4.toNat_of_limbs haval
    have hbsum := Uint4.toNat_of_limbs hbval
    rw [hl1, hl2] at hsub0
    rw [hl3, hl4] at hsub1
    rw [hl5, hl6] at hsub2
    rw [hl7, hl8] at hsub3
    have hw0 : (w0).val < 2^64 := w0.hBounds
    have hw1 : (w1).val < 2^64 := w1.hBounds
    have hw2 : (w2).val < 2^64 := w2.hBounds
    have hw3 : (w3).val < 2^64 := w3.hBounds
    rw [hosum, hasum, hbsum]
    omega

/-- Value-level spec of the `u - (v & a_is_odd)` borrow chain (`step_loop2`). -/
theorem step_loop2_value_spec (iter : core.ops.range.Range Std.Usize)
    (u v : Uint4) (m borrow : Limb) (d : Uint4)
    (hs : iter.start.val = 0) (he : iter.«end».val = 4)
    (hm : IsMask m) (hbor : borrow.val = 0) :
    field.verified.invert.invert.step_loop2 iter u v m borrow d
      ⦃ bo o => bo.val ≤ 1 ∧
          o.toNat + (if m.val = 0 then 0 else v.toNat)
            = u.toNat + 2^256 * bo.val ⦄ := by
  obtain ⟨a0, a1, a2, a3, haval⟩ := Uint4.exists_four_limbs u
  obtain ⟨b0, b1, b2, b3, hbval⟩ := Uint4.exists_four_limbs v
  obtain ⟨z0, z1, z2, z3, hzval⟩ := Uint4.exists_four_limbs d
  unfold field.verified.invert.invert.step_loop2
  -- iteration 1 : l = 0
  apply loop_step
  unfold field.verified.invert.invert.step_loop2.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨ra, hra⟩
  step as ⟨l1, hl1⟩
  step as ⟨rb, hrb⟩
  step as ⟨l2, hl2⟩
  step as ⟨l2m, hl2m⟩
  step as ⟨w0, c1, hsub0, hc1⟩
  step as ⟨od, back, hod, hback⟩
  step as ⟨o1, ho1⟩
  simp only [hra, haval, hs] at hl1
  simp at hl1
  simp only [hrb, hbval, hs] at hl2
  simp at hl2
  have hoval1 : o1.val = [w0, z1, z2, z3] := by
    rw [ho1, Array.set_val_eq, hod, hzval, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback]
  -- iteration 2 : l = 1
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨ra2, hra2⟩
  step as ⟨l3, hl3⟩
  step as ⟨rb2, hrb2⟩
  step as ⟨l4, hl4⟩
  step as ⟨l4m, hl4m⟩
  step as ⟨w1, c2, hsub1, hc2⟩
  step as ⟨od2, back2, hod2, hback2⟩
  step as ⟨o2', ho2'⟩
  simp only [hra2, haval, hs1, hs] at hl3
  simp at hl3
  simp only [hrb2, hbval, hs1, hs] at hl4
  simp at hl4
  have hoval2 : o2'.val = [w0, w1, z2, z3] := by
    rw [ho2', Array.set_val_eq, hod2, hoval1, hs1, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback2]
  -- iteration 3 : l = 2
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨ra3, hra3⟩
  step as ⟨l5, hl5⟩
  step as ⟨rb3, hrb3⟩
  step as ⟨l6, hl6⟩
  step as ⟨l6m, hl6m⟩
  step as ⟨w2, c3, hsub2, hc3⟩
  step as ⟨od3, back3, hod3, hback3⟩
  step as ⟨o3', ho3'⟩
  simp only [hra3, haval, hs2, hs1, hs] at hl5
  simp at hl5
  simp only [hrb3, hbval, hs2, hs1, hs] at hl6
  simp at hl6
  have hoval3 : o3'.val = [w0, w1, w2, z3] := by
    rw [ho3', Array.set_val_eq, hod3, hoval2, hs2, hs1, hs]
    rfl
  simp only [Aeneas.Std.WP.spec_ok, hback3]
  -- iteration 4 : l = 3
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter3 (by
      simp only [he3, he2, he1]; omega))
  intro ⟨o4, iter4⟩ ⟨ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨ra4, hra4⟩
  step as ⟨l7, hl7⟩
  step as ⟨rb4, hrb4⟩
  step as ⟨l8, hl8⟩
  step as ⟨l8m, hl8m⟩
  step as ⟨w3, c4, hsub3, hc4⟩
  step as ⟨od4, back4, hod4, hback4⟩
  step as ⟨o4', ho4'⟩
  simp only [hra4, haval, hs3, hs2, hs1, hs] at hl7
  simp at hl7
  simp only [hrb4, hbval, hs3, hs2, hs1, hs] at hl8
  simp at hl8
  have hoval4 : o4'.val = [w0, w1, w2, w3] := by
    rw [ho4', Array.set_val_eq, hod4, hoval3, hs3, hs2, hs1, hs]
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
  apply spec_ok_of
  simp only [WP.uncurry'_pair]
  constructor
  · exact hc4
  · have hosum := Uint4.toNat_of_limbs hoval4
    have hasum := Uint4.toNat_of_limbs haval
    have hbsum := Uint4.toNat_of_limbs hbval
    rw [hl1] at hsub0
    rw [hl3] at hsub1
    rw [hl5] at hsub2
    rw [hl7] at hsub3
    rw [hl2m, hl2] at hsub0
    rw [hl4m, hl4] at hsub1
    rw [hl6m, hl6] at hsub2
    rw [hl8m, hl8] at hsub3
    have hw0 : (w0).val < 2^64 := w0.hBounds
    have hw1 : (w1).val < 2^64 := w1.hBounds
    have hw2 : (w2).val < 2^64 := w2.hBounds
    have hw3 : (w3).val < 2^64 := w3.hBounds
    rcases hm with hm0 | hmo
    · rw [hm0, Nat.and_zero] at hsub0 hsub1 hsub2 hsub3
      rw [if_pos hm0]
      rw [hosum, hasum]
      omega
    · have handm : ∀ x : Limb, x.val &&& (2^64 - 1) = x.val := fun x =>
        Nat.and_two_pow_sub_one_of_lt_two_pow (show x.val < 2^64 from x.hBounds)
      rw [hmo] at hsub0 hsub1 hsub2 hsub3
      rw [handm b0] at hsub0
      rw [handm b1] at hsub1
      rw [handm b2] at hsub2
      rw [handm b3] at hsub3
      rw [if_neg (by rw [hmo]; norm_num)]
      rw [hosum, hasum, hbsum]
      omega

/-- Normalize the `overflowing_add` step-pure hypothesis plus the `FromU64Bool`
    conversion into one exact full-adder identity with a 0/1 carry. -/
private theorem norm_oadd {l2 car limb : Std.U64} {carry_bool : Bool} {i : Std.U64}
    (hadd : if l2.val + car.val > UScalar.max UScalarTy.U64
            then limb.val + U64.size = l2.val + car.val ∧ carry_bool = true
            else limb.val = l2.val + car.val ∧ carry_bool = false)
    (hi : i.val = if carry_bool then 1 else 0) :
    limb.val + 2^64 * i.val = l2.val + car.val ∧ i.val ≤ 1 := by
  have hsz : U64.size = 2^64 := by rw [U64.size_def, U64.numBits_def]; rfl
  split at hadd
  · obtain ⟨he, hcb⟩ := hadd
    subst hcb
    rw [if_pos rfl] at hi
    rw [hsz] at he
    omega
  · obtain ⟨he, hcb⟩ := hadd
    subst hcb
    rw [if_neg Bool.false_ne_true] at hi
    omega

/-- XOR with the all-ones mask is complement, at the `.val` level. -/
private theorem xor_allOnes_val (x m : Std.U64) (hm : m.val = 2^64 - 1) :
    x.val ^^^ m.val = 2^64 - 1 - x.val := by
  have hmbv : m.bv = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq
    simpa using hm
  have h1 : x.val ^^^ m.val = (x.bv ^^^ m.bv).toNat := (BitVec.toNat_xor ..).symm
  rw [h1, hmbv, BitVec.xor_allOnes, BitVec.toNat_not]
  rfl

/-- Value-level spec of the conditional-negation chain (`step_loop1`):
    identity under the zero mask, exact two's complement under the all-ones mask. -/
theorem step_loop1_value_spec (iter : core.ops.range.Range Std.Usize)
    (x : Uint4) (mask carry : Limb) (d : Uint4)
    (hs : iter.start.val = 0) (he : iter.«end».val = 4)
    (hm : IsMask mask) (hc : carry.val = if mask.val = 0 then 0 else 1) :
    field.verified.invert.invert.step_loop1 iter x mask carry d
      ⦃ o => (mask.val = 0 → o.toNat = x.toNat) ∧
             (mask.val ≠ 0 → (x.toNat = 0 ∧ o.toNat = 0) ∨
                             o.toNat + x.toNat = 2^256) ⦄ := by
  obtain ⟨a0, a1, a2, a3, haval⟩ := Uint4.exists_four_limbs x
  obtain ⟨z0, z1, z2, z3, hzval⟩ := Uint4.exists_four_limbs d
  unfold field.verified.invert.invert.step_loop1
  -- iteration 1 : l = 0
  apply loop_step
  unfold field.verified.invert.invert.step_loop1.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨ra, hra⟩
  step as ⟨l1, hl1⟩
  step as ⟨l2, hl2⟩
  step as ⟨w0, cb0, hadd0⟩
  step as ⟨i0, hi0⟩
  step as ⟨od, back, hod, hback⟩
  step as ⟨o1, ho1⟩
  obtain ⟨hstep0, hi0le⟩ := norm_oadd hadd0 hi0
  simp only [hra, haval, hs] at hl1
  simp at hl1
  have hoval1 : o1.val = [w0, z1, z2, z3] := by
    rw [ho1, Array.set_val_eq, hod, hzval, hs]
    rfl
  simp only [hback]
  -- iteration 2 : l = 1
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨ra2, hra2⟩
  step as ⟨l3, hl3⟩
  step as ⟨l4, hl4⟩
  step as ⟨w1, cb1, hadd1⟩
  step as ⟨i1, hi1⟩
  step as ⟨od2, back2, hod2, hback2⟩
  step as ⟨o2', ho2'⟩
  obtain ⟨hstep1, hi1le⟩ := norm_oadd hadd1 hi1
  simp only [hra2, haval, hs1, hs] at hl3
  simp at hl3
  have hoval2 : o2'.val = [w0, w1, z2, z3] := by
    rw [ho2', Array.set_val_eq, hod2, hoval1, hs1, hs]
    rfl
  simp only [hback2]
  -- iteration 3 : l = 2
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨ra3, hra3⟩
  step as ⟨l5, hl5⟩
  step as ⟨l6, hl6⟩
  step as ⟨w2, cb2, hadd2⟩
  step as ⟨i2, hi2⟩
  step as ⟨od3, back3, hod3, hback3⟩
  step as ⟨o3', ho3'⟩
  obtain ⟨hstep2, hi2le⟩ := norm_oadd hadd2 hi2
  simp only [hra3, haval, hs2, hs1, hs] at hl5
  simp at hl5
  have hoval3 : o3'.val = [w0, w1, w2, z3] := by
    rw [ho3', Array.set_val_eq, hod3, hoval2, hs2, hs1, hs]
    rfl
  simp only [hback3]
  -- iteration 4 : l = 3
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter3 (by
      simp only [he3, he2, he1]; omega))
  intro ⟨o4, iter4⟩ ⟨ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨ra4, hra4⟩
  step as ⟨l7, hl7⟩
  step as ⟨l8, hl8⟩
  step as ⟨w3, cb3, hadd3⟩
  step as ⟨i3, hi3⟩
  step as ⟨od4, back4, hod4, hback4⟩
  step as ⟨o4', ho4'⟩
  obtain ⟨hstep3, hi3le⟩ := norm_oadd hadd3 hi3
  simp only [hra4, haval, hs3, hs2, hs1, hs] at hl7
  simp at hl7
  have hoval4 : o4'.val = [w0, w1, w2, w3] := by
    rw [ho4', Array.set_val_eq, hod4, hoval3, hs3, hs2, hs1, hs]
    rfl
  simp only [hback4]
  -- iteration 5 : exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter4 (by
      simp only [he4, he3, he2, he1]; omega))
  intro ⟨o5, iter5⟩ ⟨ho5, hi5⟩
  simp only [ho5]
  apply spec_ok_of
  have hosum := Uint4.toNat_of_limbs hoval4
  have hasum := Uint4.toNat_of_limbs haval
  rw [hl2, hl1] at hstep0
  rw [hl4, hl3] at hstep1
  rw [hl6, hl5] at hstep2
  rw [hl8, hl7] at hstep3
  have hw0 : (w0).val < 2^64 := w0.hBounds
  have hw1 : (w1).val < 2^64 := w1.hBounds
  have hw2 : (w2).val < 2^64 := w2.hBounds
  have hw3 : (w3).val < 2^64 := w3.hBounds
  have ha0b : (a0).val < 2^64 := a0.hBounds
  have ha1b : (a1).val < 2^64 := a1.hBounds
  have ha2b : (a2).val < 2^64 := a2.hBounds
  have ha3b : (a3).val < 2^64 := a3.hBounds
  constructor
  · intro hm0
    rw [hm0, Nat.xor_zero] at hstep0 hstep1 hstep2 hstep3
    rw [hm0, if_pos rfl] at hc
    rw [hosum, hasum]
    omega
  · intro hmne
    have hmo : mask.val = 2^64 - 1 := by
      rcases hm with h | h
      · exact absurd h hmne
      · exact h
    rw [xor_allOnes_val a0 mask hmo] at hstep0
    rw [xor_allOnes_val a1 mask hmo] at hstep1
    rw [xor_allOnes_val a2 mask hmo] at hstep2
    rw [xor_allOnes_val a3 mask hmo] at hstep3
    rw [hmo] at hc
    rw [if_neg (by norm_num)] at hc
    rw [hosum, hasum]
    omega

/-- Value-level spec of the low half of the fused negate-and-add-modulus chain
    (`step_loop3`, limbs 0 and 1): writes the two low limbs of `u` and produces
    exactly `T_lo + M_lo + carry` where `T_lo` is the (conditionally complemented)
    low half of `u_sub_v` and `M_lo` is the masked low half of `p`, `2p` or `0`. -/
theorem step_loop3_value_spec (iter : core.ops.range.Range Std.Usize)
    (u u_sub_v : Uint4) (N A2 A1 carry : Limb)
    (hs : iter.start.val = 0) (he : iter.«end».val = 2)
    (hN : IsMask N) (hA2 : IsMask A2) (hA1 : IsMask A1)
    (hsub : A2.val ≠ 0 → A1.val ≠ 0)
    (hc : carry.val = if N.val = 0 then 0 else 1) :
    field.verified.invert.invert.step_loop3 iter u u_sub_v N A2 A1 carry
      ⦃ o co => co.val ≤ 1 ∧ ∃ w0 w1 : Limb,
          o.val = [w0, w1, u.val[2]!, u.val[3]!] ∧
          w0.val + 2^64 * w1.val + 2^128 * co.val
            = (if N.val = 0
               then u_sub_v.val[0]!.val + 2^64 * u_sub_v.val[1]!.val
               else 2^128 - 1 - (u_sub_v.val[0]!.val + 2^64 * u_sub_v.val[1]!.val))
              + (if A1.val = 0 then 0
                 else if A2.val = 0 then p % 2^128 else (2 * p) % 2^128)
              + carry.val ⦄ := by
  obtain ⟨s0, s1, s2, s3, hsval⟩ := Uint4.exists_four_limbs u_sub_v
  obtain ⟨z0, z1, z2, z3, hzval⟩ := Uint4.exists_four_limbs u
  have hp : p = 0x7ffffffffffffffffffffffffffffffff735481d1969f317f9850b68df11df53 := by
    norm_num [p]
  have hpx : p ^^^ 2 * p
      = 0x80000000000000000000000000000000195fd8272bba15380a8f1db9613261f5 := by decide
  unfold field.verified.invert.invert.step_loop3
  -- iteration 1 : l = 0
  apply loop_step
  unfold field.verified.invert.invert.step_loop3.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨mo, hmo⟩
  step as ⟨ma, hma⟩
  step as ⟨l1, hl1⟩
  step as ⟨l2, hl2⟩
  step as ⟨mx, hmx⟩
  step as ⟨xa, hxa⟩
  step as ⟨l3, hl3⟩
  step as ⟨l4, hl4⟩
  step as ⟨mi0, hmi0⟩
  step as ⟨sa, hsa⟩
  step as ⟨l5, hl5⟩
  step as ⟨l6, hl6⟩
  step as ⟨l7, hl7⟩
  step as ⟨w0, cb0, hadd0⟩
  step as ⟨i0, hi0⟩
  step as ⟨ua, back, hua, hback⟩
  step as ⟨o1, ho1⟩
  obtain ⟨hstep0, hi0le⟩ := norm_oadd hadd0 hi0
  -- resolve the two constants' limb 0
  obtain ⟨q0, q1, q2, q3, hqv⟩ := Uint4.exists_four_limbs mo
  have hq0 : q0.val = 0xf9850b68df11df53 := by
    have hsum := Uint4.toNat_of_limbs hqv
    rw [hmo, hp] at hsum
    have h0 : (q0).val < 2^64 := q0.hBounds
    have h1 : (q1).val < 2^64 := q1.hBounds
    have h2 : (q2).val < 2^64 := q2.hBounds
    have h3 : (q3).val < 2^64 := q3.hBounds
    omega
  obtain ⟨x0, x1, x2, x3, hxv⟩ := Uint4.exists_four_limbs mx
  have hx0 : x0.val = 0x0a8f1db9613261f5 := by
    have hsum := Uint4.toNat_of_limbs hxv
    rw [hmx, hpx] at hsum
    have h0 : (x0).val < 2^64 := x0.hBounds
    have h1 : (x1).val < 2^64 := x1.hBounds
    have h2 : (x2).val < 2^64 := x2.hBounds
    have h3 : (x3).val < 2^64 := x3.hBounds
    omega
  simp only [hma, hqv, hs] at hl1
  simp at hl1
  simp only [hxa, hxv, hs] at hl3
  simp at hl3
  simp only [hsa, hsval, hs] at hl5
  simp at hl5
  have hoval1 : o1.val = [w0, z1, z2, z3] := by
    rw [ho1, Array.set_val_eq, hua, hzval, hs]
    rfl
  simp only [hback]
  -- iteration 2 : l = 1
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨mo', hmo'⟩
  step as ⟨ma', hma'⟩
  step as ⟨l1', hl1'⟩
  step as ⟨l2', hl2'⟩
  step as ⟨mx', hmx'⟩
  step as ⟨xa', hxa'⟩
  step as ⟨l3', hl3'⟩
  step as ⟨l4', hl4'⟩
  step as ⟨mi1, hmi1⟩
  step as ⟨sa', hsa'⟩
  step as ⟨l5', hl5'⟩
  step as ⟨l6', hl6'⟩
  step as ⟨l7', hl7'⟩
  step as ⟨w1, cb1, hadd1⟩
  step as ⟨i1, hi1⟩
  step as ⟨ua', back', hua', hback'⟩
  step as ⟨o2', ho2'⟩
  obtain ⟨hstep1, hi1le⟩ := norm_oadd hadd1 hi1
  obtain ⟨q0', q1', q2', q3', hqv'⟩ := Uint4.exists_four_limbs mo'
  have hq1 : q1'.val = 0xf735481d1969f317 := by
    have hsum := Uint4.toNat_of_limbs hqv'
    rw [hmo', hp] at hsum
    have h0 : (q0').val < 2^64 := q0'.hBounds
    have h1 : (q1').val < 2^64 := q1'.hBounds
    have h2 : (q2').val < 2^64 := q2'.hBounds
    have h3 : (q3').val < 2^64 := q3'.hBounds
    omega
  obtain ⟨x0', x1', x2', x3', hxv'⟩ := Uint4.exists_four_limbs mx'
  have hx1 : x1'.val = 0x195fd8272bba1538 := by
    have hsum := Uint4.toNat_of_limbs hxv'
    rw [hmx', hpx] at hsum
    have h0 : (x0').val < 2^64 := x0'.hBounds
    have h1 : (x1').val < 2^64 := x1'.hBounds
    have h2 : (x2').val < 2^64 := x2'.hBounds
    have h3 : (x3').val < 2^64 := x3'.hBounds
    omega
  simp only [hma', hqv', hs1, hs] at hl1'
  simp at hl1'
  simp only [hxa', hxv', hs1, hs] at hl3'
  simp at hl3'
  simp only [hsa', hsval, hs1, hs] at hl5'
  simp at hl5'
  have hoval2 : o2'.val = [w0, w1, z2, z3] := by
    rw [ho2', Array.set_val_eq, hua', hoval1, hs1, hs]
    rfl
  simp only [hback']
  -- iteration 3 : exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hi3⟩
  simp only [ho3]
  apply spec_ok_of
  simp only [WP.uncurry'_pair]
  -- assemble
  rw [hl1, hq0] at hl2
  rw [hl3, hx0] at hl4
  rw [hl1', hq1] at hl2'
  rw [hl3', hx1] at hl4'
  rw [hl2, hl4] at hmi0
  rw [hl2', hl4'] at hmi1
  rw [hmi0] at hl7
  rw [hmi1] at hl7'
  rw [hl5] at hl6
  rw [hl5'] at hl6'
  rw [hl6, hl7] at hstep0
  rw [hl6', hl7'] at hstep1
  have hs0b : (s0).val < 2^64 := s0.hBounds
  have hs1b : (s1).val < 2^64 := s1.hBounds
  have hw0b : (w0).val < 2^64 := w0.hBounds
  have hw1b : (w1).val < 2^64 := w1.hBounds
  have hcle : carry.val ≤ 1 := by rw [hc]; split <;> omega
  refine ⟨hi1le, w0, w1, ?_, ?_⟩
  · rw [hoval2, hzval]
    simp [List.getElem!_cons_zero, List.getElem!_cons_succ]
  · rw [hsval]
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
    -- resolve the negation mask N in the goal and the chain equations,
    -- then the addend masks (A1, A2)
    rcases hN with hn | hn
    · -- N = 0 : no negation, seed carry 0
      rw [hn] at hstep0 hstep1
      rw [Nat.xor_zero] at hstep0
      rw [Nat.xor_zero] at hstep1
      rw [if_pos hn]
      have hc' : carry.val = 0 := by rw [hc, if_pos hn]
      rcases hA1 with h1 | h1
      · have h2 : A2.val = 0 := by
          rcases hA2 with h2 | h2
          · exact h2
          · exact absurd h1 (hsub (by rw [h2]; norm_num))
        rw [h1, h2, Nat.and_zero, Nat.and_zero] at hstep0 hstep1
        rw [Nat.xor_zero] at hstep0
        rw [Nat.xor_zero] at hstep1
        rw [if_pos h1]
        omega
      · have hone0 : (0xf9850b68df11df53 : ℕ) &&& A1.val = 0xf9850b68df11df53 := by
          rw [h1]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
        have hone1 : (0xf735481d1969f317 : ℕ) &&& A1.val = 0xf735481d1969f317 := by
          rw [h1]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
        rw [hone0] at hstep0
        rw [hone1] at hstep1
        rw [if_neg (show ¬ A1.val = 0 by rw [h1]; norm_num)]
        rcases hA2 with h2 | h2
        · rw [h2, Nat.and_zero] at hstep0 hstep1
          rw [Nat.xor_zero] at hstep0
          rw [Nat.xor_zero] at hstep1
          rw [if_pos h2]
          have hml : p % 2^128 = 0xf735481d1969f317f9850b68df11df53 := by norm_num [p]
          rw [hml]
          omega
        · have htwo0 : (0x0a8f1db9613261f5 : ℕ) &&& A2.val = 0x0a8f1db9613261f5 := by
            rw [h2]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
          have htwo1 : (0x195fd8272bba1538 : ℕ) &&& A2.val = 0x195fd8272bba1538 := by
            rw [h2]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
          rw [htwo0] at hstep0
          rw [htwo1] at hstep1
          rw [show (0xf9850b68df11df53 : ℕ) ^^^ 0x0a8f1db9613261f5
              = 0xf30a16d1be23bea6 from by decide] at hstep0
          rw [show (0xf735481d1969f317 : ℕ) ^^^ 0x195fd8272bba1538
              = 0xee6a903a32d3e62f from by decide] at hstep1
          rw [if_neg (show ¬ A2.val = 0 by rw [h2]; norm_num)]
          have hml : (2 * p) % 2^128 = 0xee6a903a32d3e62ff30a16d1be23bea6 := by norm_num [p]
          rw [hml]
          omega
    · -- N = all-ones : complement, seed carry 1
      rw [xor_allOnes_val s0 N hn] at hstep0
      rw [xor_allOnes_val s1 N hn] at hstep1
      rw [if_neg (show ¬ N.val = 0 by rw [hn]; norm_num)]
      have hc' : carry.val = 1 := by
        rw [hc, if_neg (show ¬ N.val = 0 by rw [hn]; norm_num)]
      rcases hA1 with h1 | h1
      · have h2 : A2.val = 0 := by
          rcases hA2 with h2 | h2
          · exact h2
          · exact absurd h1 (hsub (by rw [h2]; norm_num))
        rw [h1, h2, Nat.and_zero, Nat.and_zero] at hstep0 hstep1
        rw [Nat.xor_zero] at hstep0
        rw [Nat.xor_zero] at hstep1
        rw [if_pos h1]
        omega
      · have hone0 : (0xf9850b68df11df53 : ℕ) &&& A1.val = 0xf9850b68df11df53 := by
          rw [h1]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
        have hone1 : (0xf735481d1969f317 : ℕ) &&& A1.val = 0xf735481d1969f317 := by
          rw [h1]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
        rw [hone0] at hstep0
        rw [hone1] at hstep1
        rw [if_neg (show ¬ A1.val = 0 by rw [h1]; norm_num)]
        rcases hA2 with h2 | h2
        · rw [h2, Nat.and_zero] at hstep0 hstep1
          rw [Nat.xor_zero] at hstep0
          rw [Nat.xor_zero] at hstep1
          rw [if_pos h2]
          have hml : p % 2^128 = 0xf735481d1969f317f9850b68df11df53 := by norm_num [p]
          rw [hml]
          omega
        · have htwo0 : (0x0a8f1db9613261f5 : ℕ) &&& A2.val = 0x0a8f1db9613261f5 := by
            rw [h2]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
          have htwo1 : (0x195fd8272bba1538 : ℕ) &&& A2.val = 0x195fd8272bba1538 := by
            rw [h2]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
          rw [htwo0] at hstep0
          rw [htwo1] at hstep1
          rw [show (0xf9850b68df11df53 : ℕ) ^^^ 0x0a8f1db9613261f5
              = 0xf30a16d1be23bea6 from by decide] at hstep0
          rw [show (0xf735481d1969f317 : ℕ) ^^^ 0x195fd8272bba1538
              = 0xee6a903a32d3e62f from by decide] at hstep1
          rw [if_neg (show ¬ A2.val = 0 by rw [h2]; norm_num)]
          have hml : (2 * p) % 2^128 = 0xee6a903a32d3e62ff30a16d1be23bea6 := by norm_num [p]
          rw [hml]
          omega


/-- Value-level spec of the high half of the chain (`step_loop4`, limbs 2 and 3):
    writes the two high limbs of `u`; the discarded final carry is existentially
    exposed so the caller can reason about the 256-bit wrap. -/
theorem step_loop4_value_spec (iter : core.ops.range.Range Std.Usize)
    (u u_sub_v : Uint4) (N A2 A1 carry : Limb)
    (hs : iter.start.val = 2) (he : iter.«end».val = 4)
    (hN : IsMask N) (hA2 : IsMask A2) (hA1 : IsMask A1)
    (hsub : A2.val ≠ 0 → A1.val ≠ 0) (hcle : carry.val ≤ 1) :
    field.verified.invert.invert.step_loop4 iter u u_sub_v N A2 A1 carry
      ⦃ o => ∃ (w2 w3 : Limb) (c4 : ℕ), c4 ≤ 1 ∧
          o.val = [u.val[0]!, u.val[1]!, w2, w3] ∧
          w2.val + 2^64 * w3.val + 2^128 * c4
            = (if N.val = 0
               then u_sub_v.val[2]!.val + 2^64 * u_sub_v.val[3]!.val
               else 2^128 - 1 - (u_sub_v.val[2]!.val + 2^64 * u_sub_v.val[3]!.val))
              + (if A1.val = 0 then 0
                 else if A2.val = 0 then p / 2^128 else (2 * p) / 2^128)
              + carry.val ⦄ := by
  obtain ⟨s0, s1, s2, s3, hsval⟩ := Uint4.exists_four_limbs u_sub_v
  obtain ⟨z0, z1, z2, z3, hzval⟩ := Uint4.exists_four_limbs u
  have hp : p = 0x7ffffffffffffffffffffffffffffffff735481d1969f317f9850b68df11df53 := by
    norm_num [p]
  have hpx : p ^^^ 2 * p
      = 0x80000000000000000000000000000000195fd8272bba15380a8f1db9613261f5 := by decide
  unfold field.verified.invert.invert.step_loop4
  -- iteration 1 : l = 2
  apply loop_step
  unfold field.verified.invert.invert.step_loop4.body
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter (by omega))
  intro ⟨o, iter1⟩ ⟨ho, hs1, he1⟩
  simp only [ho]
  step as ⟨mo, hmo⟩
  step as ⟨ma, hma⟩
  step as ⟨l1, hl1⟩
  step as ⟨l2, hl2⟩
  step as ⟨mx, hmx⟩
  step as ⟨xa, hxa⟩
  step as ⟨l3, hl3⟩
  step as ⟨l4, hl4⟩
  step as ⟨mi2, hmi2⟩
  step as ⟨sa, hsa⟩
  step as ⟨l5, hl5⟩
  step as ⟨l6, hl6⟩
  step as ⟨w2, c2, hadd2, hc2le⟩
  step as ⟨ua, back, hua, hback⟩
  step as ⟨o1, ho1⟩
  obtain ⟨q0, q1, q2, q3, hqv⟩ := Uint4.exists_four_limbs mo
  have hq2 : q2.val = 0xffffffffffffffff := by
    have hsum := Uint4.toNat_of_limbs hqv
    rw [hmo, hp] at hsum
    have h0 : (q0).val < 2^64 := q0.hBounds
    have h1 : (q1).val < 2^64 := q1.hBounds
    have h2 : (q2).val < 2^64 := q2.hBounds
    have h3 : (q3).val < 2^64 := q3.hBounds
    omega
  obtain ⟨x0, x1, x2, x3, hxv⟩ := Uint4.exists_four_limbs mx
  have hx2 : x2.val = 0 := by
    have hsum := Uint4.toNat_of_limbs hxv
    rw [hmx, hpx] at hsum
    have h0 : (x0).val < 2^64 := x0.hBounds
    have h1 : (x1).val < 2^64 := x1.hBounds
    have h2 : (x2).val < 2^64 := x2.hBounds
    have h3 : (x3).val < 2^64 := x3.hBounds
    omega
  simp only [hma, hqv, hs] at hl1
  simp at hl1
  simp only [hxa, hxv, hs] at hl3
  simp at hl3
  simp only [hsa, hsval, hs] at hl5
  simp at hl5
  have hoval1 : o1.val = [z0, z1, w2, z3] := by
    rw [ho1, Array.set_val_eq, hua, hzval, hs]
    rfl
  simp only [hback]
  -- iteration 2 : l = 3
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_some_spec iter1 (by
      simp only [he1]; omega))
  intro ⟨o2, iter2⟩ ⟨ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨mo', hmo'⟩
  step as ⟨ma', hma'⟩
  step as ⟨l1', hl1'⟩
  step as ⟨l2', hl2'⟩
  step as ⟨mx', hmx'⟩
  step as ⟨xa', hxa'⟩
  step as ⟨l3', hl3'⟩
  step as ⟨l4', hl4'⟩
  step as ⟨mi3, hmi3⟩
  step as ⟨sa', hsa'⟩
  step as ⟨l5', hl5'⟩
  step as ⟨l6', hl6'⟩
  step as ⟨w3, c3, hadd3, hc3le⟩
  step as ⟨ua', back', hua', hback'⟩
  step as ⟨o2', ho2'⟩
  obtain ⟨q0', q1', q2', q3', hqv'⟩ := Uint4.exists_four_limbs mo'
  have hq3 : q3'.val = 0x7fffffffffffffff := by
    have hsum := Uint4.toNat_of_limbs hqv'
    rw [hmo', hp] at hsum
    have h0 : (q0').val < 2^64 := q0'.hBounds
    have h1 : (q1').val < 2^64 := q1'.hBounds
    have h2 : (q2').val < 2^64 := q2'.hBounds
    have h3 : (q3').val < 2^64 := q3'.hBounds
    omega
  obtain ⟨x0', x1', x2', x3', hxv'⟩ := Uint4.exists_four_limbs mx'
  have hx3 : x3'.val = 0x8000000000000000 := by
    have hsum := Uint4.toNat_of_limbs hxv'
    rw [hmx', hpx] at hsum
    have h0 : (x0').val < 2^64 := x0'.hBounds
    have h1 : (x1').val < 2^64 := x1'.hBounds
    have h2 : (x2').val < 2^64 := x2'.hBounds
    have h3 : (x3').val < 2^64 := x3'.hBounds
    omega
  simp only [hma', hqv', hs1, hs] at hl1'
  simp at hl1'
  simp only [hxa', hxv', hs1, hs] at hl3'
  simp at hl3'
  simp only [hsa', hsval, hs1, hs] at hl5'
  simp at hl5'
  have hoval2 : o2'.val = [z0, z1, w2, w3] := by
    rw [ho2', Array.set_val_eq, hua', hoval1, hs1, hs]
    rfl
  simp only [hback']
  -- iteration 3 : exhausted
  apply loop_step
  try simp only []
  apply Aeneas.Std.WP.spec_bind
    (core.iter.range.IteratorRange.next_Usize_none_spec iter2 (by
      simp only [he2, he1]; omega))
  intro ⟨o3, iter3⟩ ⟨ho3, hi3⟩
  simp only [ho3]
  apply spec_ok_of
  -- assemble
  rw [hl1, hq2] at hl2
  rw [hl3, hx2] at hl4
  rw [hl2, hl4] at hmi2
  rw [hl1', hq3] at hl2'
  rw [hl3', hx3] at hl4'
  rw [hl2', hl4'] at hmi3
  rw [hl5] at hl6
  rw [hl5'] at hl6'
  rw [hl6, hmi2] at hadd2
  rw [hl6', hmi3] at hadd3
  have hs2b : (s2).val < 2^64 := s2.hBounds
  have hs3b : (s3).val < 2^64 := s3.hBounds
  have hw2b : (w2).val < 2^64 := w2.hBounds
  have hw3b : (w3).val < 2^64 := w3.hBounds
  refine ⟨w2, w3, c3.val, hc3le, ?_, ?_⟩
  · rw [hoval2, hzval]
    simp [List.getElem!_cons_zero, List.getElem!_cons_succ]
  · rw [hsval]
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
    have hph : p / 2^128 = 0x7fffffffffffffffffffffffffffffff := by norm_num [p]
    have h2ph : (2 * p) / 2^128 = 0xffffffffffffffffffffffffffffffff := by norm_num [p]
    rcases hN with hn | hn
    · -- N = 0
      rw [hn, Nat.xor_zero] at hadd2 hadd3
      rw [if_pos hn]
      rcases hA1 with h1 | h1
      · have h2 : A2.val = 0 := by
          rcases hA2 with h2 | h2
          · exact h2
          · exact absurd h1 (hsub (by rw [h2]; norm_num))
        rw [h1, h2, Nat.and_zero, Nat.and_zero, Nat.xor_zero] at hadd2 hadd3
        rw [if_pos h1]
        omega
      · have hone2 : (0xffffffffffffffff : ℕ) &&& A1.val = 0xffffffffffffffff := by
          rw [h1]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
        have hone3 : (0x7fffffffffffffff : ℕ) &&& A1.val = 0x7fffffffffffffff := by
          rw [h1]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
        rw [hone2] at hadd2
        rw [hone3] at hadd3
        rw [if_neg (show ¬ A1.val = 0 by rw [h1]; norm_num)]
        rcases hA2 with h2 | h2
        · rw [h2, Nat.and_zero, Nat.xor_zero] at hadd2 hadd3
          rw [if_pos h2, hph]
          omega
        · have htop : (0x8000000000000000 : ℕ) &&& A2.val = 0x8000000000000000 := by
            rw [h2]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
          rw [Nat.zero_and, Nat.xor_zero] at hadd2
          rw [htop, show (0x7fffffffffffffff : ℕ) ^^^ 0x8000000000000000
              = 0xffffffffffffffff from by decide] at hadd3
          rw [if_neg (show ¬ A2.val = 0 by rw [h2]; norm_num), h2ph]
          omega
    · -- N = all-ones
      rw [xor_allOnes_val s2 N hn] at hadd2
      rw [xor_allOnes_val s3 N hn] at hadd3
      rw [if_neg (show ¬ N.val = 0 by rw [hn]; norm_num)]
      rcases hA1 with h1 | h1
      · have h2 : A2.val = 0 := by
          rcases hA2 with h2 | h2
          · exact h2
          · exact absurd h1 (hsub (by rw [h2]; norm_num))
        rw [h1, h2, Nat.and_zero, Nat.and_zero, Nat.xor_zero] at hadd2 hadd3
        rw [if_pos h1]
        omega
      · have hone2 : (0xffffffffffffffff : ℕ) &&& A1.val = 0xffffffffffffffff := by
          rw [h1]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
        have hone3 : (0x7fffffffffffffff : ℕ) &&& A1.val = 0x7fffffffffffffff := by
          rw [h1]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
        rw [hone2] at hadd2
        rw [hone3] at hadd3
        rw [if_neg (show ¬ A1.val = 0 by rw [h1]; norm_num)]
        rcases hA2 with h2 | h2
        · rw [h2, Nat.and_zero, Nat.xor_zero] at hadd2 hadd3
          rw [if_pos h2, hph]
          omega
        · have htop : (0x8000000000000000 : ℕ) &&& A2.val = 0x8000000000000000 := by
            rw [h2]; exact Nat.and_two_pow_sub_one_of_lt_two_pow (by norm_num)
          rw [Nat.zero_and, Nat.xor_zero] at hadd2
          rw [htop, show (0x7fffffffffffffff : ℕ) ^^^ 0x8000000000000000
              = 0xffffffffffffffff from by decide] at hadd3
          rw [if_neg (show ¬ A2.val = 0 by rw [h2]; norm_num), h2ph]
          omega

/-! ## Small arithmetic helpers for the step invariant -/

/-- gcd is preserved by halving an even member against an odd second argument. -/
theorem gcd_half_of_even_odd (x b : ℕ) (hx : x % 2 = 0) (hb : b % 2 = 1) :
    Nat.gcd (x / 2) b = Nat.gcd x b := by
  conv_rhs => rw [show x = 2 * (x / 2) by omega]
  exact (Nat.Coprime.gcd_mul_left_cancel (x / 2)
    (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hb))).symm

theorem two_ne_zero_zmod : (2 : ZMod p) ≠ 0 := by
  haveI : Fact (Nat.Prime p) := fact_p_prime
  have hplt : 2 < p := by norm_num [p]
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact h
  have hval := congrArg ZMod.val h2
  rw [ZMod.val_cast_of_lt hplt, ZMod.val_zero] at hval
  omega

/-- Parametric congruence step (the `Cancel2Mod` argument): from the exact ℕ identities
    `2A' + B = A` and `2U' + V = U + k·p` and the congruences `A ≡ U·y`, `B ≡ V·y`,
    conclude `A' ≡ U'·y (mod p)`.  Instantiated with `(A,B,U,V) := (a,b,u,v)` in the
    subtract case, `(b,a,v,u)` in the swap case and `(a,0,u,0)` in the even case. -/
theorem cong_of_double (y A B U V A' U' k : ℕ)
    (hA : (A : ZMod p) = (U : ZMod p) * (y : ZMod p))
    (hB : (B : ZMod p) = (V : ZMod p) * (y : ZMod p))
    (h2a : 2 * A' + B = A) (h2u : 2 * U' + V = U + k * p) :
    (A' : ZMod p) = (U' : ZMod p) * (y : ZMod p) := by
  haveI : Fact (Nat.Prime p) := fact_p_prime
  have hc : (2 : ZMod p) * (A' : ZMod p) + (V : ZMod p) * y
      = (U : ZMod p) * y := by
    have hc0 := congrArg (Nat.cast : ℕ → ZMod p) h2a
    push_cast at hc0
    rw [hB] at hc0
    rw [← hA]
    exact hc0
  have hu : (2 : ZMod p) * (U' : ZMod p) + (V : ZMod p) = (U : ZMod p) := by
    have hu0 := congrArg (Nat.cast : ℕ → ZMod p) h2u
    push_cast at hu0
    rwa [ZMod.natCast_self, mul_zero, add_zero] at hu0
  apply mul_left_cancel₀ two_ne_zero_zmod
  have hexp : (2 : ZMod p) * (A' : ZMod p)
      = ((2 : ZMod p) * (U' : ZMod p) + (V : ZMod p)) * y - (V : ZMod p) * y := by
    rw [hu, ← hc]; ring
  rw [hexp]; ring

theorem isMask_xor {x y r : Limb} (hx : IsMask x) (hy : IsMask y)
    (hr : r.val = x.val ^^^ y.val) : IsMask r := by
  unfold IsMask at *
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] at hr <;>
    simp only [Nat.zero_xor, Nat.xor_zero, Nat.xor_self] at hr <;> omega

theorem isMask_or {x y r : Limb} (hx : IsMask x) (hy : IsMask y)
    (hr : r.val = x.val ||| y.val) : IsMask r := by
  unfold IsMask at *
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] at hr <;>
    simp only [Nat.zero_or, Nat.or_zero, Nat.or_self] at hr <;> omega

/-! ## The Algorithm-1 step invariant (task item 3)

The Rust `step` is one iteration of Algorithm 1 of "Optimized Binary GCD for Modular
Inversion" (https://eprint.iacr.org/2020/972): on state `(a, b, u, v)` with `b` odd it
performs, branch-free,

  if a odd ∧ a < b then swap (a,b) and (u,v);
  if a odd then a ← a - b, u ← u - v (mod p);
  a ← a / 2;  u ← u / 2 (mod p)    -- exact: the masked additions of 0/1/2 copies of p
                                    -- make the numerator of u nonnegative and even

so the congruences `a ≡ u·y` and `b ≡ v·y (mod p)` (`y` = the value being inverted) are
preserved, `b` stays odd, `u,v` stay in `[0, p]`, `gcd(a,b)` is unchanged, and the
bit-size potential halves: `2·a'·b' ≤ a·b`. -/

/-- Arithmetic part of the binary-GCD invariant for the state `(a, b, u, v)` relative to
    the inverted value `y`.

    `a, b ≤ p` keep the a-side subtraction chain in range and are trivially inductive
    (`b' ∈ {a, b}`, `a' = ⌊·/2⌋`). The fused negate-and-add-modulus carry chain now
    includes the selected two-modulus contribution on all four limbs, so these local
    arithmetic and modular facts are sufficient. -/
def InvA (y : ℕ) (a b u v : Uint4) : Prop :=
  b.toNat % 2 = 1 ∧
  u.toNat ≤ p ∧
  v.toNat ≤ p ∧
  ((a.toNat : ZMod p) = (u.toNat : ZMod p) * (y : ZMod p)) ∧
  ((b.toNat : ZMod p) = (v.toNat : ZMod p) * (y : ZMod p)) ∧
  Nat.gcd a.toNat b.toNat = Nat.gcd y p ∧
  a.toNat ≤ p ∧
  b.toNat ≤ p

/-- Full loop invariant: `InvA` plus zero-propagation (for `y = 0` the working value `a`
    and the output accumulator `v` stay `0`; this clause is discharged by the *proved*
    `step_basic_spec`). A structure (rather than a
    conjunction) so that tactic normalization cannot flatten it. -/
structure Inv (y : ℕ) (a b u v : Uint4) : Prop where
  invA : InvA y a b u v
  zero : y = 0 → a.toNat = 0 ∧ v.toNat = 0

set_option maxHeartbeats 8000000 in
/-- One `step` preserves the arithmetic invariant and halves the potential `a·b`.
    The former source used a top-bit OR for the high contribution of `2p`; that operation
    was exact only under a non-inductive window condition. The repaired source selects the
    high limbs of `2p` inside `step_loop4`, so this proof now follows directly from the
    four-limb full-adder identities with no reachability hypothesis. -/
theorem step_congruence (y : ℕ) (a b u v : Uint4) (h : InvA y a b u v) :
    field.verified.invert.invert.step a b u v
      ⦃ s => InvA y s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
             2 * (s.1.toNat * s.2.1.toNat) ≤ a.toNat * b.toNat ⦄ := by
  -- Drive the branch-free body once, using the value-level loop specs above;
  -- the outputs are `(a7, b1, u4, v1) = (a', b', u', v')`.
  unfold field.verified.invert.invert.step
  step as ⟨a1, ha1⟩
  step as ⟨l, hl⟩
  rw [ha1] at hl
  step as ⟨a_is_odd, hodd, hoddbv⟩
  step as ⟨a_is_odd1, hodd1⟩
  step as ⟨borrow, hborrow⟩
  step as ⟨a_sub_b, hasb⟩
  step as ⟨i, hi⟩
  have hi4 : i.val = 4 := by rw [hi]; simp
  have hodd_le : a_is_odd.val ≤ 1 := by
    rw [hodd]
    have h1 : ((1#u64) : Std.U64).val = 1 := by simp
    simp only [UScalar.val_and, h1, Nat.and_one_is_mod]
    omega
  have hmask_odd : IsMask a_is_odd1 := isMask_of_wrapping_neg hodd_le hodd1
  -- `a - b` borrow chain, exact value
  refine WP.spec_bind (step_loop0_value_spec { start := 0#usize, «end» := i }
    a b borrow a_sub_b (by simp) hi4 hborrow) ?_
  rintro ⟨borrow1, a_sub_b1⟩ ⟨hb1le, hb1sum⟩
  step as ⟨a_lt_b, hltb⟩
  have hmask_ltb : IsMask a_lt_b := isMask_of_wrapping_neg hb1le hltb
  step as ⟨both, hboth⟩
  have hmask_both : IsMask both := isMask_and hmask_odd hmask_ltb hboth
  step with select_spec as ⟨b1, hb1sel⟩
  step as ⟨l1, hl1⟩
  step as ⟨carry, hcarry⟩
  have hcarry' : carry.val = if a_lt_b.val = 0 then 0 else 1 := by
    rw [hcarry, hl1]
    rcases hmask_ltb with hh | hh
    · rw [hh]; simp
    · rw [hh, Nat.and_two_pow_sub_one_of_lt_two_pow (show (1:ℕ) < 2^64 by norm_num)]
      norm_num
  -- conditional negation, exact value
  refine WP.spec_bind (step_loop1_value_spec { start := 0#usize, «end» := i }
    a_sub_b1 a_lt_b carry a_sub_b (by simp) hi4 hmask_ltb hcarry') ?_
  intro a_diff_b hdiff
  obtain ⟨hdiff_id, hdiff_neg⟩ := hdiff
  step with select_spec as ⟨a2, ha2sel⟩
  -- `u - (v & a_is_odd)` borrow chain, exact value
  refine WP.spec_bind (step_loop2_value_spec { start := 0#usize, «end» := i }
    u v a_is_odd1 borrow a_sub_b (by simp) hi4 hmask_odd hborrow) ?_
  rintro ⟨borrow2, u_sub_v⟩ ⟨hb2le, hs2sum⟩
  obtain ⟨s0, s1, s2, s3, hsval⟩ := Uint4.exists_four_limbs u_sub_v
  have hssumN := Uint4.toNat_of_limbs hsval
  step as ⟨u_sub_v_neg, husvn⟩
  step as ⟨should_negate, hsn⟩
  have hmask_sn : IsMask should_negate := isMask_and hmask_odd hmask_ltb hsn
  step as ⟨v_u, hvu⟩
  step as ⟨a3, ha3⟩
  step as ⟨l2, hl2⟩
  step as ⟨l3, hl3⟩
  step as ⟨result_is_odd, hrio⟩
  step as ⟨l4, hl4⟩
  step as ⟨add_two, hat⟩
  step as ⟨add_one, hao⟩
  step as ⟨carry1, hcar1⟩
  -- masks of the modulus-addition ladder
  have hmask_usvn : IsMask u_sub_v_neg := isMask_of_wrapping_neg hb2le husvn
  have hmask_vu : IsMask v_u := isMask_xor hmask_usvn hmask_sn hvu
  rw [ha3] at hl2
  simp only [hsval] at hl2
  simp at hl2
  have hl3v : l3.val = s0.val % 2 := by
    rw [hl3, hl2, hl1, Nat.and_one_is_mod]
  have hl3_le : l3.val ≤ 1 := by rw [hl3v]; omega
  have hmask_rio : IsMask result_is_odd := isMask_of_wrapping_neg hl3_le hrio
  have hmask_l4 : IsMask l4 := by
    unfold IsMask
    rcases hmask_rio with hh | hh <;> rw [hl4, hh] <;> omega
  have hmask_at : IsMask add_two := isMask_and hmask_vu hmask_l4 hat
  have hmask_ao : IsMask add_one := isMask_or hmask_vu hmask_rio hao
  have hsubset : add_two.val ≠ 0 → add_one.val ≠ 0 := by
    intro hne
    have h1 : add_two.val ≤ v_u.val := by rw [hat]; exact Nat.and_le_left
    have h2 : v_u.val ≤ add_one.val := by rw [hao]; exact Nat.left_le_or
    omega
  have hcar1' : carry1.val = if should_negate.val = 0 then 0 else 1 := by
    rw [hcar1, hl1]
    rcases hmask_sn with hh | hh
    · rw [hh]; simp
    · rw [hh, Nat.and_two_pow_sub_one_of_lt_two_pow (show (1:ℕ) < 2^64 by norm_num)]
      norm_num
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = 2 := by rw [hi1]; simp
  -- low half of the fused chain, exact value
  refine WP.spec_bind (step_loop3_value_spec { start := 0#usize, «end» := i1 }
    u u_sub_v should_negate add_two add_one carry1 (by simp) hi1v
    hmask_sn hmask_at hmask_ao hsubset hcar1') ?_
  rintro ⟨u1, carry2⟩ ⟨hc2le, w0, w1, hu1val, hu1sum⟩
  -- high half of the fused chain, exact value
  refine WP.spec_bind (step_loop4_value_spec { start := i1, «end» := i }
    u1 u_sub_v should_negate add_two add_one carry2 hi1v hi4
    hmask_sn hmask_at hmask_ao hsubset hc2le) ?_
  rintro u2 ⟨w2, w3, c4, hc4le, hu2val, hu2sum⟩
  step with select_spec as ⟨v1, hv1sel⟩
  step as ⟨a7, ha7⟩
  step as ⟨u4, hu4⟩
  -- Unpack the strengthened input invariant.
  obtain ⟨hbodd, hule, hvle, hacong, hbcong, hgcd, hale, hble⟩ := h
  -- `both = a_is_odd1 & a_lt_b`, so `both ≠ 0` forces `a` odd (used for `b' = a` odd).
  have hboth_le : both.val ≤ a_is_odd1.val := by rw [hboth]; exact Nat.and_le_left
  have ha_par : both.val ≠ 0 → a.toNat % 2 = 1 := by
    intro hbne
    have h1 : a_is_odd1.val ≠ 0 := by omega
    have h2 : a_is_odd1.val = 2 ^ 64 - 1 := by
      rcases hmask_odd with hh | hh
      · exact absurd hh h1
      · exact hh
    have h3 : a_is_odd.val = 1 := by rw [h2] at hodd1; omega
    have hval : a_is_odd.val = l.val &&& 1 := by rw [hodd]; simp [UScalar.val_and]
    rw [hval, hl] at h3
    rw [Uint4.toNat_mod_two_eq_limb0]
    rwa [Nat.and_one_is_mod] at h3
  -- ==== value-level bookkeeping ====
  have hpv : p = 0x7ffffffffffffffffffffffffffffffff735481d1969f317f9850b68df11df53 := by
    norm_num [p]
  obtain ⟨z0, z1, z2, z3, huval⟩ := Uint4.exists_four_limbs u
  simp only [huval, List.getElem!_cons_zero, List.getElem!_cons_succ] at hu1val
  simp only [hu1val, List.getElem!_cons_zero, List.getElem!_cons_succ] at hu2val
  simp only [hsval, List.getElem!_cons_zero, List.getElem!_cons_succ] at hu1sum hu2sum
  have hu2nat := Uint4.toNat_of_limbs hu2val
  have husumN := Uint4.toNat_of_limbs huval
  have hu4v : u4.toNat = u2.toNat / 2 := by rw [hu4]; simp
  have ha7v : a7.toNat = a2.toNat / 2 := by rw [ha7]; simp
  have hs0b : (s0).val < 2^64 := s0.hBounds
  have hs1b : (s1).val < 2^64 := s1.hBounds
  have hs2b : (s2).val < 2^64 := s2.hBounds
  have hs3b : (s3).val < 2^64 := s3.hBounds
  have hw0b : (w0).val < 2^64 := w0.hBounds
  have hw1b : (w1).val < 2^64 := w1.hBounds
  have hw2b : (w2).val < 2^64 := w2.hBounds
  have hw3b : (w3).val < 2^64 := w3.hBounds
  have hsv256 : u_sub_v.toNat < 2^256 := Uint4.toNat_lt u_sub_v
  have hu256 : u.toNat < 2^256 := Uint4.toNat_lt u
  have hv256 : v.toNat < 2^256 := Uint4.toNat_lt v
  have ha256 : a.toNat < 2^256 := Uint4.toNat_lt a
  have hb256 : b.toNat < 2^256 := Uint4.toNat_lt b
  have hd256 : a_sub_b1.toNat < 2^256 := Uint4.toNat_lt a_sub_b1
  have hdd256 : a_diff_b.toNat < 2^256 := Uint4.toNat_lt a_diff_b
  -- parity of the wrapped difference is the parity of its low limb
  have hspar : u_sub_v.toNat % 2 = s0.val % 2 := by omega
  -- ==== dichotomies for the three logical conditions ====
  have hval_odd : a.toNat % 2 = a_is_odd.val := by
    rw [hodd]
    have h1 : ((1#u64) : Std.U64).val = 1 := by simp
    simp only [UScalar.val_and, h1, Nat.and_one_is_mod]
    rw [hl]
    exact Uint4.toNat_mod_two_eq_limb0 a
  have hpar_a : (a_is_odd1.val = 0 ∧ a.toNat % 2 = 0) ∨
      (a_is_odd1.val = 2^64 - 1 ∧ a.toNat % 2 = 1) := by
    rcases hmask_odd with hh | hh
    · left; refine ⟨hh, ?_⟩
      rw [hh] at hodd1
      rw [hval_odd]
      omega
    · right; refine ⟨hh, ?_⟩
      rw [hh] at hodd1
      rw [hval_odd]
      omega
  have hltb_dich : (a_lt_b.val = 0 ∧ borrow1.val = 0 ∧ b.toNat ≤ a.toNat) ∨
      (a_lt_b.val = 2^64 - 1 ∧ borrow1.val = 1 ∧ a.toNat < b.toNat) := by
    rcases hmask_ltb with hh | hh
    · left
      rw [hh] at hltb
      refine ⟨hh, ?_, ?_⟩ <;> omega
    · right
      rw [hh] at hltb
      refine ⟨hh, ?_, ?_⟩ <;> omega
  -- Trim the context before the master case analysis: `omega` case-splits on every
  -- disjunctive hypothesis, and the ~10 `IsMask` disjunctions would multiply every
  -- leaf call by 2^10.  Everything cleared here has already been consumed.
  clear hmask_odd hmask_ltb hmask_both hmask_sn hmask_usvn hmask_vu hmask_rio hmask_l4
  clear hmask_at hmask_ao hsubset hodd hoddbv hodd1 hltb hcarry hcarry' hcar1 hval_odd
  clear hasb ha1 hl hborrow hb1le hi hi1 hi1v
  clear hu4 ha7 hl2 hl3 ha3 huval hsval hu1val hu2val
  clear husumN
  -- ==== the master case analysis (12 leaves) ====
  -- Each disjunct records the mask values, the exact a-side identity, `u' ≤ p`, and
  -- the exact u-side identity `2u' + (v or u or 0) = (u or v) + k·p`, `k ≤ 2`.
  have hcases :
      (a_is_odd1.val = 0 ∧ both.val = 0 ∧
        2 * a7.toNat = a.toNat ∧ u4.toNat ≤ p ∧
        (∃ k, k ≤ 2 ∧ 2 * u4.toNat + 0 = u.toNat + k * p)) ∨
      (a_is_odd1.val = 2^64 - 1 ∧ a_lt_b.val = 0 ∧ both.val = 0 ∧
        a.toNat % 2 = 1 ∧ b.toNat ≤ a.toNat ∧
        2 * a7.toNat + b.toNat = a.toNat ∧ u4.toNat ≤ p ∧
        (∃ k, k ≤ 2 ∧ 2 * u4.toNat + v.toNat = u.toNat + k * p)) ∨
      (a_is_odd1.val = 2^64 - 1 ∧ a_lt_b.val = 2^64 - 1 ∧ both.val ≠ 0 ∧
        a.toNat % 2 = 1 ∧ a.toNat < b.toNat ∧
        2 * a7.toNat + a.toNat = b.toNat ∧ u4.toNat ≤ p ∧
        (∃ k, k ≤ 2 ∧ 2 * u4.toNat + u.toNat = v.toNat + k * p)) := by
    rcases hpar_a with ⟨hm0, hpar0⟩ | ⟨hm1, hpar1⟩
    · -- ===== CASE E : `a` even =====
      left
      have hboth0 : both.val = 0 := by rw [hboth, hm0]; exact Nat.zero_and _
      have hsn0 : should_negate.val = 0 := by rw [hsn, hm0]; exact Nat.zero_and _
      have ha2v : a2.toNat = a.toNat := by rw [ha2sel, if_pos hm0]
      have h2a7 : 2 * a7.toNat = a.toNat := by
        rw [ha7v, ha2v]
        omega
      clear hdiff_id hdiff_neg hb1sum ha2sel ha2v ha7v
      rw [if_pos hm0] at hs2sum
      have hb20 : borrow2.val = 0 := by omega
      have husvn0 : u_sub_v_neg.val = 0 := by rw [husvn]; omega
      have hvu0 : v_u.val = 0 := by
        rw [hvu, husvn0, hsn0]
        exact Nat.xor_self 0
      have hat0 : add_two.val = 0 := by rw [hat, hvu0]; exact Nat.zero_and _
      have haov : add_one.val = result_is_odd.val := by
        rw [hao, hvu0]; exact Nat.zero_or _
      have hcar10 : carry1.val = 0 := by rw [hcar1', if_pos hsn0]
      rw [if_pos hsn0] at hu1sum hu2sum
      rcases Nat.mod_two_eq_zero_or_one s0.val with hpar | hpar
      · -- `u` even: halve directly (k = 0)
        have hrio0 : result_is_odd.val = 0 := by rw [hrio, hl3v]; omega
        have hao0 : add_one.val = 0 := by rw [haov, hrio0]
        rw [if_pos hao0] at hu1sum hu2sum
        refine ⟨hm0, hboth0, h2a7, ?_, 0, by norm_num, ?_⟩ <;> omega
      · -- `u` odd: add one modulus (k = 1)
        have hrio1 : result_is_odd.val = 2^64 - 1 := by rw [hrio, hl3v]; omega
        have hao1 : add_one.val = 2^64 - 1 := by rw [haov, hrio1]
        rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
          if_pos hat0] at hu1sum
        rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
          if_pos hat0] at hu2sum
        refine ⟨hm0, hboth0, h2a7, ?_, 1, by norm_num, ?_⟩ <;> omega
    · rcases hltb_dich with ⟨hlt0, hbor10, hble_a⟩ | ⟨hlt1, hbor11, halt_b⟩
      · -- ===== CASE OG : `a` odd, `a ≥ b` =====
        right; left
        have hboth0 : both.val = 0 := by rw [hboth, hlt0]; exact Nat.and_zero _
        have hsn0 : should_negate.val = 0 := by rw [hsn, hlt0]; exact Nat.and_zero _
        have hd_id : a_diff_b.toNat = a_sub_b1.toNat := hdiff_id hlt0
        have ha2v : a2.toNat = a_diff_b.toNat := by
          rw [ha2sel, if_neg (show ¬ a_is_odd1.val = 0 by rw [hm1]; norm_num)]
        have h2a7 : 2 * a7.toNat + b.toNat = a.toNat := by
          rw [ha7v, ha2v, hd_id]
          omega
        clear hdiff_id hdiff_neg hb1sum ha2sel ha2v ha7v hd_id
        rw [if_neg (show ¬ a_is_odd1.val = 0 by rw [hm1]; norm_num)] at hs2sum
        have hcar10 : carry1.val = 0 := by rw [hcar1', if_pos hsn0]
        rw [if_pos hsn0] at hu1sum hu2sum
        rcases show borrow2.val = 0 ∨ borrow2.val = 1 by omega with hb20 | hb21
        · -- β = 0 : `u ≥ v`, no add-two
          have husvn0 : u_sub_v_neg.val = 0 := by rw [husvn]; omega
          have hvu0 : v_u.val = 0 := by
            rw [hvu, husvn0, hsn0]
            exact Nat.xor_self 0
          have hat0 : add_two.val = 0 := by rw [hat, hvu0]; exact Nat.zero_and _
          have haov : add_one.val = result_is_odd.val := by
            rw [hao, hvu0]; exact Nat.zero_or _
          rcases Nat.mod_two_eq_zero_or_one s0.val with hpar | hpar
          · have hrio0 : result_is_odd.val = 0 := by rw [hrio, hl3v]; omega
            have hao0 : add_one.val = 0 := by rw [haov, hrio0]
            rw [if_pos hao0] at hu1sum hu2sum
            refine ⟨hm1, hlt0, hboth0, hpar1, hble_a, h2a7, ?_, 0, by norm_num, ?_⟩ <;>
              omega
          · have hrio1 : result_is_odd.val = 2^64 - 1 := by rw [hrio, hl3v]; omega
            have hao1 : add_one.val = 2^64 - 1 := by rw [haov, hrio1]
            rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
              if_pos hat0] at hu1sum
            rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
              if_pos hat0] at hu2sum
            refine ⟨hm1, hlt0, hboth0, hpar1, hble_a, h2a7, ?_, 1, by norm_num, ?_⟩ <;>
              omega
        · -- β = 1 : `u < v`
          have husvn1 : u_sub_v_neg.val = 2^64 - 1 := by rw [husvn]; omega
          have hvu1 : v_u.val = 2^64 - 1 := by
            rw [hvu, husvn1, hsn0, Nat.xor_zero]
          rcases Nat.mod_two_eq_zero_or_one s0.val with hpar | hpar
          · -- difference even: add two moduli through the full carry chain
            have hrio0 : result_is_odd.val = 0 := by rw [hrio, hl3v]; omega
            have hl4v : l4.val = 2^64 - 1 := by rw [hl4]; omega
            have hat1 : add_two.val = 2^64 - 1 := by
              rw [hat, hvu1, hl4v, Nat.and_self]
            have hao1 : add_one.val = 2^64 - 1 := by
              rw [hao, hvu1, hrio0, Nat.or_zero]
            rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
              if_neg (show ¬ add_two.val = 0 by rw [hat1]; norm_num)] at hu1sum
            rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
              if_neg (show ¬ add_two.val = 0 by rw [hat1]; norm_num)] at hu2sum
            refine ⟨hm1, hlt0, hboth0, hpar1, hble_a, h2a7, ?_, 2, by norm_num, ?_⟩ <;>
              omega
          · -- difference odd: add one modulus, the wrap supplies the sign
            have hrio1 : result_is_odd.val = 2^64 - 1 := by rw [hrio, hl3v]; omega
            have hl4v : l4.val = 0 := by rw [hl4]; omega
            have hat0 : add_two.val = 0 := by
              rw [hat, hvu1, hl4v]; exact Nat.and_zero _
            have hao1 : add_one.val = 2^64 - 1 := by
              rw [hao, hvu1, hrio1, Nat.or_self]
            rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
              if_pos hat0] at hu1sum
            rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
              if_pos hat0] at hu2sum
            refine ⟨hm1, hlt0, hboth0, hpar1, hble_a, h2a7, ?_, 1, by norm_num, ?_⟩ <;>
              omega
      · -- ===== CASE OL : `a` odd, `a < b` (swap) =====
        right; right
        have hboth1 : both.val = 2^64 - 1 := by
          rw [hboth, hm1, hlt1]; exact Nat.and_self _
        have hsn1 : should_negate.val = 2^64 - 1 := by
          rw [hsn, hm1, hlt1]; exact Nat.and_self _
        have hd_neg := hdiff_neg (show a_lt_b.val ≠ 0 by rw [hlt1]; norm_num)
        have ha2v : a2.toNat = a_diff_b.toNat := by
          rw [ha2sel, if_neg (show ¬ a_is_odd1.val = 0 by rw [hm1]; norm_num)]
        have h2a7 : 2 * a7.toNat + a.toNat = b.toNat := by
          rw [ha7v, ha2v]
          omega
        clear hdiff_id hdiff_neg hb1sum ha2sel ha2v ha7v hd_neg
        rw [if_neg (show ¬ a_is_odd1.val = 0 by rw [hm1]; norm_num)] at hs2sum
        have hcar11 : carry1.val = 1 := by
          rw [hcar1', if_neg (show ¬ should_negate.val = 0 by rw [hsn1]; norm_num)]
        rw [if_neg (show ¬ should_negate.val = 0 by rw [hsn1]; norm_num)]
          at hu1sum hu2sum
        rcases show borrow2.val = 0 ∨ borrow2.val = 1 by omega with hb20 | hb21
        · -- β = 0 : `u ≥ v`, negation makes the value nonpositive
          have husvn0 : u_sub_v_neg.val = 0 := by rw [husvn]; omega
          have hvu1 : v_u.val = 2^64 - 1 := by
            rw [hvu, husvn0, hsn1, Nat.zero_xor]
          rcases Nat.mod_two_eq_zero_or_one s0.val with hpar | hpar
          · -- difference even: add two moduli through the full carry chain
            have hrio0 : result_is_odd.val = 0 := by rw [hrio, hl3v]; omega
            have hl4v : l4.val = 2^64 - 1 := by rw [hl4]; omega
            have hat1 : add_two.val = 2^64 - 1 := by
              rw [hat, hvu1, hl4v, Nat.and_self]
            have hao1 : add_one.val = 2^64 - 1 := by
              rw [hao, hvu1, hrio0, Nat.or_zero]
            rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
              if_neg (show ¬ add_two.val = 0 by rw [hat1]; norm_num)] at hu1sum
            rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
              if_neg (show ¬ add_two.val = 0 by rw [hat1]; norm_num)] at hu2sum
            refine ⟨hm1, hlt1, by rw [hboth1]; norm_num, hpar1, halt_b, h2a7, ?_,
              2, by norm_num, ?_⟩ <;> omega
          · -- difference odd
            have hrio1 : result_is_odd.val = 2^64 - 1 := by rw [hrio, hl3v]; omega
            have hl4v : l4.val = 0 := by rw [hl4]; omega
            have hat0 : add_two.val = 0 := by
              rw [hat, hvu1, hl4v]; exact Nat.and_zero _
            have hao1 : add_one.val = 2^64 - 1 := by
              rw [hao, hvu1, hrio1, Nat.or_self]
            rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
              if_pos hat0] at hu1sum
            rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
              if_pos hat0] at hu2sum
            refine ⟨hm1, hlt1, by rw [hboth1]; norm_num, hpar1, halt_b, h2a7, ?_,
              1, by norm_num, ?_⟩ <;> omega
        · -- β = 1 : `u < v`, wrap and negation cancel
          have husvn1 : u_sub_v_neg.val = 2^64 - 1 := by rw [husvn]; omega
          have hvu0 : v_u.val = 0 := by
            rw [hvu, husvn1, hsn1]
            exact Nat.xor_self _
          have hat0 : add_two.val = 0 := by rw [hat, hvu0]; exact Nat.zero_and _
          have haov : add_one.val = result_is_odd.val := by
            rw [hao, hvu0]; exact Nat.zero_or _
          rcases Nat.mod_two_eq_zero_or_one s0.val with hpar | hpar
          · have hrio0 : result_is_odd.val = 0 := by rw [hrio, hl3v]; omega
            have hao0 : add_one.val = 0 := by rw [haov, hrio0]
            rw [if_pos hao0] at hu1sum hu2sum
            refine ⟨hm1, hlt1, by rw [hboth1]; norm_num, hpar1, halt_b, h2a7, ?_,
              0, by norm_num, ?_⟩ <;> omega
          · have hrio1 : result_is_odd.val = 2^64 - 1 := by rw [hrio, hl3v]; omega
            have hao1 : add_one.val = 2^64 - 1 := by rw [haov, hrio1]
            rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
              if_pos hat0] at hu1sum
            rw [if_neg (show ¬ add_one.val = 0 by rw [hao1]; norm_num),
              if_pos hat0] at hu2sum
            refine ⟨hm1, hlt1, by rw [hboth1]; norm_num, hpar1, halt_b, h2a7, ?_,
              1, by norm_num, ?_⟩ <;> omega
  -- ==== discharge the invariant and potential conjuncts ====
  refine ⟨?_, ?_⟩
  · -- The strengthened arithmetic invariant on `(a', b', u', v') = (a7, b1, u4, v1)`.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- `b'` odd:  `b' = if both = 0 then b else a`, both odd.
      rw [hb1sel]
      split
      · exact hbodd
      · next hne => exact ha_par hne
    · -- `u' ≤ p` — from the chain ledger, in every case.
      rcases hcases with ⟨_, _, _, hup, _⟩ | ⟨_, _, _, _, _, _, hup, _⟩ |
        ⟨_, _, _, _, _, _, hup, _⟩ <;> exact hup
    · -- `v' ≤ p`:  `v' = if both = 0 then v else u`, both `≤ p`.
      rw [hv1sel]
      split
      · exact hvle
      · exact hule
    · -- `a' ≡ u'·y (mod p)` — the parametric cancel-2 argument, per case.
      rcases hcases with ⟨_, _, h2a, _, k, _, h2u⟩ |
        ⟨_, _, _, _, _, h2a, _, k, _, h2u⟩ | ⟨_, _, _, _, _, h2a, _, k, _, h2u⟩
      · exact cong_of_double y a.toNat 0 u.toNat 0 a7.toNat u4.toNat k hacong
          (by push_cast; ring) (by omega) h2u
      · exact cong_of_double y a.toNat b.toNat u.toNat v.toNat a7.toNat u4.toNat k
          hacong hbcong h2a h2u
      · exact cong_of_double y b.toNat a.toNat v.toNat u.toNat a7.toNat u4.toNat k
          hbcong hacong h2a h2u
    · -- `b' ≡ v'·y (mod p)`:  `(b', v') = (b, v)` or `(a, u)`.
      rw [hb1sel, hv1sel]
      by_cases hb0 : both.val = 0
      · rw [if_pos hb0, if_pos hb0]; exact hbcong
      · rw [if_neg hb0, if_neg hb0]; exact hacong
    · -- `gcd a' b' = gcd y p` — halving/subtraction/swap steps of `Nat.gcd`.
      rcases hcases with ⟨_, hboth0, h2a, _⟩ | ⟨_, _, hboth0, _, hble_a, h2a, _⟩ |
        ⟨_, _, hbothne, hodd_a, halt_b, h2a, _⟩
      · rw [hb1sel, if_pos hboth0]
        have ha7h : a7.toNat = a.toNat / 2 := by omega
        rw [ha7h, gcd_half_of_even_odd a.toNat b.toNat (by omega) hbodd]
        exact hgcd
      · rw [hb1sel, if_pos hboth0]
        have ha7h : a7.toNat = (a.toNat - b.toNat) / 2 := by omega
        rw [ha7h, gcd_half_of_even_odd (a.toNat - b.toNat) b.toNat (by omega) hbodd,
          Nat.gcd_sub_self_left hble_a]
        exact hgcd
      · rw [hb1sel, if_neg hbothne]
        have ha7h : a7.toNat = (b.toNat - a.toNat) / 2 := by omega
        rw [ha7h, gcd_half_of_even_odd (b.toNat - a.toNat) a.toNat (by omega) hodd_a,
          Nat.gcd_sub_self_left halt_b.le, Nat.gcd_comm]
        exact hgcd
    · -- `a' ≤ p` — the a-side halves.
      rcases hcases with ⟨_, _, h2a, _⟩ | ⟨_, _, _, _, _, h2a, _⟩ |
        ⟨_, _, _, _, _, h2a, _⟩ <;> omega
    · -- `b' ≤ p`:  `b' = if both = 0 then b else a`, both `≤ p`.
      rw [hb1sel]
      split
      · exact hble
      · exact hale
  · -- Potential halving `2·a'·b' ≤ a·b`.
    rcases hcases with ⟨_, hboth0, h2a, _⟩ | ⟨_, _, hboth0, _, hble_a, h2a, _⟩ |
      ⟨_, _, hbothne, _, halt_b, h2a, _⟩
    · rw [hb1sel, if_pos hboth0]
      have heq : 2 * (a7.toNat * b.toNat) = a.toNat * b.toNat := by
        calc 2 * (a7.toNat * b.toNat) = (2 * a7.toNat) * b.toNat := by ring
          _ = a.toNat * b.toNat := by rw [h2a]
      omega
    · rw [hb1sel, if_pos hboth0]
      have h2 : 2 * a7.toNat = a.toNat - b.toNat := by omega
      calc 2 * (a7.toNat * b.toNat) = (2 * a7.toNat) * b.toNat := by ring
        _ = (a.toNat - b.toNat) * b.toNat := by rw [h2]
        _ ≤ a.toNat * b.toNat := Nat.mul_le_mul (Nat.sub_le _ _) (le_refl _)
    · rw [hb1sel, if_neg hbothne]
      have h2 : 2 * a7.toNat = b.toNat - a.toNat := by omega
      calc 2 * (a7.toNat * a.toNat) = (2 * a7.toNat) * a.toNat := by ring
        _ = (b.toNat - a.toNat) * a.toNat := by rw [h2]
        _ ≤ b.toNat * a.toNat := Nat.mul_le_mul (Nat.sub_le _ _) (le_refl _)
        _ = a.toNat * b.toNat := Nat.mul_comm _ _

/-- Conjunction of two Hoare specs on the same computation. -/
theorem spec_and {α : Type u} {m : Result α} {P Q : α → Prop}
    (hP : m ⦃ x => P x ⦄) (hQ : m ⦃ x => Q x ⦄) : m ⦃ x => P x ∧ Q x ⦄ := by
  obtain ⟨x, hx, hPx⟩ := WP.spec_imp_exists hP
  obtain ⟨x', hx', hQx⟩ := WP.spec_imp_exists hQ
  rw [hx] at hx'
  injection hx' with hxx
  subst hxx
  rw [hx, WP.spec_ok]
  exact ⟨hPx, hQx⟩

/-- One `step` preserves the full invariant `Inv` and halves the potential.
    (Sorry-free except through `step_congruence`; the zero clause comes from the proved
    `step_basic_spec`.) -/
theorem step_spec (y : ℕ) (a b u v : Uint4) (h : Inv y a b u v) :
    field.verified.invert.invert.step a b u v
      ⦃ s => Inv y s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
             2 * (s.1.toNat * s.2.1.toNat) ≤ a.toNat * b.toNat ⦄ := by
  have hand := spec_and (step_congruence y a b u v h.invA) (step_basic_spec a b u v)
  apply WP.spec_mono hand
  rintro s ⟨⟨hA, hpot⟩, hzero⟩
  refine ⟨⟨hA, ?_⟩, hpot⟩
  intro hy
  obtain ⟨ha0, hv0⟩ := h.zero hy
  obtain ⟨ha0', hveq⟩ := hzero ha0
  refine ⟨ha0', ?_⟩
  rw [hveq]
  exact hv0

/-! ## The 510-iteration induction (inner 128-step loop, outer 3-pass loop,
trailing 126-step loop) -/

/-- The inner `for _ in 0 .. 2*Limb::BITS` loop: `e - s` iterations of `step`, shaving
    `e - s` off the potential exponent. -/
theorem invert_loop0_loop0_spec (y k : ℕ) (iter : core.ops.range.Range Std.Usize)
    (a b u v : Uint4) (hinv : Inv y a b u v)
    (hpot : a.toNat * b.toNat < 2^(k + (iter.«end».val - iter.start.val))) :
    field.verified.invert.invert_loop0_loop0 iter a b u v
      ⦃ s => Inv y s.1 s.2.1 s.2.2.1 s.2.2.2 ∧ s.1.toNat * s.2.1.toNat < 2^k ⦄ := by
  unfold field.verified.invert.invert_loop0_loop0
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (s : (core.ops.range.Range Std.Usize) × Uint4 × Uint4 × Uint4 × Uint4) =>
      s.1.«end».val - s.1.start.val)
    (inv := fun s =>
      s.1.«end» = iter.«end» ∧
      Inv y s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 ∧
      s.2.1.toNat * s.2.2.1.toNat < 2^(k + (iter.«end».val - s.1.start.val)))
  · rintro ⟨it, aa, bb, uu, vv⟩ hs
    have hite : it.«end» = iter.«end» := hs.1
    have hinv' : Inv y aa bb uu vv := hs.2.1
    have hpot' : aa.toNat * bb.toNat < 2^(k + (iter.«end».val - it.start.val)) := hs.2.2
    unfold field.verified.invert.invert_loop0_loop0.body
    step as ⟨o, iter1, ho, hoe⟩
    rcases o with _ | l
    · split at ho
      · simp at ho
      · next hge =>
        try simp only [WP.spec_ok]
        and_intros
        · exact hinv'
        · have hz : iter.«end».val - it.start.val = 0 := by
            rw [← hite]; omega
          rw [hz, Nat.add_zero] at hpot'
          exact hpot'
    · split at ho
      · next hlt =>
        obtain ⟨hosome, hst1⟩ := ho
        have hstep := step_spec y aa bb uu vv hinv'
        refine WP.spec_bind hstep ?_
        rintro ⟨a1, b1, u1, v1⟩ hpost
        have hinv2 : Inv y a1 b1 u1 v1 := hpost.1
        have hpot2 : 2 * (a1.toNat * b1.toNat) ≤ aa.toNat * bb.toNat := hpost.2
        try simp only [WP.spec_ok]
        and_intros
        · show iter1.«end» = iter.«end»
          rw [hoe, hite]
        · exact hinv2
        · show a1.toNat * b1.toNat < 2^(k + (iter.«end».val - iter1.start.val))
          rw [hst1]
          have hexp : k + (iter.«end».val - it.start.val)
              = (k + (iter.«end».val - (it.start.val + 1))) + 1 := by
            rw [← hite]; omega
          rw [hexp, pow_succ] at hpot'
          omega
        · show iter1.«end».val - iter1.start.val < it.«end».val - it.start.val
          have h1 : iter1.«end».val = it.«end».val := by rw [hoe]
          omega
      · simp at ho
  · exact ⟨rfl, hinv, hpot⟩

/-- Remaining passes of an inclusive-range iterator (`3` for the fresh `2..=4`). -/
def passes (it : core.ops.range.RangeInclusive Std.Usize) : ℕ :=
  if it.exhausted then 0 else it.«end».val + 1 - it.start.val

theorem passes_not_exhausted {it : core.ops.range.RangeInclusive Std.Usize}
    (h : it.exhausted = false) :
    passes it = it.«end».val + 1 - it.start.val := by
  unfold passes
  rw [h]
  simp

theorem passes_exhausted {it : core.ops.range.RangeInclusive Std.Usize}
    (h : it.exhausted = true) : passes it = 0 := by
  unfold passes
  rw [h]
  simp

/-- The outer `for _ in 2..=U256::LIMBS` loop: `128·passes` iterations of `step`. -/
theorem invert_loop0_spec (y k : ℕ) (it0 : core.ops.range.RangeInclusive Std.Usize)
    (a b u v : Uint4) (hinv : Inv y a b u v)
    (hpot : a.toNat * b.toNat < 2^(k + 128 * passes it0)) :
    field.verified.invert.invert_loop0 it0 a b u v
      ⦃ s => Inv y s.1 s.2.1 s.2.2.1 s.2.2.2 ∧ s.1.toNat * s.2.1.toNat < 2^k ⦄ := by
  unfold field.verified.invert.invert_loop0
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun
      (s : (core.ops.range.RangeInclusive Std.Usize) × Uint4 × Uint4 × Uint4 × Uint4) =>
      passes s.1)
    (inv := fun s =>
      Inv y s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 ∧
      s.2.1.toNat * s.2.2.1.toNat < 2^(k + 128 * passes s.1))
  · rintro ⟨it, aa, bb, uu, vv⟩ hs
    have hinv' : Inv y aa bb uu vv := hs.1
    have hpot' : aa.toNat * bb.toNat < 2^(k + 128 * passes it) := hs.2
    unfold field.verified.invert.invert_loop0.body
    step as ⟨o, iter1, ho⟩
    rcases o with _ | l
    · -- done: exhausted or start past end
      split at ho
      · next hcond =>
        try simp only [WP.spec_ok]
        and_intros
        · exact hinv'
        · have hp0 : passes it = 0 := by
            unfold passes
            split
            · rfl
            · next hnex =>
              rcases hcond with hex | hlt
              · exact absurd hex hnex
              · omega
          rw [hp0, Nat.mul_zero, Nat.add_zero] at hpot'
          exact hpot'
      · split at ho <;> simp at ho
    · -- one more pass
      split at ho
      · obtain ⟨hlno, -⟩ := ho
        simp at hlno
      · next hcond =>
        have hnex : it.exhausted = false := by
          rcases hx : it.exhausted with _ | _
          · rfl
          · exact absurd (Or.inl hx) hcond
        split at ho
        · next hlt2 =>
          obtain ⟨-, hst1, hend1, hex1⟩ := ho
          have hpass : passes it = passes iter1 + 1 := by
            rw [passes_not_exhausted hnex, passes_not_exhausted hex1, hend1, hst1]
            omega
          step as ⟨bits, hbits⟩
          step as ⟨i1, hi1⟩
          have hi1v : i1.val = 128 := by
            rw [hi1, usize_wrapping_mul_val (by simp [hbits])]
            simp [hbits]
          have hinner := invert_loop0_loop0_spec y (k + 128 * passes iter1)
            { start := 0#usize, «end» := i1 } aa bb uu vv hinv' (by
              have harg : k + 128 * passes iter1 + (i1.val - (0#usize).val)
                  = k + 128 * passes it := by
                rw [hpass, hi1v]
                simp
                ring
              rw [harg]
              exact hpot')
          refine WP.spec_bind hinner ?_
          rintro ⟨a1, b1, u1, v1⟩ hpost
          have hinv2 : Inv y a1 b1 u1 v1 := hpost.1
          have hpot2 : a1.toNat * b1.toNat < 2^(k + 128 * passes iter1) := hpost.2
          try simp only [WP.spec_ok]
          and_intros
          · exact hinv2
          · exact hpot2
          · show passes iter1 < passes it
            omega
        · next hge2 =>
          obtain ⟨-, hst1, hend1, hex1⟩ := ho
          have hpass : passes it = 1 := by
            rw [passes_not_exhausted hnex]
            have h1 : ¬ it.«end».val < it.start.val := fun hh => hcond (Or.inr hh)
            omega
          have hpass1 : passes iter1 = 0 := passes_exhausted hex1
          step as ⟨bits, hbits⟩
          step as ⟨i1, hi1⟩
          have hi1v : i1.val = 128 := by
            rw [hi1, usize_wrapping_mul_val (by simp [hbits])]
            simp [hbits]
          have hinner := invert_loop0_loop0_spec y k
            { start := 0#usize, «end» := i1 } aa bb uu vv hinv' (by
              have harg : k + (i1.val - (0#usize).val) = k + 128 * passes it := by
                rw [hpass, hi1v]
                simp
              rw [harg]
              exact hpot')
          refine WP.spec_bind hinner ?_
          rintro ⟨a1, b1, u1, v1⟩ hpost
          have hinv2 : Inv y a1 b1 u1 v1 := hpost.1
          have hpot2 : a1.toNat * b1.toNat < 2^k := hpost.2
          try simp only [WP.spec_ok]
          and_intros
          · exact hinv2
          · show a1.toNat * b1.toNat < 2^(k + 128 * passes iter1)
            rw [hpass1, Nat.mul_zero, Nat.add_zero]
            exact hpot2
          · show passes iter1 < passes it
            omega
  · exact ⟨hinv, hpot⟩

/-- The trailing `for _ in 0 .. 2*Limb::BITS - 2` loop: runs the potential down to
    `< 2^0 = 1`, i.e. `a = 0` (as `b` stays odd), so `b = gcd(y, p)` and `v` represents
    it: `gcd(y,p) ≡ v·y (mod p)`. -/
theorem invert_loop1_spec (y : ℕ) (iter : core.ops.range.Range Std.Usize)
    (a b u v : Uint4) (hinv : Inv y a b u v)
    (hpot : a.toNat * b.toNat < 2^(iter.«end».val - iter.start.val)) :
    field.verified.invert.invert_loop1 iter a b u v
      ⦃ r => r.toNat ≤ p ∧
             ((Nat.gcd y p : ℕ) : ZMod p) = (r.toNat : ZMod p) * (y : ZMod p) ∧
             (y = 0 → r.toNat = 0) ⦄ := by
  unfold field.verified.invert.invert_loop1
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (s : (core.ops.range.Range Std.Usize) × Uint4 × Uint4 × Uint4 × Uint4) =>
      s.1.«end».val - s.1.start.val)
    (inv := fun s =>
      s.1.«end» = iter.«end» ∧
      Inv y s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 ∧
      s.2.1.toNat * s.2.2.1.toNat < 2^(iter.«end».val - s.1.start.val))
  · rintro ⟨it, aa, bb, uu, vv⟩ hs
    have hite : it.«end» = iter.«end» := hs.1
    have hinv' : Inv y aa bb uu vv := hs.2.1
    have hpot' : aa.toNat * bb.toNat < 2^(iter.«end».val - it.start.val) := hs.2.2
    unfold field.verified.invert.invert_loop1.body
    step as ⟨o, iter1, ho, hoe⟩
    rcases o with _ | l
    · split at ho
      · simp at ho
      · next hge =>
        try simp only [WP.spec_ok]
        have hz : iter.«end».val - it.start.val = 0 := by
          rw [← hite]; omega
        rw [hz, pow_zero, Nat.lt_one_iff] at hpot'
        obtain ⟨hodd, hu, hv, hca, hcb, hgcd, _hap, _hbp⟩ := hinv'.invA
        have hbb : bb.toNat ≠ 0 := by omega
        have haa : aa.toNat = 0 := by
          rcases Nat.mul_eq_zero.mp hpot' with h | h
          · exact h
          · exact absurd h hbb
        rw [haa, Nat.gcd_zero_left] at hgcd
        and_intros
        · exact hv
        · rw [← hgcd]
          exact hcb
        · exact fun hy => (hinv'.zero hy).2
    · split at ho
      · next hlt =>
        obtain ⟨hosome, hst1⟩ := ho
        have hstep := step_spec y aa bb uu vv hinv'
        refine WP.spec_bind hstep ?_
        rintro ⟨a1, b1, u1, v1⟩ hpost
        have hinv2 : Inv y a1 b1 u1 v1 := hpost.1
        have hpot2 : 2 * (a1.toNat * b1.toNat) ≤ aa.toNat * bb.toNat := hpost.2
        try simp only [WP.spec_ok]
        and_intros
        · show iter1.«end» = iter.«end»
          rw [hoe, hite]
        · exact hinv2
        · show a1.toNat * b1.toNat < 2^(iter.«end».val - iter1.start.val)
          rw [hst1]
          have hexp : iter.«end».val - it.start.val
              = (iter.«end».val - (it.start.val + 1)) + 1 := by
            rw [← hite]; omega
          rw [hexp, pow_succ] at hpot'
          omega
        · show iter1.«end».val - iter1.start.val < it.«end».val - it.start.val
          have h1 : iter1.«end».val = it.«end».val := by rw [hoe]
          omega
      · simp at ho
  · exact ⟨rfl, hinv, hpot⟩

end Invert

/-! ## The exported contract lemma -/

open Invert in
/-- **Contract.** `invert` never fails; on reduced input `a < p` it returns the canonical
    inverse (with the validity flag cleared exactly on the non-invertible input 0).

    The per-step Algorithm-1 invariant, all 510 loop iterations, final reduction and flag
    computation are proved from the generated machine model. -/
theorem invert_ok (a : Uint4) (ha : a.toNat < p) :
    ∃ r flag, field.verified.invert.invert a = .ok (r, flag) ∧ r.toNat < p ∧
      (flag = true ↔ a.toNat ≠ 0) ∧ (a.toNat = 0 → r.toNat = 0) ∧
      (a.toNat ≠ 0 → (a.toNat * r.toNat) % p = 1) := by
  have hspec : field.verified.invert.invert a
      ⦃ rf => rf.1.toNat < p ∧ (rf.2 = true ↔ a.toNat ≠ 0) ∧
              (a.toNat = 0 → rf.1.toNat = 0) ∧
              (a.toNat ≠ 0 → (a.toNat * rf.1.toNat) % p = 1) ⦄ := by
    unfold field.verified.invert.invert
    step as ⟨b, hbm⟩
    step as ⟨u, hu1⟩
    step as ⟨v, hv0⟩
    step as ⟨i, hi⟩
    step as ⟨iter, hits, hite, hitex⟩
    have hpodd : p % 2 = 1 := by norm_num [p]
    have hinv0 : Inv a.toNat a b u v := by
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [hbm]; exact hpodd
      · rw [hu1]; exact one_lt_p.le
      · rw [hv0]; exact Nat.zero_le p
      · rw [hu1, Nat.cast_one, one_mul]
      · rw [hbm, hv0, Nat.cast_zero, zero_mul, ZMod.natCast_self]
      · rw [hbm]
      · exact ha.le
      · exact le_of_eq hbm
      · intro hy
        exact ⟨hy, hv0⟩
    have hpass : passes iter = 3 := by
      rw [passes_not_exhausted hitex, hite, hi, hits]
      simp
    have h0 := invert_loop0_spec a.toNat 126 iter a b u v hinv0 (by
      rw [hpass, hbm]
      have h510 : 126 + 128 * 3 = 510 := by norm_num
      rw [h510]
      calc a.toNat * p < 2^255 * 2^255 :=
            Nat.mul_lt_mul_of_lt_of_lt (lt_trans ha p_lt_two_pow_255) p_lt_two_pow_255
        _ = 2^510 := by rw [← pow_add]
      )
    refine WP.spec_bind h0 ?_
    rintro ⟨a1, b1, u1, v1⟩ ⟨hinv1, hpot1⟩
    try simp only at hinv1 hpot1
    step as ⟨bits, hbits⟩
    step as ⟨i2, hi2⟩
    have hi2v : i2.val = 128 := by
      rw [hi2, usize_wrapping_mul_val (by simp [hbits])]
      simp [hbits]
    step as ⟨i3, hi3⟩
    have hi3v : i3.val = 126 := by
      rw [hi3, usize_wrapping_sub_val (by simp; omega)]
      rw [hi2v]
      simp
    have h1 := invert_loop1_spec a.toNat { start := 0#usize, «end» := i3 } a1 b1 u1 v1
      hinv1 (by
        have harg : i3.val - (0#usize).val = 126 := by rw [hi3v]; simp
        rw [harg]
        exact hpot1)
    refine WP.spec_bind h1 ?_
    intro v2 hv2
    obtain ⟨hv2p, hv2c, hv2z⟩ := hv2
    have hred := red1_spec v2 (by have := p_pos; omega)
    refine WP.spec_bind hred ?_
    intro r hr
    have hz := ffield_is_zero_spec a
    refine WP.spec_bind hz ?_
    intro c hc
    step as ⟨c1, hc1⟩
    step as ⟨res, hres⟩
    rw [hres]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hr]
      exact Nat.mod_lt _ p_pos
    · rw [hc1]
      rcases c with _ | _ <;> simp_all
    · intro h0
      rw [hr, hv2z h0, Nat.zero_mod]
    · intro hne
      have hp : Nat.Prime p := p_prime
      have hgcd1 : Nat.gcd a.toNat p = 1 := by
        have hnd : ¬ p ∣ a.toNat := fun hdvd =>
          absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd) (by omega)
        have hcop := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
        exact Nat.Coprime.gcd_eq_one hcop.symm
      rw [hgcd1, Nat.cast_one] at hv2c
      have hzr : ((a.toNat * r.toNat : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
        push_cast
        rw [hr, ZMod.natCast_mod, mul_comm]
        exact hv2c.symm
      have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hzr
      rwa [Nat.mod_eq_of_lt one_lt_p] at hmod
  obtain ⟨rf, heq, hpost⟩ := WP.spec_imp_exists hspec
  exact ⟨rf.1, rf.2, heq, hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2⟩

end HelioseleneSpec
