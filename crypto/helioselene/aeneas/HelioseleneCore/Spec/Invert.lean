/- Specification of `field.verified.invert.invert` — constant-time modular inversion by
   binary GCD (Algorithm 1 of "Optimized Binary GCD for Modular Inversion",
   https://eprint.iacr.org/2020/972), 510 fixed iterations of the branch-free `step`.

   Exported contract lemma (namespace `HelioseleneSpec`): `invert_ok`.

   Proof status:
   * PROVED (no `sorry` in their dependency cone): `sub_with_bounded_overflow_spec`,
     `add_with_bounded_overflow_spec`, `select_word_spec`/`select_loop_spec`/`select_spec`
     (the masked 4-limb select), totality of every inner loop of `step`
     (`step_loop0_total` … `step_loop4_total`), totality + zero-propagation of `step`
     itself (`step_basic_spec`, `step_total`), and the local `sub_value_spec`,
     `red1_loop_spec`, `red1_spec`, `is_zero_loop_spec`, `is_zero_spec` specs.
   * SORRIED (exactly one `sorry` in this file): `step_congruence` — the per-step
     preservation of the Algorithm-1 invariant (congruences `a ≡ u·value`,
     `b ≡ v·value (mod p)`, oddness of `b`, ranges of `u`,`v`, gcd preservation and the
     potential halving `2·a'·b' ≤ a·b`).  `step_spec`, the three loop-induction lemmas
     and `invert_ok` are fully assembled around it, so discharging that single lemma
     completes the verification of inversion.

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
    (u u_sub_v : Uint4) (should_negate add_one_modulus carry : Limb)
    (hend : iter.«end».val ≤ 4) (hc : carry.val ≤ 1) :
    field.verified.invert.invert.step_loop4 iter u u_sub_v should_negate
      add_one_modulus carry
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
        step as ⟨mi, hmi⟩
        step as ⟨a2, ha2⟩
        subst ha2
        step as ⟨l2, hl2⟩
        step as ⟨l3, hl3⟩
        step as ⟨l4, carry1, hadd, hc1⟩
        step as ⟨a3, back, ha3, hback⟩
        subst ha3
        step as ⟨a4, ha4⟩
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
  step as ⟨a4, ha4⟩
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = 3 := by
    rw [hi2, usize_wrapping_sub_val (by rw [hi]; simp), hi4]
    simp
  step as ⟨l5, hl5⟩
  step as ⟨i3, hi3⟩
  step as ⟨i4, hi4'⟩
  have hi4v : i4.val = 63 := by
    rw [hi4', usize_wrapping_sub_val (by rw [hi3]; simp), hi3]
    simp
  step as ⟨l6, hl6⟩
  step as ⟨l7, hl7⟩
  step as ⟨a5, back, ha5, hback⟩
  step as ⟨i5, hi5⟩
  have hi5v : i5.val = 3 := by
    rw [hi5, usize_wrapping_sub_val (by rw [hi]; simp), hi4]
    simp
  step as ⟨a6, ha6⟩
  step with select_spec as ⟨v1, hv1sel⟩
  step as ⟨a7, ha7⟩
  simp only [hback]
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

/-! ## The Algorithm-1 step invariant (task item 3: statement + one `sorry`)

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
    the inverted value `y`. -/
def InvA (y : ℕ) (a b u v : Uint4) : Prop :=
  b.toNat % 2 = 1 ∧
  u.toNat ≤ p ∧
  v.toNat ≤ p ∧
  ((a.toNat : ZMod p) = (u.toNat : ZMod p) * (y : ZMod p)) ∧
  ((b.toNat : ZMod p) = (v.toNat : ZMod p) * (y : ZMod p)) ∧
  Nat.gcd a.toNat b.toNat = Nat.gcd y p

/-- Full loop invariant: `InvA` plus zero-propagation (for `y = 0` the working value `a`
    and the output accumulator `v` stay `0`; this clause is discharged by the *proved*
    `step_basic_spec`, not by the sorried congruence lemma).  A structure (rather than a
    conjunction) so that tactic normalization cannot flatten it. -/
structure Inv (y : ℕ) (a b u v : Uint4) : Prop where
  invA : InvA y a b u v
  zero : y = 0 → a.toNat = 0 ∧ v.toNat = 0

/-- **THE one `sorry` of this file**: one `step` preserves the arithmetic invariant and
    halves the potential `a·b`. -/
theorem step_congruence (y : ℕ) (a b u v : Uint4) (h : InvA y a b u v) :
    field.verified.invert.invert.step a b u v
      ⦃ s => InvA y s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
             2 * (s.1.toNat * s.2.1.toNat) ≤ a.toNat * b.toNat ⦄ := by
  /- PROOF OBLIGATION (per-step correctness of eprint 2020/972 Algorithm 1; this is the
     analogue of the Veridise Dafny per-iteration lemmas for `invert::step` in
     https://github.com/VeridiseAuditing/helioselene-dafny-proofs — the repository the
     Rust comments cite for `sub_with_bounded_overflow` (crypto_bigint_0_5_5/Limb.dfy
     L342-355) and `select` (helioselene/field/Base.dfy L238-264); the remaining
     obligations correspond to its lemmas about the borrow-chain subtraction, the
     conditional two's-complement negation, and the fused negate-and-add-modulus carry
     chain of `step`.)

     Value-level facts to establish about the branch-free code (all loops are 4- resp.
     2-limb chains of `sub_with_bounded_overflow` / `overflowing_add` /
     `add_with_bounded_overflow`, already given exact per-limb specs above; what is
     missing is lifting them to `Uint.toNat` by induction over the limb index, in the
     style of `select_loop_spec`):

     1. `step_loop0` computes `a_sub_b` with
        `a_sub_b.toNat + b.toNat = a.toNat + 2^256·borrow` and `borrow = 1 ↔ a < b`
        (multiprecision subtraction chain; `a_lt_b = -borrow` is then the 0/all-ones
        comparison mask).
     2. `step_loop1` (XOR with `a_lt_b` + carry seeded `1 & a_lt_b`) yields
        `a_diff_b.toNat = |a.toNat - b.toNat|` — conditional two's-complement negation:
        for `a < b`, `¬x + 1 = 2^256 - x` on the wrapped difference `x`.
     3. `step_loop2` computes `u_sub_v` with
        `u_sub_v.toNat ≡ u.toNat - (a odd ? v.toNat : 0) (mod 2^256)` plus its borrow.
     4. `step_loop3`/`step_loop4` + the final top-bit OR compute (writing
        `w = ±(u - v_masked)` for the value selected by `should_negate`)
        `u_new_pre = w + (add_one ? p : 0) + (add_two ? p : 0)` exactly in `[0, 2^256)`:
        the masked-addend trick `(MODULUS & add_one) ^^^ (MODULUS_XOR_TWO_MODULUS & add_two)`
        equals `p` resp. `2p` limb-wise because `add_two → add_one`
        (`add_two = neg ∧ ¬odd`, `add_one = neg ∨ odd`), and in the high limbs `2p`
        differs from `p` exactly in bit 255 (`MODULUS_XOR_TWO_MODULUS_spec` gives the
        constant's value `p ^^^ 2p`).  The chosen number of copies of `p` makes
        `u_new_pre` nonnegative and even, and `u_new_pre ≤ v_masked's p + 2p < 2^256`.
     5. The closing shifts give `a' = (a odd ? |a-b| : a)/2` (exact: the dividend is
        even — both operands odd in the subtraction case) and `u' = u_new_pre/2 ≤ p`.

     From these, invariant preservation is the classical Algorithm-1 argument:
     * swap case (`a` odd, `a < b`): `b' = a`, `v' = u` preserve both congruences;
       `2a' = b - a ≡ (v - u)·y`, and `2u' ≡ v - u (mod p)` by construction, so
       `a' ≡ u'·y` after cancelling the unit 2 of `ZMod p` (`p` odd).
     * subtract case (`a` odd, `a ≥ b`): `2a' = a - b ≡ (u - v)·y` and `2u' ≡ u - v`.
     * even case: `2a' = a`, `2u' ≡ u`, `b' = b`, `v' = v`.
     * oddness of `b'`: `b' = b` odd, or `b' = a`, odd in the swap case.
     * `u', v' ∈ [0, p]`: `v' ∈ {v, u}`; `u' = u_new_pre/2` with `u_new_pre ≤ 2p` even.
     * gcd: swaps, subtraction of the odd `b` from the odd `a`, and halving the even
       member against the odd `b'` preserve `Nat.gcd`.
     * potential: `2·a'·b' ≤ a·b` in all three cases (subtract/swap cases because
       `(a-b)·b < a·b` resp. `(b-a)·a < b·a`; even case with equality). -/
  sorry

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
        obtain ⟨hodd, hu, hv, hca, hcb, hgcd⟩ := hinv'.invA
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

    Depends on the single `sorry` in `Invert.step_congruence` (the per-step Algorithm-1
    invariant); everything else — totality, the loop inductions over all 510 iterations,
    the final reduction and flag computation — is proved. -/
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
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [hbm]; exact hpodd
      · rw [hu1]; exact one_lt_p.le
      · rw [hv0]; exact Nat.zero_le p
      · rw [hu1, Nat.cast_one, one_mul]
      · rw [hbm, hv0, Nat.cast_zero, zero_mul, ZMod.natCast_self]
      · rw [hbm]
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
