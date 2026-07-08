/- ZMod-level coordinate contracts for the Aeneas-translated Selene point operations.

   For every translated Selene point operation this file proves an `_ok` contract that
   drives the generated code down to explicit coordinate formulas over `ZMod p`, via the
   abstraction map

     `ψ : Uint4 → ZMod p`,  `ψ u = (u.toNat : ZMod p)`.

   Contents:
   * point plumbing: `Reduced` (all three coordinates `< p`), `mkψ P = (ψ P.x, ψ P.y, ψ P.z)`;
   * `addCoords`/`dblCoords`: the ZMod-level mirrors of the exact operation chains the
     code computes (RCB add-2015-rcb-3 for a = -3 with constant `b = Bcurve`, and
     dbl-2007-bl-2), as `let`-chains, plus `ring`-normalized closed polynomial forms
     (`addCoords_x/y/z`, `dblCoords_x/y/z`);
   * `add_coords_ok`, `sub_coords_ok`, `neg_coords_ok`, `double_coords_ok` (including the
     `is_identity`-driven conditional select: the result is `(0,1,0)` when `ψ P.x = 0`),
     `identity_coords`, `generator_coords`, `is_identity_ok`, `ct_eq_ok`, `eq_ok`,
     `curve_equation_ok`, `from_xy_ok`;
   * `sqrt_ok`: the field-level square-root contract (`flag = true ↔ ψ r ^ 2 = ψ a`,
     result reduced and even) — the `↔` comes from the final `res² ct_eq value` check in
     the generated code, WITHOUT relying on correctness of the windowed exponentiation
     ladder; and `recover_y_ok` on top of it.

   Sorry status: everything is PROVED except the single, clearly marked completeness
   obligation `sqrt_complete` (`IsSquare (ψ a) → flag = true`), which requires functional
   correctness of the 125-iteration windowed ladder (allowed fallback; the group-law
   development does not depend on it).

   No new axioms, no `native_decide`; lemmas that mention the generated hex-string
   constants inherit the `<const>._native.decide.ax_1` string-length axioms of Funs.lean
   (field layer plus, new with the Selene scope, `point.selene.B` / `point.selene.G_Y` /
   `field.verified.sqrt.MODULUS_PLUS_ONE_DIV_FOUR` — README §5c.3,
   human_audit_assumptions.txt VIII.3). -/
import HelioseleneCore.Spec.Selene.Curve
import HelioseleneCore.Spec.Linear
import HelioseleneCore.Spec.Reduction

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std Result
open helioselene

namespace HelioseleneSpec

namespace Selene

open crypto_bigint.uint HelioseleneModel

/-! ## The abstraction map `ψ : Uint4 → ZMod p` -/

/-- The coordinate abstraction map into `ZMod p` (total on `Uint4`; the intended domain
is reduced values `< p`, where it is injective). -/
def ψ (u : Uint4) : ZMod p := (u.toNat : ZMod p)

theorem ψ_def (u : Uint4) : ψ u = (u.toNat : ZMod p) := rfl

/-- On reduced values, `ψ` is injective (`ZMod.val` recovers `toNat`). -/
theorem ψ_inj_iff (a b : Uint4) (ha : a.toNat < p) (hb : b.toNat < p) :
    ψ a = ψ b ↔ a.toNat = b.toNat := by
  unfold ψ
  constructor
  · intro h
    have hval := congrArg ZMod.val h
    rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at hval
  · intro h; rw [h]

/-- On reduced values, `ψ a = 0` iff the representative is the zero word. -/
theorem ψ_eq_zero_iff (a : Uint4) (ha : a.toNat < p) : ψ a = 0 ↔ a.toNat = 0 := by
  unfold ψ
  rw [ZMod.natCast_eq_zero_iff]
  constructor
  · intro h; exact Nat.eq_zero_of_dvd_of_lt h ha
  · intro h; rw [h]; exact dvd_zero p

/-! ## Field-operation triples in `ψ` form

Each wraps the corresponding `_ok` contract (Spec/Linear, Spec/Reduction) as a
Hoare triple whose postcondition carries reducedness plus the `ψ`-hom equation. -/

private theorem mul_specψ (a b : Uint4) :
    field.HelioseleneField.Insts.CoreOpsArithMulHelioseleneFieldHelioseleneField.mul a b
      ⦃ r => r.toNat < p ∧ ψ r = ψ a * ψ b ⦄ := by
  obtain ⟨r, heq, hv⟩ := mul_ok a b
  rw [heq, WP.spec_ok]
  refine ⟨hv ▸ Nat.mod_lt _ p_pos, ?_⟩
  unfold ψ
  rw [hv, ZMod.natCast_mod]
  push_cast
  ring

private theorem square_specψ (a : Uint4) :
    field.HelioseleneField.Insts.FfField.square a
      ⦃ r => r.toNat < p ∧ ψ r = ψ a * ψ a ⦄ := by
  unfold field.HelioseleneField.Insts.FfField.square
  obtain ⟨r, heq, hv⟩ := square_ok a
  rw [heq, WP.spec_ok]
  refine ⟨hv ▸ Nat.mod_lt _ p_pos, ?_⟩
  unfold ψ
  rw [hv, ZMod.natCast_mod]
  push_cast
  ring

private theorem add_specψ (a b : Uint4) (ha : a.toNat < p) (hb : b.toNat < p) :
    field.HelioseleneField.Insts.CoreOpsArithAddHelioseleneFieldHelioseleneField.add a b
      ⦃ r => r.toNat < p ∧ ψ r = ψ a + ψ b ⦄ := by
  obtain ⟨r, heq, hv⟩ := add_ok a b ha hb
  rw [heq, WP.spec_ok]
  refine ⟨hv ▸ Nat.mod_lt _ p_pos, ?_⟩
  unfold ψ
  rw [hv, ZMod.natCast_mod]
  push_cast
  ring

private theorem sub_specψ (a b : Uint4) (ha : a.toNat < p) (hb : b.toNat < p) :
    field.HelioseleneField.Insts.CoreOpsArithSubHelioseleneFieldHelioseleneField.sub a b
      ⦃ r => r.toNat < p ∧ ψ r = ψ a - ψ b ⦄ := by
  obtain ⟨r, heq, hv⟩ := sub_ok a b ha hb
  rw [heq, WP.spec_ok]
  refine ⟨hv ▸ Nat.mod_lt _ p_pos, ?_⟩
  unfold ψ
  rw [hv, ZMod.natCast_mod]
  push_cast [Nat.cast_sub (le_of_lt hb)]
  rw [ZMod.natCast_self]
  ring

private theorem neg_specψ (a : Uint4) (ha : a.toNat < p) :
    field.HelioseleneField.Insts.CoreOpsArithNegHelioseleneField.neg a
      ⦃ r => r.toNat < p ∧ ψ r = -ψ a ⦄ := by
  obtain ⟨r, heq, hv⟩ := neg_ok a ha
  rw [heq, WP.spec_ok]
  refine ⟨hv ▸ Nat.mod_lt _ p_pos, ?_⟩
  unfold ψ
  rw [hv, ZMod.natCast_mod]
  push_cast [Nat.cast_sub (le_of_lt ha)]
  rw [ZMod.natCast_self]
  ring

private theorem double_specψ (a : Uint4) (ha : a.toNat < p) :
    field.HelioseleneField.Insts.FfField.double a
      ⦃ r => r.toNat < p ∧ ψ r = 2 * ψ a ⦄ := by
  unfold field.HelioseleneField.Insts.FfField.double
  obtain ⟨r, heq, hv⟩ := double_ok a ha
  rw [heq, WP.spec_ok]
  refine ⟨hv ▸ Nat.mod_lt _ p_pos, ?_⟩
  unfold ψ
  rw [hv, ZMod.natCast_mod]
  push_cast
  ring

private theorem B_specψ :
    point.selene.B ⦃ b => b.toNat < p ∧ ψ b = (Bcurve : ZMod p) ⦄ := by
  obtain ⟨b, heq, hv⟩ := B_ok
  rw [heq, WP.spec_ok]
  exact ⟨hv ▸ Bcurve_lt_p, by unfold ψ; rw [hv]⟩

private theorem FfZERO_spec :
    field.HelioseleneField.Insts.FfField.ZERO ⦃ z => z.toNat = 0 ⦄ := by
  unfold field.HelioseleneField.Insts.FfField.ZERO
  obtain ⟨z, heq, hv⟩ := Uint.ZERO_ok 4#usize
  rw [heq]
  simp only [bind_tc_ok, WP.spec_ok]
  exact hv

private theorem FfONE_spec :
    field.HelioseleneField.Insts.FfField.ONE ⦃ o => o.toNat = 1 ⦄ := by
  unfold field.HelioseleneField.Insts.FfField.ONE
  obtain ⟨o, heq, hv⟩ := Uint.ONE_ok 4#usize (by simp)
  rw [heq]
  simp only [bind_tc_ok, WP.spec_ok]
  exact hv

/-- The field-level constant-time equality is `toNat`-equality (via the `Uint` model). -/
private theorem fct_eq_spec (a b : Uint4) :
    field.HelioseleneField.Insts.SubtleConstantTimeEq.ct_eq a b
      ⦃ c => c = (a.toNat == b.toNat) ⦄ := by
  unfold field.HelioseleneField.Insts.SubtleConstantTimeEq.ct_eq
  exact (WP.spec_ok _).mpr rfl

/-- `ψ`-level form of the field constant-time equality on reduced inputs. -/
private theorem fct_eq_specψ (a b : Uint4) (ha : a.toNat < p) (hb : b.toNat < p) :
    field.HelioseleneField.Insts.SubtleConstantTimeEq.ct_eq a b
      ⦃ c => c = true ↔ ψ a = ψ b ⦄ := by
  apply WP.spec_mono (fct_eq_spec a b)
  intro c hc
  rw [hc, beq_iff_eq, ψ_inj_iff a b ha hb]

private theorem is_zero_specψ (a : Uint4) (ha : a.toNat < p) :
    field.HelioseleneField.Insts.FfField.is_zero a ⦃ c => c = true ↔ ψ a = 0 ⦄ := by
  unfold field.HelioseleneField.Insts.FfField.is_zero
  apply WP.spec_mono (is_zero_spec a)
  intro c hc
  rw [hc, ψ_eq_zero_iff a ha]

/-- `subtle::Choice` conjunction (model: `Bool.and`). -/
private theorem choice_and_spec (a b : subtle.Choice) :
    subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand a b ⦃ c => c = (a && b) ⦄ :=
  (WP.spec_ok _).mpr rfl

/-- `subtle::Choice` disjunction (model: `Bool.or`). -/
private theorem choice_or_spec (a b : subtle.Choice) :
    subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor a b ⦃ c => c = (a || b) ⦄ :=
  (WP.spec_ok _).mpr rfl

/-- Generic spec for `lift`ed pure values. -/
private theorem lift_spec {α : Type u} (x : α) : Aeneas.Std.lift x ⦃ y => y = x ⦄ :=
  (WP.spec_ok _).mpr rfl

/-! ## Point plumbing -/

/-- A `SelenePoint` is *reduced* when all three coordinates are `< p`. -/
def Reduced (P : point.selene.SelenePoint) : Prop :=
  P.x.toNat < p ∧ P.y.toNat < p ∧ P.z.toNat < p

/-- The `ψ`-image of a point's projective coordinate triple. -/
abbrev mkψ (P : point.selene.SelenePoint) : ZMod p × ZMod p × ZMod p :=
  (ψ P.x, ψ P.y, ψ P.z)

theorem mkψ_def (P : point.selene.SelenePoint) : mkψ P = (ψ P.x, ψ P.y, ψ P.z) := rfl

/-! ## ZMod-level coordinate formulas

`addCoords` mirrors — operation by operation, in the code's order — the complete
addition chain of `SelenePoint::add` (RCB 2015, algorithm 4 shape, `a = -3`, constant
`b = Bcurve`); `dblCoords` mirrors `Group::double`'s dbl-2007-bl-2 chain (before the
identity fix-up select, which `double_coords_ok` handles as a top-level `if`). -/

/-- ZMod-level mirror of the translated RCB addition chain. Argument order:
`(x1, y1, z1)` = self, `(x2, y2, z2)` = other. -/
def addCoords (x1 y1 z1 x2 y2 z2 : ZMod p) : ZMod p × ZMod p × ZMod p :=
  let b : ZMod p := (Bcurve : ZMod p)
  let t0 := x1 * x2
  let t1 := y1 * y2
  let t2 := z1 * z2
  let t3 := (x1 + y1) * (x2 + y2) - (t0 + t1)   -- x1·y2 + x2·y1
  let t4 := (y1 + z1) * (y2 + z2) - (t1 + t2)   -- y1·z2 + y2·z1
  let t5 := (x1 + z1) * (x2 + z2) - (t0 + t2)   -- x1·z2 + x2·z1
  let u := t5 - b * t2
  let v := u + 2 * u                             -- 3·(t5 - b·t2)
  let zc := t1 - v
  let xc := t1 + v
  let w := b * t5 - (2 * t2 + t2) - t0
  let ww := 2 * w + w                            -- 3·(b·t5 - 3·t2 - t0)
  let s := 2 * t0 + t0 - (2 * t2 + t2)           -- 3·t0 - 3·t2
  (t3 * xc - t4 * ww, xc * zc + s * ww, t4 * zc + t3 * s)

/-- ZMod-level mirror of the translated dbl-2007-bl-2 doubling chain (generic branch;
the identity branch is handled by the `if` in `double_coords_ok`). -/
def dblCoords (x y z : ZMod p) : ZMod p × ZMod p × ZMod p :=
  let m := (x - z) * (x + z)
  let w := 2 * m + m                             -- 3·(x² - z²)
  let s := 2 * (y * z)
  let sss := s * (s * s)
  let r := y * s
  let b := 2 * (x * r)
  let h := w * w - 2 * b
  (h * s, w * (b - h) - 2 * (r * r), sss)

/-! ### Normalized closed forms (for the group-law development) -/

theorem addCoords_x (x1 y1 z1 x2 y2 z2 : ZMod p) :
    (addCoords x1 y1 z1 x2 y2 z2).1
      = (x1 * y2 + x2 * y1)
          * (y1 * y2 + 3 * (x1 * z2 + x2 * z1) - 3 * (Bcurve : ZMod p) * (z1 * z2))
        - 3 * (y1 * z2 + y2 * z1)
          * ((Bcurve : ZMod p) * (x1 * z2 + x2 * z1) - 3 * (z1 * z2) - x1 * x2) := by
  simp only [addCoords]
  ring

theorem addCoords_y (x1 y1 z1 x2 y2 z2 : ZMod p) :
    (addCoords x1 y1 z1 x2 y2 z2).2.1
      = (y1 * y2 + 3 * (x1 * z2 + x2 * z1) - 3 * (Bcurve : ZMod p) * (z1 * z2))
          * (y1 * y2 - 3 * (x1 * z2 + x2 * z1) + 3 * (Bcurve : ZMod p) * (z1 * z2))
        + (3 * (x1 * x2) - 3 * (z1 * z2)) * 3
          * ((Bcurve : ZMod p) * (x1 * z2 + x2 * z1) - 3 * (z1 * z2) - x1 * x2) := by
  simp only [addCoords]
  ring

theorem addCoords_z (x1 y1 z1 x2 y2 z2 : ZMod p) :
    (addCoords x1 y1 z1 x2 y2 z2).2.2
      = (y1 * z2 + y2 * z1)
          * (y1 * y2 - 3 * (x1 * z2 + x2 * z1) + 3 * (Bcurve : ZMod p) * (z1 * z2))
        + (x1 * y2 + x2 * y1) * (3 * (x1 * x2) - 3 * (z1 * z2)) := by
  simp only [addCoords]
  ring

theorem dblCoords_x (x y z : ZMod p) :
    (dblCoords x y z).1
      = (3 * (x ^ 2 - z ^ 2) * (3 * (x ^ 2 - z ^ 2)) - 8 * x * y ^ 2 * z) * (2 * y * z) := by
  simp only [dblCoords]
  ring

theorem dblCoords_y (x y z : ZMod p) :
    (dblCoords x y z).2.1
      = 3 * (x ^ 2 - z ^ 2)
          * (4 * x * y ^ 2 * z - (9 * (x ^ 2 - z ^ 2) ^ 2 - 8 * x * y ^ 2 * z))
        - 8 * y ^ 4 * z ^ 2 := by
  simp only [dblCoords]
  ring

theorem dblCoords_z (x y z : ZMod p) :
    (dblCoords x y z).2.2 = 8 * y ^ 3 * z ^ 3 := by
  simp only [dblCoords]
  ring

/-! ## Point addition (`SelenePoint::add`, RCB complete formulas) -/

private theorem add_coords_spec (P Q : point.selene.SelenePoint)
    (hP : Reduced P) (hQ : Reduced Q) :
    point.selene.SelenePoint.Insts.CoreOpsArithAddSelenePointSelenePoint.add P Q
      ⦃ R => Reduced R ∧
          mkψ R = addCoords (ψ P.x) (ψ P.y) (ψ P.z) (ψ Q.x) (ψ Q.y) (ψ Q.z) ⦄ := by
  obtain ⟨hPx, hPy, hPz⟩ := hP
  obtain ⟨hQx, hQy, hQz⟩ := hQ
  unfold point.selene.SelenePoint.Insts.CoreOpsArithAddSelenePointSelenePoint.add
  step with mul_specψ P.x Q.x as ⟨t0, ht0l, ht0⟩
  step with mul_specψ P.y Q.y as ⟨t1, ht1l, ht1⟩
  step with mul_specψ P.z Q.z as ⟨t2, ht2l, ht2⟩
  step with add_specψ P.x P.y hPx hPy as ⟨t3, ht3l, ht3⟩
  step with add_specψ Q.x Q.y hQx hQy as ⟨t4, ht4l, ht4⟩
  step with mul_specψ t3 t4 as ⟨t31, ht31l, ht31⟩
  step with add_specψ t0 t1 ht0l ht1l as ⟨t41, ht41l, ht41⟩
  step with sub_specψ t31 t41 ht31l ht41l as ⟨t32, ht32l, ht32⟩
  step with add_specψ P.y P.z hPy hPz as ⟨t42, ht42l, ht42⟩
  step with add_specψ Q.y Q.z hQy hQz as ⟨x3a, hx3al, hx3a⟩
  step with mul_specψ t42 x3a as ⟨t43, ht43l, ht43⟩
  step with add_specψ t1 t2 ht1l ht2l as ⟨x31, hx31l, hx31⟩
  step with sub_specψ t43 x31 ht43l hx31l as ⟨t44, ht44l, ht44⟩
  step with add_specψ P.x P.z hPx hPz as ⟨x32, hx32l, hx32⟩
  step with add_specψ Q.x Q.z hQx hQz as ⟨y3a, hy3al, hy3a⟩
  step with mul_specψ x32 y3a as ⟨x33, hx33l, hx33⟩
  step with add_specψ t0 t2 ht0l ht2l as ⟨y31, hy31l, hy31⟩
  step with sub_specψ x33 y31 hx33l hy31l as ⟨y32, hy32l, hy32⟩
  step with B_specψ as ⟨hfB, hhfBl, hhfB⟩
  step with mul_specψ hfB t2 as ⟨z3a, hz3al, hz3a⟩
  step with sub_specψ y32 z3a hy32l hz3al as ⟨x34, hx34l, hx34⟩
  step with double_specψ x34 hx34l as ⟨z31, hz31l, hz31⟩
  step with add_specψ x34 z31 hx34l hz31l as ⟨x35, hx35l, hx35⟩
  step with sub_specψ t1 x35 ht1l hx35l as ⟨z32, hz32l, hz32⟩
  step with add_specψ t1 x35 ht1l hx35l as ⟨x36, hx36l, hx36⟩
  step with mul_specψ hfB y32 as ⟨y33, hy33l, hy33⟩
  step with double_specψ t2 ht2l as ⟨t11, ht11l, ht11⟩
  step with add_specψ t11 t2 ht11l ht2l as ⟨t21, ht21l, ht21⟩
  step with sub_specψ y33 t21 hy33l ht21l as ⟨y34, hy34l, hy34⟩
  step with sub_specψ y34 t0 hy34l ht0l as ⟨y35, hy35l, hy35⟩
  step with double_specψ y35 hy35l as ⟨t12, ht12l, ht12⟩
  step with add_specψ t12 y35 ht12l hy35l as ⟨y36, hy36l, hy36⟩
  step with double_specψ t0 ht0l as ⟨t13, ht13l, ht13⟩
  step with add_specψ t13 t0 ht13l ht0l as ⟨t01, ht01l, ht01⟩
  step with sub_specψ t01 t21 ht01l ht21l as ⟨t02, ht02l, ht02⟩
  step with mul_specψ t44 y36 as ⟨t14, ht14l, ht14⟩
  step with mul_specψ t02 y36 as ⟨t22, ht22l, ht22⟩
  step with mul_specψ x36 z32 as ⟨y37, hy37l, hy37⟩
  step with add_specψ y37 t22 hy37l ht22l as ⟨y38, hy38l, hy38⟩
  step with mul_specψ t32 x36 as ⟨x37, hx37l, hx37⟩
  step with sub_specψ x37 t14 hx37l ht14l as ⟨x38, hx38l, hx38⟩
  step with mul_specψ t44 z32 as ⟨z33, hz33l, hz33⟩
  step with mul_specψ t32 t02 as ⟨t15, ht15l, ht15⟩
  step with add_specψ z33 t15 hz33l ht15l as ⟨z34, hz34l, hz34⟩
  refine ⟨⟨hx38l, hy38l, hz34l⟩, ?_⟩
  simp only [mkψ, addCoords, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [hx38, hx37, ht14, hy38, hy37, ht22, hz34, hz33, ht15, ht32, ht31, ht3,
      ht4, ht41, ht44, ht43, ht42, hx3a, hx31, hx36, hz32, hx35, hz31, hx34, hy32,
      hx33, hx32, hy3a, hy31, hz3a, hy36, ht12, hy35, hy34, hy33, ht21, ht11, ht02,
      ht01, ht13, hhfB, ht0, ht1, ht2]

/-- **Point addition drives to the RCB coordinate polynomials.** For reduced inputs the
translated `SelenePoint::add` returns `ok` with a reduced result whose `ψ`-coordinates
are exactly `addCoords` of the input coordinates. -/
theorem add_coords_ok (P Q : point.selene.SelenePoint) (hP : Reduced P) (hQ : Reduced Q) :
    ∃ R, point.selene.SelenePoint.Insts.CoreOpsArithAddSelenePointSelenePoint.add P Q
        = .ok R
      ∧ Reduced R
      ∧ mkψ R = addCoords (ψ P.x) (ψ P.y) (ψ P.z) (ψ Q.x) (ψ Q.y) (ψ Q.z) :=
  WP.spec_imp_exists (add_coords_spec P Q hP hQ)

/-! ## Negation and subtraction -/

private theorem neg_coords_spec (P : point.selene.SelenePoint) (hP : Reduced P) :
    point.selene.SelenePoint.Insts.CoreOpsArithNegSelenePoint.neg P
      ⦃ R => Reduced R ∧ mkψ R = (ψ P.x, -ψ P.y, ψ P.z) ⦄ := by
  obtain ⟨hPx, hPy, hPz⟩ := hP
  unfold point.selene.SelenePoint.Insts.CoreOpsArithNegSelenePoint.neg
  step with neg_specψ P.y hPy as ⟨ny, hnyl, hny⟩
  refine ⟨⟨hPx, hnyl, hPz⟩, ?_⟩
  exact hny

/-- **Point negation negates the `y`-coordinate.** -/
theorem neg_coords_ok (P : point.selene.SelenePoint) (hP : Reduced P) :
    ∃ R, point.selene.SelenePoint.Insts.CoreOpsArithNegSelenePoint.neg P = .ok R
      ∧ Reduced R ∧ mkψ R = (ψ P.x, -ψ P.y, ψ P.z) :=
  WP.spec_imp_exists (neg_coords_spec P hP)

/-- **Point subtraction is `add ∘ neg`**: the coordinates are `addCoords` of `P` and the
negated `Q`. -/
theorem sub_coords_ok (P Q : point.selene.SelenePoint) (hP : Reduced P) (hQ : Reduced Q) :
    ∃ R, point.selene.SelenePoint.Insts.CoreOpsArithSubSelenePointSelenePoint.sub P Q
        = .ok R
      ∧ Reduced R
      ∧ mkψ R = addCoords (ψ P.x) (ψ P.y) (ψ P.z) (ψ Q.x) (-ψ Q.y) (ψ Q.z) := by
  obtain ⟨N, hNeq, hNred, hNco⟩ := neg_coords_ok Q hQ
  obtain ⟨R, hReq, hRred, hRco⟩ := add_coords_ok P N hP hNred
  refine ⟨R, ?_, hRred, ?_⟩
  · unfold point.selene.SelenePoint.Insts.CoreOpsArithSubSelenePointSelenePoint.sub
    rw [hNeq]
    simp only [bind_tc_ok]
    exact hReq
  · rw [hRco]
    simp only [mkψ, Prod.mk.injEq] at hNco
    rw [hNco.1, hNco.2.1, hNco.2.2]

/-! ## Identity, generator, `is_identity` -/

private theorem identity_spec :
    point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.identity
      ⦃ I => I.x.toNat = 0 ∧ I.y.toNat = 1 ∧ I.z.toNat = 0 ⦄ := by
  unfold point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.identity
  step with FfZERO_spec as ⟨z, hz⟩
  step with FfONE_spec as ⟨o, ho⟩
  exact ⟨hz, ho, hz⟩

/-- **The translated identity has coordinates `(0, 1, 0)`.** -/
theorem identity_coords :
    ∃ I, point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.identity = .ok I
      ∧ Reduced I ∧ I.x.toNat = 0 ∧ I.y.toNat = 1 ∧ I.z.toNat = 0
      ∧ mkψ I = (0, 1, 0) := by
  obtain ⟨I, heq, h0, h1, h2⟩ := WP.spec_imp_exists identity_spec
  refine ⟨I, heq, ⟨?_, ?_, ?_⟩, h0, h1, h2, ?_⟩
  · rw [h0]; exact p_pos
  · rw [h1]; exact one_lt_p
  · rw [h2]; exact p_pos
  · simp only [mkψ, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> unfold ψ
    · rw [h0]; exact Nat.cast_zero
    · rw [h1]; exact Nat.cast_one
    · rw [h2]; exact Nat.cast_zero

/-- **The translated generator has coordinates `(1, gY, 1)`.** -/
theorem generator_coords :
    ∃ G, point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.generator = .ok G
      ∧ Reduced G ∧ G.x.toNat = 1 ∧ G.y.toNat = gY ∧ G.z.toNat = 1
      ∧ mkψ G = (1, (gY : ZMod p), 1) := by
  obtain ⟨G, heq, hx, hy, hz⟩ := G_ok
  refine ⟨G, ?_, ⟨?_, ?_, ?_⟩, hx, hy, hz, ?_⟩
  · unfold point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.generator
    exact heq
  · rw [hx]; exact one_lt_p
  · rw [hy]; exact gY_lt_p
  · rw [hz]; exact one_lt_p
  · simp only [mkψ, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> unfold ψ
    · rw [hx]; exact Nat.cast_one
    · rw [hy]
    · rw [hz]; exact Nat.cast_one

/-- Raw (`toNat`-level, `BEq`) form of the `is_identity` test: it computes
`self.x == 0`. -/
private theorem is_identity_beq_spec (P : point.selene.SelenePoint) :
    point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.is_identity P
      ⦃ c => c = (P.x.toNat == 0) ⦄ := by
  unfold point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.is_identity
  step with FfZERO_spec as ⟨z, hz⟩
  apply WP.spec_mono (fct_eq_spec P.x z)
  intro c hc
  rw [hc, hz]

/-- **`is_identity` tests `x = 0`** (sound as an identity test because `B` is a
non-residue, `Curve.lean`; note it does NOT test `z = 0`). -/
theorem is_identity_ok (P : point.selene.SelenePoint) (hP : Reduced P) :
    ∃ c, point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.is_identity P
        = .ok c
      ∧ (c = true ↔ ψ P.x = 0) := by
  obtain ⟨c, heq, hc⟩ := WP.spec_imp_exists (is_identity_beq_spec P)
  refine ⟨c, heq, ?_⟩
  rw [hc, beq_iff_eq, ψ_eq_zero_iff P.x hP.1]

/-! ## Doubling (dbl-2007-bl-2 with the identity fix-up select) -/

/-- The `SelenePoint`-level constant-time select is the componentwise `if`. -/
private theorem point_select_spec (A B : point.selene.SelenePoint) (c : subtle.Choice) :
    point.selene.SelenePoint.Insts.SubtleConditionallySelectable.conditional_select A B c
      ⦃ R => R = if c then B else A ⦄ := by
  by_cases hc : c = true
  · simp only [hc, ↓reduceIte]
    exact (WP.spec_ok _).mpr rfl
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).mpr rfl

private theorem double_coords_spec (P : point.selene.SelenePoint) (hP : Reduced P) :
    point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.double P
      ⦃ R => Reduced R ∧
          mkψ R = if ψ P.x = 0 then ((0 : ZMod p), (1 : ZMod p), (0 : ZMod p))
                  else dblCoords (ψ P.x) (ψ P.y) (ψ P.z) ⦄ := by
  obtain ⟨hPx, hPy, hPz⟩ := hP
  unfold point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.double
  step with sub_specψ P.x P.z hPx hPz as ⟨d1, hd1l, hd1⟩
  step with add_specψ P.x P.z hPx hPz as ⟨d2, hd2l, hd2⟩
  step with mul_specψ d1 d2 as ⟨w, hwl, hw⟩
  step with double_specψ w hwl as ⟨d3, hd3l, hd3⟩
  step with add_specψ d3 w hd3l hwl as ⟨w1, hw1l, hw1⟩
  step with mul_specψ P.y P.z as ⟨d4, hd4l, hd4⟩
  step with double_specψ d4 hd4l as ⟨s, hsl, hs⟩
  step with square_specψ s as ⟨ss, hssl, hss⟩
  step with mul_specψ s ss as ⟨sss, hsssl, hsss⟩
  step with mul_specψ P.y s as ⟨r, hrl, hr⟩
  step with square_specψ r as ⟨rr, hrrl, hrr⟩
  step with mul_specψ P.x r as ⟨d5, hd5l, hd5⟩
  step with double_specψ d5 hd5l as ⟨b', hb'l, hb'⟩
  step with square_specψ w1 as ⟨d6, hd6l, hd6⟩
  step with double_specψ b' hb'l as ⟨d7, hd7l, hd7⟩
  step with sub_specψ d6 d7 hd6l hd7l as ⟨h', hh'l, hh'⟩
  step with mul_specψ h' s as ⟨X3, hX3l, hX3⟩
  step with sub_specψ b' h' hb'l hh'l as ⟨d8, hd8l, hd8⟩
  step with mul_specψ w1 d8 as ⟨d9, hd9l, hd9⟩
  step with double_specψ rr hrrl as ⟨d10, hd10l, hd10⟩
  step with sub_specψ d9 d10 hd9l hd10l as ⟨Y3, hY3l, hY3⟩
  step with identity_spec as ⟨sp, hspx, hspy, hspz⟩
  step with is_identity_beq_spec P as ⟨c, hc⟩
  step with point_select_spec { x := X3, y := Y3, z := sss } sp c as ⟨R, hR⟩
  by_cases hx0 : P.x.toNat = 0
  · have hct : c = true := by rw [hc, beq_iff_eq]; exact hx0
    simp only [hct, ↓reduceIte] at hR
    subst hR
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hspx]; exact p_pos
    · rw [hspy]; exact one_lt_p
    · rw [hspz]; exact p_pos
    · rw [if_pos ((ψ_eq_zero_iff P.x hPx).mpr hx0)]
      simp only [mkψ, Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩ <;> unfold ψ
      · rw [hspx]; exact Nat.cast_zero
      · rw [hspy]; exact Nat.cast_one
      · rw [hspz]; exact Nat.cast_zero
  · have hcf : c = false := by
      rw [hc]
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact hx0
    simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hR
    subst hR
    refine ⟨⟨hX3l, hY3l, hsssl⟩, ?_⟩
    rw [if_neg (fun h => hx0 ((ψ_eq_zero_iff P.x hPx).mp h))]
    simp only [mkψ, dblCoords, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [hX3, hh', hd6, hd7, hw1, hd3, hw, hd1, hd2, hb', hd5, hr, hs, hd4,
        hY3, hd9, hd8, hd10, hrr, hsss, hss]

/-- **Doubling drives to the dbl-2007-bl-2 coordinate polynomials**, with the
identity-flagged case (`is_identity`, i.e. `ψ P.x = 0`) returning `(0, 1, 0)`. -/
theorem double_coords_ok (P : point.selene.SelenePoint) (hP : Reduced P) :
    ∃ R, point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.double P = .ok R
      ∧ Reduced R
      ∧ mkψ R = if ψ P.x = 0 then ((0 : ZMod p), (1 : ZMod p), (0 : ZMod p))
                else dblCoords (ψ P.x) (ψ P.y) (ψ P.z) :=
  WP.spec_imp_exists (double_coords_spec P hP)

/-! ## Constant-time point equality and `PartialEq` -/

private theorem ct_eq_spec (P Q : point.selene.SelenePoint)
    (hP : Reduced P) (hQ : Reduced Q) :
    point.selene.SelenePoint.Insts.SubtleConstantTimeEq.ct_eq P Q
      ⦃ c => c = true ↔
          ((ψ P.x = 0 ∧ ψ Q.x = 0) ∨
           (ψ P.x * ψ Q.z = ψ Q.x * ψ P.z ∧ ψ P.y * ψ Q.z = ψ Q.y * ψ P.z)) ⦄ := by
  obtain ⟨hPx, hPy, hPz⟩ := hP
  obtain ⟨hQx, hQy, hQz⟩ := hQ
  unfold point.selene.SelenePoint.Insts.SubtleConstantTimeEq.ct_eq
  step with mul_specψ P.x Q.z as ⟨x1, hx1l, hx1⟩
  step with mul_specψ Q.x P.z as ⟨x2, hx2l, hx2⟩
  step with mul_specψ P.y Q.z as ⟨y1, hy1l, hy1⟩
  step with mul_specψ Q.y P.z as ⟨y2, hy2l, hy2⟩
  step with is_zero_specψ P.x hPx as ⟨c, hc⟩
  step with is_zero_specψ Q.x hQx as ⟨c1, hc1⟩
  step with choice_and_spec c c1 as ⟨c2, hc2⟩
  step with fct_eq_specψ x1 x2 hx1l hx2l as ⟨c3, hc3⟩
  step with fct_eq_specψ y1 y2 hy1l hy2l as ⟨c4, hc4⟩
  step with choice_and_spec c3 c4 as ⟨c5, hc5⟩
  apply WP.spec_mono (choice_or_spec c2 c5)
  intro cf hcf
  rw [hcf, hc2, hc5, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    hc, hc1, hc3, hc4, hx1, hx2, hy1, hy2]

/-- **`ct_eq` computes projective coordinate equality**: true iff both `x`-coordinates
are zero, or the cross-multiplied `x`- and `y`-coordinates agree. (Exactly the boolean
combination the code computes.) -/
theorem ct_eq_ok (P Q : point.selene.SelenePoint) (hP : Reduced P) (hQ : Reduced Q) :
    ∃ c, point.selene.SelenePoint.Insts.SubtleConstantTimeEq.ct_eq P Q = .ok c
      ∧ (c = true ↔
          ((ψ P.x = 0 ∧ ψ Q.x = 0) ∨
           (ψ P.x * ψ Q.z = ψ Q.x * ψ P.z ∧ ψ P.y * ψ Q.z = ψ Q.y * ψ P.z))) :=
  WP.spec_imp_exists (ct_eq_spec P Q hP hQ)

/-- **`PartialEq::eq` is `ct_eq` converted to `bool`** (the model conversion is the
identity), so it satisfies the same contract. -/
theorem eq_ok (P Q : point.selene.SelenePoint) (hP : Reduced P) (hQ : Reduced Q) :
    ∃ c, point.selene.SelenePoint.Insts.CoreCmpPartialEqSelenePoint.eq P Q = .ok c
      ∧ (c = true ↔
          ((ψ P.x = 0 ∧ ψ Q.x = 0) ∨
           (ψ P.x * ψ Q.z = ψ Q.x * ψ P.z ∧ ψ P.y * ψ Q.z = ψ Q.y * ψ P.z))) := by
  obtain ⟨c, heq, hc⟩ := ct_eq_ok P Q hP hQ
  refine ⟨c, ?_, hc⟩
  unfold point.selene.SelenePoint.Insts.CoreCmpPartialEqSelenePoint.eq
  rw [heq]
  simp only [bind_tc_ok]
  rfl

/-! ## `curve_equation` and `from_xy` -/

private theorem curve_equation_spec (x : Uint4) (hx : x.toNat < p) :
    point.selene.curve_equation x
      ⦃ r => r.toNat < p ∧
          ψ r = (ψ x * ψ x) * ψ x - 2 * ψ x - ψ x + (Bcurve : ZMod p) ⦄ := by
  unfold point.selene.curve_equation
  step with square_specψ x as ⟨s, hsl, hs⟩
  step with mul_specψ s x as ⟨cu, hcul, hcu⟩
  step with double_specψ x hx as ⟨d, hdl, hd⟩
  step with sub_specψ cu d hcul hdl as ⟨e, hel, he⟩
  step with sub_specψ e x hel hx as ⟨f, hfl, hf⟩
  step with B_specψ as ⟨b, hbl, hb⟩
  apply WP.spec_mono (add_specψ f b hfl hbl)
  intro r hr
  refine ⟨hr.1, ?_⟩
  rw [hr.2, hf, he, hcu, hs, hd, hb]

/-- **`curve_equation` computes the RHS of the curve equation**, exactly as the code
does: `(x·x)·x - 2·x - x + B`. -/
theorem curve_equation_ok (x : Uint4) (hx : x.toNat < p) :
    ∃ r, point.selene.curve_equation x = .ok r ∧ r.toNat < p
      ∧ ψ r = (ψ x * ψ x) * ψ x - 2 * ψ x - ψ x + (Bcurve : ZMod p) :=
  WP.spec_imp_exists (curve_equation_spec x hx)

/-- **`from_xy` builds `(x : y : 1)` and flags whether the affine curve equation
holds**: `y·y = (x·x)·x - 2·x - x + B`. -/
theorem from_xy_ok (x y : Uint4) (hx : x.toNat < p) (hy : y.toNat < p) :
    ∃ P flag, point.selene.SelenePoint.from_xy x y = .ok (P, flag)
      ∧ Reduced P ∧ mkψ P = (ψ x, ψ y, 1)
      ∧ (flag = true ↔
          ψ y * ψ y = (ψ x * ψ x) * ψ x - 2 * ψ x - ψ x + (Bcurve : ZMod p)) := by
  obtain ⟨o, hoeq, ho⟩ := WP.spec_imp_exists FfONE_spec
  obtain ⟨s, hseq, hsl, hs⟩ := WP.spec_imp_exists (square_specψ y)
  obtain ⟨r, hreq, hrl, hr⟩ := WP.spec_imp_exists (curve_equation_spec x hx)
  obtain ⟨c, hceq, hc⟩ := WP.spec_imp_exists (fct_eq_specψ s r hsl hrl)
  refine ⟨{ x := x, y := y, z := o }, c, ?_, ⟨hx, hy, by rw [ho]; exact one_lt_p⟩, ?_, ?_⟩
  · unfold point.selene.SelenePoint.from_xy
    rw [hoeq]
    simp only [bind_tc_ok]
    rw [hseq]
    simp only [bind_tc_ok]
    rw [hreq]
    simp only [bind_tc_ok]
    rw [hceq]
    simp only [bind_tc_ok]
    rfl
  · show (ψ x, ψ y, ψ o) = (ψ x, ψ y, 1)
    have h1 : ψ o = 1 := by unfold ψ; rw [ho]; exact Nat.cast_one
    rw [h1]
  · rw [hc, hs, hr]

/-! ## The field square root (`verified::sqrt`) and `recover_y` -/

private theorem mul_red (a b : Uint4) :
    field.HelioseleneField.Insts.CoreOpsArithMulHelioseleneFieldHelioseleneField.mul a b
      ⦃ r => r.toNat < p ⦄ := by
  obtain ⟨r, heq, hv⟩ := mul_ok a b
  rw [heq, WP.spec_ok, hv]
  exact Nat.mod_lt _ p_pos

private theorem square_red (a : Uint4) :
    field.HelioseleneField.Insts.FfField.square a ⦃ r => r.toNat < p ⦄ := by
  unfold field.HelioseleneField.Insts.FfField.square
  obtain ⟨r, heq, hv⟩ := square_ok a
  rw [heq, WP.spec_ok, hv]
  exact Nat.mod_lt _ p_pos

private theorem mul_shared_red (a b : Uint4) :
    field.HelioseleneField.Insts.CoreOpsArithMulShared0HelioseleneFieldHelioseleneField.mul
      a b ⦃ r => r.toNat < p ⦄ := by
  unfold field.HelioseleneField.Insts.CoreOpsArithMulShared0HelioseleneFieldHelioseleneField.mul
  exact mul_red a b

private theorem mul_assign_red (a b : Uint4) :
    field.HelioseleneField.Insts.CoreOpsArithMulAssignHelioseleneField.mul_assign a b
      ⦃ r => r.toNat < p ⦄ := by
  unfold field.HelioseleneField.Insts.CoreOpsArithMulAssignHelioseleneField.mul_assign
  exact mul_red a b

private theorem mul_assign_shared_red (a b : Uint4) :
    field.HelioseleneField.Insts.CoreOpsArithMulAssignShared0HelioseleneField.mul_assign a b
      ⦃ r => r.toNat < p ⦄ := by
  unfold field.HelioseleneField.Insts.CoreOpsArithMulAssignShared0HelioseleneField.mul_assign
  exact mul_shared_red a b

private theorem square_valψ (a : Uint4) :
    field.HelioseleneField.Insts.FfField.square a
      ⦃ r => r.toNat < p ∧ r.toNat = (a.toNat * a.toNat) % p ⦄ := by
  unfold field.HelioseleneField.Insts.FfField.square
  obtain ⟨r, heq, hv⟩ := square_ok a
  rw [heq, WP.spec_ok]
  exact ⟨hv ▸ Nat.mod_lt _ p_pos, hv⟩

-- U8 bit-fiddling value lemmas
private theorem u8_shl1_val (b : Std.U8) (hb : b.val < 128) :
    (Std.U8.wrapping_shl b 1#u32).val = 2 * b.val := by
  show ((Std.U8.wrapping_shl b 1#u32).bv).toNat = 2 * b.bv.toNat
  rw [Std.U8.wrapping_shl_bv_eq]
  rw [show ((1#u32).val % 8) = 1 from by simp]
  rw [show b.bv.shiftLeft 1 = b.bv <<< 1 from rfl]
  rw [BitVec.toNat_shiftLeft]
  have hb' : b.bv.toNat < 128 := hb
  rw [Nat.shiftLeft_eq]
  omega

private theorem u8_shl3_1_val : (Std.U8.wrapping_shl 1#u8 3#u32).val = 8 := by decide

private theorem and8_lt (n : ℕ) (h16 : n < 16) (h : n &&& 8 = 0) : n < 8 := by
  interval_cases n <;> revert h <;> decide

/-- `IteratorRange.next` on an `I32` range whose end stays `≤ 64` (the sqrt
squaring loops): merged some/none spec, mirroring the library's `next_Usize_spec`. -/
private theorem next_I32_spec (r : core.ops.range.Range Std.I32)
    (hb : r.«end».val ≤ 64) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32 r
    ⦃ (o : Option Std.I32) (r' : core.ops.range.Range Std.I32) =>
        (if r.start.val < r.«end».val
         then o = some r.start ∧ r'.start.val = r.start.val + 1
         else o = none ∧ r'.start = r.start) ∧ r'.«end» = r.«end» ⦄ := by
  by_cases hlt : r.start.val < r.«end».val
  · have hfwd : r.start.val + ((1#usize).val : ℤ) ≤ IScalar.max .I32 := by
      scalar_tac
    simp only [core.iter.range.IteratorRange.next, core.iter.range.StepI32,
      core.iter.range.IScalarStep, core.iter.range.IScalarStep.forward_checked,
      liftFun1, liftFun2, core.cmp.impls.PartialOrdI32.lt,
      core.clone.impls.CloneI32.clone, bind_tc_ok, decide_eq_true_eq, hlt,
      ↓reduceIte, hfwd, ↓reduceDIte, WP.spec_ok, WP.uncurry'_pair]
    refine ⟨⟨trivial, ?_⟩, trivial⟩
    simp
  · simp only [core.iter.range.IteratorRange.next, core.iter.range.StepI32,
      core.iter.range.IScalarStep, liftFun2, core.cmp.impls.PartialOrdI32.lt,
      bind_tc_ok, decide_eq_true_eq, hlt, ↓reduceIte, WP.spec_ok, WP.uncurry'_pair]
    exact ⟨⟨trivial, trivial⟩, trivial⟩

/-- The repeated-squaring loops of `sqrt` terminate with a reduced result. -/
private theorem sqrt_loop0_spec (iter : core.ops.range.Range Std.I32) (res : Uint4)
    (hend : iter.«end».val ≤ 64) (hres : res.toNat < p) :
    field.verified.sqrt.sqrt_loop0 iter res ⦃ r => r.toNat < p ⦄ := by
  unfold field.verified.sqrt.sqrt_loop0
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (st : core.ops.range.Range Std.I32 × field.HelioseleneField) =>
      (st.1.«end».val - st.1.start.val).toNat)
    (inv := fun st => st.1.«end».val ≤ 64 ∧ st.2.toNat < p)
  · rintro ⟨it1, res1⟩ ⟨he1, hr1⟩
    dsimp only at he1 hr1 ⊢
    unfold field.verified.sqrt.sqrt_loop0.body
    step with next_I32_spec it1 he1 as ⟨o, it2, ho, hoend⟩
    split at ho
    · rename_i hlt
      obtain ⟨ho1, hstart⟩ := ho
      simp only [ho1]
      step with square_red res1 as ⟨res2, hres2⟩
      refine ⟨by rw [hoend]; exact he1, hres2, ?_⟩
      rw [hoend, hstart]
      omega
    · obtain ⟨ho1, hstart⟩ := ho
      simp only [ho1, WP.spec_ok]
      exact hr1
  · exact ⟨hend, hres⟩

/-- The other three squaring loops are literal copies of `sqrt_loop0`. -/
private theorem sqrt_loop1_eq :
    field.verified.sqrt.sqrt_loop1 = field.verified.sqrt.sqrt_loop0 := rfl
private theorem sqrt_loop2_eq :
    field.verified.sqrt.sqrt_loop2 = field.verified.sqrt.sqrt_loop0 := rfl
private theorem sqrt_loop3_eq :
    field.verified.sqrt.sqrt_loop3 = field.verified.sqrt.sqrt_loop0 := rfl

/-- The 125-iteration windowed loop of `sqrt`: terminates, and the `bits` accumulator
stays `< 8` (so every table lookup stays in bounds). -/
private theorem sqrt_loop4_spec (iter : core.ops.range.Range Std.Usize)
    (table : Aeneas.Std.Array field.HelioseleneField 16#usize)
    (res : field.HelioseleneField) (bits : Std.U8)
    (limbs : Aeneas.Std.Array crypto_bigint.limb.Limb 4#usize)
    (hend : iter.«end».val = 125) (hbits : bits.val < 8) :
    field.verified.sqrt.sqrt_loop4 iter table res bits limbs
      ⦃ (r : field.HelioseleneField) (bs : Std.U8) => bs.val < 8 ⦄ := by
  unfold field.verified.sqrt.sqrt_loop4
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (st : core.ops.range.Range Std.Usize × field.HelioseleneField × Std.U8) =>
      125 - st.1.start.val)
    (inv := fun st => st.1.«end».val = 125 ∧ st.2.2.val < 8)
  · rintro ⟨it1, res1, bits1⟩ ⟨he1, hb1⟩
    dsimp only at he1 hb1 ⊢
    unfold field.verified.sqrt.sqrt_loop4.body
    step as ⟨o, it2, ho, hoend⟩
    split at ho
    · rename_i hlt
      obtain ⟨ho1, hstart⟩ := ho
      simp only [ho1]
      have hk : it1.start.val ≤ 124 := by omega
      step with lift_spec (Std.Usize.wrapping_sub 124#usize it1.start) as ⟨i, hi⟩
      have hiv : i.val = 124 - it1.start.val := by
        rw [hi]
        simp only [Usize.wrapping_sub_val_eq]
        have h124 : (124#usize).val = 124 := by simp
        rw [h124]
        have hsz : 2^32 ≤ UScalar.size .Usize := by
          rw [UScalar.size]
          rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h]
        have hstart_lt : it1.start.val < UScalar.size .Usize := by
          rw [UScalar.size]
          exact it1.start.hBounds
        have heq2 : 124 + (UScalar.size .Usize - it1.start.val)
            = (124 - it1.start.val) + UScalar.size .Usize := by omega
        rw [heq2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      step with lift_spec (Std.U8.wrapping_shl bits1 1#u32) as ⟨sh, hsh⟩
      have hshv : sh.val = 2 * bits1.val := by
        rw [hsh]; exact u8_shl1_val bits1 (by omega)
      step as ⟨i1, hi1⟩
      step as ⟨l, hl⟩
      step as ⟨i2, hi2⟩
      step with lift_spec (UScalar.cast .U32 i2) as ⟨i3, hi3⟩
      step with lift_spec (Std.U64.wrapping_shr l i3) as ⟨i4, hi4⟩
      step as ⟨i5, hi5v, hi5bv⟩
      step with lift_spec (UScalar.cast .U8 i5) as ⟨bit, hbit⟩
      have hbitv : bit.val ≤ 1 := by
        rw [hbit, UScalar.cast_val_eq]
        have hle : i5.val ≤ 1 := by
          rw [hi5v]
          simp only [UScalar.val_and]
          exact le_trans Nat.and_le_right (by simp)
        have h8 : i5.val % 2^UScalarTy.U8.numBits ≤ i5.val := Nat.mod_le _ _
        omega
      step as ⟨bits2, hbits2v, hbits2bv⟩
      simp only [UScalar.val_or] at hbits2v
      have hb16 : bits2.val < 16 := by
        have hor := Nat.or_lt_two_pow (x := sh.val) (y := bit.val) (n := 4)
          (by omega) (by omega)
        rw [hbits2v]
        omega
      step with square_red res1 as ⟨res2, hres2⟩
      step with lift_spec (Std.U8.wrapping_shl 1#u8 3#u32) as ⟨i6, hi6⟩
      have hi6v : i6.val = 8 := by rw [hi6]; exact u8_shl3_1_val
      step as ⟨i7, hi7v, hi7bv⟩
      simp only [UScalar.val_and] at hi7v
      split
      · -- window full: table multiply, reset bits to 0
        rename_i hne
        step with lift_spec (core.convert.num.FromUsizeU8.from bits2) as ⟨i8, hi8⟩
        have hi8v : i8.val = bits2.val := by
          rw [hi8]; exact core.convert.num.FromUsizeU8.from_val_eq bits2
        step with Aeneas.Std.Array.index_usize_spec table i8
          (by rw [hi8v]; scalar_tac) as ⟨hf, hhf⟩
        step with mul_assign_red res2 hf as ⟨res3, hres3⟩
        refine ⟨by rw [hoend]; exact he1, by simp, ?_⟩
        rw [hstart]
        omega
      · -- window not full: keep accumulating; bit 3 clear keeps bits2 < 8
        rename_i hzero
        simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hzero
        have hi7z : i7.val = 0 := by rw [hzero]; simp
        refine ⟨by rw [hoend]; exact he1, ?_, ?_⟩
        · apply and8_lt bits2.val hb16
          rw [← hi6v, ← hi7v]
          exact hi7z
        · rw [hstart]
          omega
    · obtain ⟨ho1, hstart⟩ := ho
      simp only [ho1, WP.spec_ok]
      exact hb1
  · exact ⟨hend, hbits⟩

/-- `(p + 1) / 4`, the exponent constant of `sqrt` (`p ≡ 3 (mod 4)`). -/
def mp4 : ℕ := 14474011154664524427946373126085988481655826483807673377251202393641830348757

private theorem mp4_lt : mp4 < 2^256 := by unfold mp4; norm_num

private theorem parse_MPODF
    (h : ("1ffffffffffffffffffffffffffffffffdcd5207465a7cc5fe6142da37c477d5" : String).toByteArray.size ≤ U32.max) :
    parseBeHex? ((toStr "1ffffffffffffffffffffffffffffffffdcd5207465a7cc5fe6142da37c477d5" h).val)
      = some 14474011154664524427946373126085988481655826483807673377251202393641830348757 := by
  rw [toStr_val]; decide

private theorem len_MPODF
    (h : ("1ffffffffffffffffffffffffffffffffdcd5207465a7cc5fe6142da37c477d5" : String).toByteArray.size ≤ U32.max) :
    ((toStr "1ffffffffffffffffffffffffffffffffdcd5207465a7cc5fe6142da37c477d5" h).val).length
      = 16 * (4#usize).val := by
  rw [toStr_val, usize4_val]; decide

private theorem MPODF_ok :
    ∃ u, field.verified.sqrt.MODULUS_PLUS_ONE_DIV_FOUR = ok u ∧ u.toNat = mp4 := by
  refine ⟨Uint.ofNat 4#usize mp4, ?_, Uint4.toNat_ofNat mp4_lt⟩
  unfold field.verified.sqrt.MODULUS_PLUS_ONE_DIV_FOUR
  rw [Uint.from_be_hex_ok _ _ mp4 (len_MPODF _) (parse_MPODF _)]
  rfl

private theorem ff_is_odd_spec (a : Uint4) :
    field.HelioseleneField.Insts.FfPrimeFieldArrayU832.is_odd a
      ⦃ c => c = true ↔ a.toNat % 2 = 1 ⦄ := by
  unfold field.HelioseleneField.Insts.FfPrimeFieldArrayU832.is_odd
  exact is_odd_spec a

private theorem fselect_spec (x y : Uint4) (c : subtle.Choice) :
    field.HelioseleneField.Insts.SubtleConditionallySelectable.conditional_select x y c
      ⦃ r => r = if c then y else x ⦄ := by
  unfold field.HelioseleneField.Insts.SubtleConditionallySelectable.conditional_select
  rw [Uint.conditional_select_ok]
  simp only [bind_tc_ok, WP.spec_ok]

private theorem shared_neg_spec (a : Uint4) (ha : a.toNat < p) :
    Shared0HelioseleneField.Insts.CoreOpsArithNegHelioseleneField.neg a
      ⦃ r => r.toNat = (p - a.toNat) % p ⦄ := by
  unfold Shared0HelioseleneField.Insts.CoreOpsArithNegHelioseleneField.neg
  exact neg_spec a ha

private theorem cond_negate_spec (a : Uint4) (ha : a.toNat < p) (c : subtle.Choice) :
    subtle.ConditionallyNegatable.Blanket.conditional_negate
      field.HelioseleneField.Insts.SubtleConditionallySelectable
      Shared0HelioseleneField.Insts.CoreOpsArithNegHelioseleneField a c
      ⦃ r => r.toNat = if c then (p - a.toNat) % p else a.toNat ⦄ := by
  unfold subtle.ConditionallyNegatable.Blanket.conditional_negate
  step with shared_neg_spec a ha as ⟨n, hn⟩
  apply WP.spec_mono (fselect_spec a n c)
  intro r hr
  by_cases hcb : c = true
  · rw [hr, if_pos hcb, if_pos hcb, hn]
  · rw [hr, if_neg hcb, if_neg hcb]

private theorem p_odd : p % 2 = 1 := by unfold p; norm_num

private theorem sqrt_spec (a : Uint4) (ha : a.toNat < p) :
    field.verified.sqrt.sqrt a
      ⦃ (r : field.HelioseleneField) (flag : Bool) =>
          r.toNat < p ∧ r.toNat % 2 = 0 ∧ (flag = true ↔ ψ r ^ 2 = ψ a) ⦄ := by
  unfold field.verified.sqrt.sqrt
  step with FfONE_spec as ⟨one, hone⟩
  step as ⟨table1, htable1⟩
  step with square_red a as ⟨hf1, hhf1⟩
  step as ⟨table2, htable2⟩
  step as ⟨hf2, hhf2⟩
  step with mul_shared_red hf2 a as ⟨hf3, hhf3⟩
  step as ⟨table3, htable3⟩
  step as ⟨hf4, hhf4⟩
  step with square_red hf4 as ⟨hf5, hhf5⟩
  step as ⟨table4, htable4⟩
  step as ⟨hf6, hhf6⟩
  step with mul_shared_red hf6 a as ⟨hf7, hhf7⟩
  step as ⟨table5, htable5⟩
  step as ⟨hf8, hhf8⟩
  step with square_red hf8 as ⟨hf9, hhf9⟩
  step as ⟨table6, htable6⟩
  step as ⟨hf10, hhf10⟩
  step with mul_shared_red hf10 a as ⟨hf11, hhf11⟩
  step as ⟨table7, htable7⟩
  step as ⟨hf12, hhf12⟩
  step with square_red hf12 as ⟨hf13, hhf13⟩
  step as ⟨table8, htable8⟩
  step as ⟨hf14, hhf14⟩
  step with mul_shared_red hf14 a as ⟨hf15, hhf15⟩
  step as ⟨table9, htable9⟩
  step as ⟨hf16, hhf16⟩
  step with square_red hf16 as ⟨hf17, hhf17⟩
  step as ⟨table10, htable10⟩
  step as ⟨hf18, hhf18⟩
  step with mul_shared_red hf18 a as ⟨hf19, hhf19⟩
  step as ⟨table11, htable11⟩
  step as ⟨hf20, hhf20⟩
  step with square_red hf20 as ⟨hf21, hhf21⟩
  step as ⟨table12, htable12⟩
  step as ⟨hf22, hhf22⟩
  step with mul_shared_red hf22 a as ⟨hf23, hhf23⟩
  step as ⟨table13, htable13⟩
  step as ⟨hf24, hhf24⟩
  step with square_red hf24 as ⟨hf25, hhf25⟩
  step as ⟨table14, htable14⟩
  step as ⟨hf26, hhf26⟩
  step with mul_shared_red hf26 a as ⟨hf27, hhf27⟩
  step as ⟨table15, htable15⟩
  step as ⟨res, hres⟩
  step with square_red res as ⟨fz, hfz⟩
  step with square_red fz as ⟨fzz, hfzz⟩
  step with square_red fzz as ⟨res1, hres1⟩
  step with square_red res1 as ⟨res2, hres2⟩
  step with mul_assign_shared_red res2 res as ⟨res3, hres3⟩
  step with sqrt_loop0_spec { start := 0#i32, «end» := 8#i32 } res3 (by simp) hres3
    as ⟨res4, hres4⟩
  step with mul_assign_shared_red res4 res3 as ⟨res5, hres5⟩
  rw [sqrt_loop1_eq]
  step with sqrt_loop0_spec { start := 0#i32, «end» := 16#i32 } res5 (by simp) hres5
    as ⟨res6, hres6⟩
  step with mul_assign_red res6 res5 as ⟨res7, hres7⟩
  rw [sqrt_loop2_eq]
  step with sqrt_loop0_spec { start := 0#i32, «end» := 32#i32 } res7 (by simp) hres7
    as ⟨res8, hres8⟩
  step with mul_assign_red res8 res7 as ⟨res9, hres9⟩
  rw [sqrt_loop3_eq]
  step with sqrt_loop0_spec { start := 0#i32, «end» := 64#i32 } res9 (by simp) hres9
    as ⟨res10, hres10⟩
  step with mul_assign_red res10 res9 as ⟨res11, hres11⟩
  obtain ⟨mp, hmpeq, hmpv⟩ := MPODF_ok
  rw [hmpeq]
  simp only [bind_tc_ok]
  rw [Uint.as_limbs_ok]
  simp only [bind_tc_ok]
  step with sqrt_loop4_spec { start := 0#usize, «end» := 125#usize } table15 res11 0#u8 mp
    (by simp) (by simp) as ⟨res12, bits, hbits⟩
  step with lift_spec (core.convert.num.FromUsizeU8.from bits) as ⟨idx, hidx⟩
  step with Aeneas.Std.Array.index_usize_spec table15 idx
    (by rw [hidx, core.convert.num.FromUsizeU8.from_val_eq]; scalar_tac) as ⟨hf29, hhf29⟩
  step with mul_assign_red res12 hf29 as ⟨res13, hres13⟩
  step with ff_is_odd_spec res13 as ⟨codd, hcodd⟩
  step with cond_negate_spec res13 hres13 codd as ⟨res14, hres14⟩
  step with square_valψ res14 as ⟨hf30, hhf30l, hhf30v⟩
  step with fct_eq_spec hf30 a as ⟨c1, hc1⟩
  rw [CtOption.new_ok]
  simp only [WP.spec_ok, WP.uncurry'_pair]
  have hres14l : res14.toNat < p := by
    rw [hres14]
    by_cases hcb : codd = true
    · rw [if_pos hcb]; exact Nat.mod_lt _ p_pos
    · rw [if_neg hcb]; exact hres13
  refine ⟨hres14l, ?_, ?_⟩
  · -- evenness from the conditional negate
    have hp2 := p_odd
    by_cases hcb : codd = true
    · have hodd : res13.toNat % 2 = 1 := hcodd.mp hcb
      have hlt : p - res13.toNat < p := by omega
      rw [hres14, if_pos hcb, Nat.mod_eq_of_lt hlt]
      omega
    · have heven : ¬ res13.toNat % 2 = 1 := fun h => hcb (hcodd.mpr h)
      rw [hres14, if_neg hcb]
      omega
  · -- the flag is exactly the final `res² = value` check
    rw [hc1, beq_iff_eq, ← ψ_inj_iff hf30 a hhf30l ha]
    have hsq : ψ hf30 = ψ res14 ^ 2 := by
      unfold ψ
      rw [hhf30v, ZMod.natCast_mod]
      push_cast
      rw [pow_two]
    rw [hsq]

/-- **The verified field square root (weak/soundness contract).** For a reduced input
the translated `sqrt` returns `ok (r, flag)` with `r` reduced and even, and the flag is
true iff `r` is a square root of the input (`flag ↔ ψ r ^ 2 = ψ a`, from the final
`ct_eq` self-check — no windowed-ladder correctness needed). Together with
`sqrt_complete` (the ladder obligation) this pins the flag to `IsSquare (ψ a)`.

**WARNING (false-flag direction).** The biconditional pins the flag only to the
RETURNED candidate `r`. Until `sqrt_complete` (currently `sorry`) is proved,
`flag = false` does NOT imply `ψ a` is a non-square: a consumer treating the flag as a
quadratic-residuosity oracle in the false direction would be relying on the `sorry`.
`flag = true → IsSquare (ψ a)` IS covered (take the witness `r`). -/
theorem sqrt_ok (a : Uint4) (ha : a.toNat < p) :
    ∃ r flag, field.HelioseleneField.Insts.FfField.sqrt a = .ok (r, flag)
      ∧ r.toNat < p ∧ r.toNat % 2 = 0 ∧ (flag = true ↔ ψ r ^ 2 = ψ a) := by
  obtain ⟨rf, heq, hpost⟩ := WP.spec_imp_exists (sqrt_spec a ha)
  obtain ⟨r, flag⟩ := rf
  simp only [WP.uncurry'_pair] at hpost
  refine ⟨r, flag, ?_, hpost.1, hpost.2.1, hpost.2.2⟩
  unfold field.HelioseleneField.Insts.FfField.sqrt
  exact heq

/-- **`recover_y` = `curve_equation` + `sqrt`.** The flag is true iff the returned `r`
satisfies `r² = x³ - 3x + B` (stated exactly as `curve_equation` computes the RHS). -/
theorem recover_y_ok (x : Uint4) (hx : x.toNat < p) :
    ∃ r flag, point.selene.recover_y x = .ok (r, flag)
      ∧ r.toNat < p ∧ r.toNat % 2 = 0
      ∧ (flag = true ↔
          ψ r ^ 2 = (ψ x * ψ x) * ψ x - 2 * ψ x - ψ x + (Bcurve : ZMod p)) := by
  obtain ⟨cq, hceq, hcl, hcv⟩ := curve_equation_ok x hx
  obtain ⟨r, flag, hseq, hrl, hre, hflag⟩ := sqrt_ok cq hcl
  refine ⟨r, flag, ?_, hrl, hre, ?_⟩
  · unfold point.selene.recover_y
    rw [hceq]
    simp only [bind_tc_ok]
    exact hseq
  · rw [hflag, hcv]

-- PROOF OBLIGATION: functional correctness of the windowed exponentiation ladder in
-- `field.verified.sqrt.sqrt`: the 16-entry table satisfies `table[i] = value^i`, the
-- fixed squaring/multiplication prefix and the 125-iteration 4-bit-window loop
-- (invariant: `res = value ^ (bits-consumed-so-far prefix of (p+1)/4)`, window flushes
-- multiplying by `table[bits]`) compute `res13 = value ^ ((p+1)/4)`. Since
-- `p ≡ 3 (mod 4)`, for a square input `(value^((p+1)/4))^2 = value` (Euler), the
-- conditional negation preserves the square, and the final `ct_eq` check succeeds.
-- ONLY this completeness direction depends on ladder correctness; the group-law
-- development uses none of it (`sqrt_ok` covers soundness of the flag).
/-- **`sqrt` completeness (SORRIED — windowed-ladder correctness):** on a square input
the returned validity flag is true. Together with the (proved) `sqrt_ok` this gives
`flag = true ↔ IsSquare (ψ a)`; the reverse direction `flag = true → IsSquare (ψ a)`
already follows from `sqrt_ok` (`ψ r ^ 2 = ψ a`). -/
theorem sqrt_complete (a : Uint4) (ha : a.toNat < p) (r : Uint4) (flag : Bool)
    (heq : field.HelioseleneField.Insts.FfField.sqrt a = .ok (r, flag))
    (hsq : IsSquare (ψ a)) : flag = true := sorry

end Selene

end HelioseleneSpec
