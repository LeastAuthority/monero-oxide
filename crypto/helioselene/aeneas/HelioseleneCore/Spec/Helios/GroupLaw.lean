/- THE GROUP LAW: the Aeneas-translated Helios point operations implement the
   mathlib elliptic-curve group.

   Helios sibling of `Spec/Selene/GroupLaw.lean` (the template — same section
   structure, same theorem names). This file connects the coordinate-level
   contracts of `Spec/Helios/Ops.lean` (RCB add-2015-rcb-3 complete addition,
   dbl-2007-bl-2 doubling with identity fix-up, negation, identity, generator,
   constant-time equality) to mathlib's `WeierstrassCurve.Affine.Point` group for
   the short-Weierstrass curve

     `W : y² = x³ - 3x + B` over `Fq = ZMod (2^255 - 19)`
     (`a₁ = a₂ = a₃ = 0`, `a₄ = -3`, `a₆ = B`).

   It is LIGHTER than the Selene file in exactly one respect: the Helios
   coordinate type `dalek_ff_group.field.FieldElement` IS `Fq` definitionally
   (TypesExternal.lean), so there is no limb layer, no `Reduced` invariant, and
   the abstraction map on coordinates is the definitional `asFq`; every
   `Reduced`-clause of the Selene development is simply gone.

   Layers:
   1. `W`, `W.IsElliptic` (discriminant nonzero, `Spec/Helios/Curve.lean`), and the
      mathlib group `AddCommGroup W.toAffine.Point`;
   2. the carrier `HPt` = projective representatives satisfying the homogeneous
      curve equation (and not `(0,0,0)`), with the abstraction
      `Θ : HPt → W.toAffine.Point` (`z = 0` ↦ `0`, else the affine point `(x/z, y/z)`);
   3. per-case algebraic certificates for the RCB/BL coordinate formulas
      (regenerated for the (q, B_helios) instance by `tools/gen_lean_helios.py`
      → `tools/lean_certs_helios.txt`; their integer cofactors coincide with the
      Selene certificates because the cofactor extraction is over ℤ with `B`
      symbolic — the two printed cert files differ only in the field-name
      spelling `Fq` vs `F` of the type ascriptions, so a literal `diff` shows
      10 differing lines), checked by
      `linear_combination`, assembled into `Θ`-homomorphism theorems for the
      translated `add`/`sub`/`neg`/`double`/`identity`/`generator`;
   4. correctness of the translated `ct_eq`/`eq` as deciders of `Θ`-equality;
   5. the quotient group `HClass = HPt / (Θ · = Θ ·)` whose `0`, `+`, `-` (unary and
      binary) are the descended translated Rust operations (`rfl` to the
      choice-extracted wrappers of section 5; the wrappers are tied to the
      generated functions by the propositional `*_ok` equations), its
      `AddCommGroup` instance (transported along the injective `Θbar`), and the
      headline

        `ΘAddEquiv : HClass ≃+ W.toAffine.Point`.

   See the summary comment at the end of the file for the theorem list, sorry
   status, and the axiom audit. -/
import HelioseleneCore.Spec.Helios.Ops
import Mathlib

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std Result
open helioselene
open WeierstrassCurve

namespace HelioseleneSpec

namespace Helios

noncomputable section

/-! ## 1. The curve `W` and its mathlib group

The coefficient field is `Fq = ZMod (2^255 - 19)` (abbrev in `Spec/Helios/Curve.lean`,
with the `Fact (Nat.Prime _)` instance `fact_q_prime'` in scope). -/

/-- The Helios short-Weierstrass curve over `Fq`:
`y² = x³ - 3x + B` (`a₁ = a₂ = a₃ = 0`, `a₄ = -3`, `a₆ = B`). -/
noncomputable def W : WeierstrassCurve Fq :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -3, a₆ := (Bcurve : Fq) }

instance : W.IsShortNF := ⟨rfl, rfl, rfl⟩

@[simp] theorem W_a1 : W.a₁ = 0 := rfl
@[simp] theorem W_a2 : W.a₂ = 0 := rfl
@[simp] theorem W_a3 : W.a₃ = 0 := rfl
@[simp] theorem W_a4 : W.a₄ = -3 := rfl
@[simp] theorem W_a6 : W.a₆ = (Bcurve : Fq) := rfl

/-- The discriminant of `W` is nonzero (kernel fact `delta_ne_zero`,
`Spec/Helios/Curve.lean`). -/
theorem W_delta_ne_zero : W.Δ ≠ 0 := by
  rw [Δ_of_isShortNF]
  show -16 * (4 * (-3 : Fq) ^ 3 + 27 * (Bcurve : Fq) ^ 2) ≠ 0
  exact delta_ne_zero

/-- **Helios is an elliptic curve.** -/
instance instIsElliptic : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr W_delta_ne_zero⟩

/-- The mathlib group of affine points (plus `0`) of `W`. -/
example : AddCommGroup W.toAffine.Point := inferInstance

/-- The affine curve equation of `W`, in the `y² = x³ - 3x + B` shape. -/
theorem equation_iff_helios (x y : Fq) :
    W.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - 3 * x + (Bcurve : Fq) := by
  rw [Affine.equation_iff]
  simp only [W_a1, W_a2, W_a3, W_a4, W_a6]
  constructor <;> intro h <;> linear_combination h

/-- Every affine point of `W` is nonsingular (`Δ ≠ 0`), so `Nonsingular` reduces to
the curve equation. -/
theorem nonsingular_iff_helios (x y : Fq) :
    W.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 - 3 * x + (Bcurve : Fq) := by
  rw [← Affine.equation_iff_nonsingular_of_Δ_ne_zero W_delta_ne_zero, equation_iff_helios]

/-- `negY` for Helios is plain negation (`a₁ = a₃ = 0`). -/
theorem negY_helios (x y : Fq) : W.toAffine.negY x y = -y := by
  rw [Affine.negY]; simp

/-- `addX` for Helios: `ℓ² - x₁ - x₂`. -/
theorem addX_helios (x1 x2 l : Fq) : W.toAffine.addX x1 x2 l = l ^ 2 - x1 - x2 := by
  rw [Affine.addX]
  simp only [W_a1, W_a2]
  ring

/-- `addY` for Helios: `ℓ(x₁ - x₃) - y₁` with `x₃ = ℓ² - x₁ - x₂`. -/
theorem addY_helios (x1 x2 y1 l : Fq) :
    W.toAffine.addY x1 x2 y1 l = l * (x1 - (l ^ 2 - x1 - x2)) - y1 := by
  rw [Affine.addY, Affine.negAddY, Affine.negY, Affine.addX]
  simp only [W_a1, W_a2, W_a3]
  ring

/-- In `Fq`, a nonzero element is not its own negative (`2 ≠ 0`). -/
theorem ne_neg_self {y : Fq} (hy : y ≠ 0) : y ≠ -y := by
  intro h
  apply hy
  have h2 : (2 : Fq) * y = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact absurd h' two_ne_zero
  · exact h'

/-- The tangent slope for Helios: `slope x x y y = (3x² - 3)/(2y)` when `y ≠ 0`. -/
theorem slope_tangent_helios (x y : Fq) (hy : y ≠ 0) :
    W.toAffine.slope x x y y = (3 * x ^ 2 - 3) / (2 * y) := by
  have hne : y ≠ W.toAffine.negY x y := by rw [negY_helios]; exact ne_neg_self hy
  rw [Affine.slope_of_Y_ne rfl hne, negY_helios]
  simp only [W_a1, W_a2, W_a4]
  ring

/-- The chord slope for Helios (mathlib's `slope_of_X_ne`, restated). -/
theorem slope_chord_helios (x1 x2 y1 y2 : Fq) (hx : x1 ≠ x2) :
    W.toAffine.slope x1 x2 y1 y2 = (y1 - y2) / (x1 - x2) :=
  Affine.slope_of_X_ne hx

/-- The generator's affine coordinates are a nonsingular point of `W`. -/
theorem gen_nonsingular : W.toAffine.Nonsingular 1 (gY : Fq) := by
  rw [nonsingular_iff_helios]
  linear_combination generator_on_curve_zmod

/-! ## 2. The carrier `HPt` and the abstraction `Θ`

Unlike the Selene `OnCurveP` there is NO `Reduced` clause: `asFq` is total on the
definitionally-`Fq` coordinate type, so a representative is just a coordinate triple
satisfying the homogeneous equation and different from `(0, 0, 0)`. -/

/-- A `HeliosPoint` is **on the curve** (as a projective representative) when it
satisfies the homogeneous curve equation `y²z = x³ - 3xz² + Bz³` and is not the
zero triple. -/
def OnCurveP (P : point.helios.HeliosPoint) : Prop :=
  (asFq P.y) ^ 2 * asFq P.z
      = (asFq P.x) ^ 3 - 3 * asFq P.x * (asFq P.z) ^ 2 + (Bcurve : Fq) * (asFq P.z) ^ 3
    ∧ ¬(asFq P.x = 0 ∧ asFq P.y = 0 ∧ asFq P.z = 0)

/-- The subtype of on-curve `HeliosPoint`s — the carrier of the verified group. -/
def HPt : Type := { P : point.helios.HeliosPoint // OnCurveP P }

/-- `z = 0` forces `x = 0` on the curve (`x³ = 0`). -/
theorem x_eq_zero_of_z_eq_zero {P : point.helios.HeliosPoint} (h : OnCurveP P)
    (hz : asFq P.z = 0) : asFq P.x = 0 := by
  have heq := h.1
  rw [hz] at heq
  have h3 : asFq P.x ^ 3 = 0 := by linear_combination -heq
  exact pow_eq_zero_iff (by norm_num) |>.mp h3

/-- At infinity (`z = 0`), the `y`-coordinate is nonzero. -/
theorem y_ne_zero_of_z_eq_zero {P : point.helios.HeliosPoint} (h : OnCurveP P)
    (hz : asFq P.z = 0) : asFq P.y ≠ 0 :=
  fun hy => h.2 ⟨x_eq_zero_of_z_eq_zero h hz, hy, hz⟩

/-- For `z ≠ 0`, the coordinate ratios satisfy the affine curve equation. -/
theorem affine_eq_of_onCurveP {P : point.helios.HeliosPoint} (h : OnCurveP P)
    (hz : asFq P.z ≠ 0) :
    (asFq P.y / asFq P.z) ^ 2
      = (asFq P.x / asFq P.z) ^ 3 - 3 * (asFq P.x / asFq P.z) + (Bcurve : Fq) := by
  have heq := h.1
  field_simp
  linear_combination heq

/-- **Every on-curve representative has `y ≠ 0`** (Helios has no 2-torsion, and its
points at infinity are `(0 : y : 0)`, `y ≠ 0`). -/
theorem y_ne_zero_of_onCurveP {P : point.helios.HeliosPoint} (h : OnCurveP P) :
    asFq P.y ≠ 0 := by
  by_cases hz : asFq P.z = 0
  · exact y_ne_zero_of_z_eq_zero h hz
  · exact fun hy =>
      no_two_torsion _ _ (affine_eq_of_onCurveP h hz) (by rw [hy, zero_div])

/-- `x = 0` forces `z = 0` on the curve (`B` is a non-residue): soundness of the
`is_identity` test. -/
theorem z_eq_zero_of_x_eq_zero {P : point.helios.HeliosPoint} (h : OnCurveP P)
    (hx : asFq P.x = 0) : asFq P.z = 0 := by
  by_contra hz
  have haff := affine_eq_of_onCurveP h hz
  rw [hx, zero_div] at haff
  exact no_affine_x_zero (asFq P.y / asFq P.z) (by linear_combination haff)

/-- For `z ≠ 0`, the coordinate ratios are a nonsingular affine point of `W`. -/
theorem theta_ns (P : HPt) (hz : asFq P.1.z ≠ 0) :
    W.toAffine.Nonsingular (asFq P.1.x / asFq P.1.z) (asFq P.1.y / asFq P.1.z) := by
  rw [nonsingular_iff_helios]
  exact affine_eq_of_onCurveP P.2 hz

/-- **The abstraction map** into the mathlib point group: representatives with
`z = 0` map to `0`, the rest to the affine point of their coordinate ratios. -/
noncomputable def Θ (P : HPt) : W.toAffine.Point :=
  if hz : asFq P.1.z = 0 then 0 else .some _ _ (theta_ns P hz)

theorem Θ_of_z_eq {P : HPt} (hz : asFq P.1.z = 0) : Θ P = 0 := by
  rw [Θ, dif_pos hz]

theorem Θ_of_z_ne {P : HPt} (hz : asFq P.1.z ≠ 0) :
    Θ P = .some _ _ (theta_ns P hz) := by
  rw [Θ, dif_neg hz]

/-! ### On-curve constructors and scale invariance -/

/-- On-curve criterion for a finite (`z ≠ 0`) representative. -/
theorem onCurveP_of_affine {R : point.helios.HeliosPoint}
    (hz : asFq R.z ≠ 0)
    (heq : (asFq R.y / asFq R.z) ^ 2
      = (asFq R.x / asFq R.z) ^ 3 - 3 * (asFq R.x / asFq R.z) + (Bcurve : Fq)) :
    OnCurveP R := by
  refine ⟨?_, fun h => hz h.2.2⟩
  field_simp at heq
  linear_combination heq

/-- On-curve criterion for an infinity representative. -/
theorem onCurveP_of_infinity {R : point.helios.HeliosPoint}
    (hx : asFq R.x = 0) (hy : asFq R.y ≠ 0) (hz : asFq R.z = 0) : OnCurveP R := by
  refine ⟨?_, fun h => hy h.2.1⟩
  rw [hx, hz]; ring

/-- A nonzero scaling of an on-curve point is on the curve. -/
theorem onCurveP_smul {R : point.helios.HeliosPoint} (Q : HPt) {c : Fq} (hc : c ≠ 0)
    (hx : asFq R.x = c * asFq Q.1.x) (hy : asFq R.y = c * asFq Q.1.y)
    (hz : asFq R.z = c * asFq Q.1.z) : OnCurveP R := by
  obtain ⟨hQeq, _⟩ := Q.2
  refine ⟨?_, ?_⟩
  · rw [hx, hy, hz]
    linear_combination c ^ 3 * hQeq
  · rintro ⟨_, hy0, _⟩
    rw [hy] at hy0
    rcases mul_eq_zero.mp hy0 with h | h
    · exact hc h
    · exact y_ne_zero_of_onCurveP Q.2 h

/-- `Θ` is scale-invariant: representatives with proportional coordinates map to
the same mathlib point. -/
theorem Θ_eq_of_smul {R Q : HPt} {c : Fq} (hc : c ≠ 0)
    (hx : asFq R.1.x = c * asFq Q.1.x) (hy : asFq R.1.y = c * asFq Q.1.y)
    (hz : asFq R.1.z = c * asFq Q.1.z) :
    Θ R = Θ Q := by
  by_cases hzQ : asFq Q.1.z = 0
  · rw [Θ_of_z_eq (by rw [hz, hzQ, mul_zero]), Θ_of_z_eq hzQ]
  · have hzR : asFq R.1.z ≠ 0 := by rw [hz]; exact mul_ne_zero hc hzQ
    rw [Θ_of_z_ne hzR, Θ_of_z_ne hzQ]
    simp only [Affine.Point.some.injEq]
    rw [hx, hy, hz, mul_div_mul_left _ _ hc, mul_div_mul_left _ _ hc]
    exact ⟨rfl, rfl⟩

/-! ## 3. Coordinate algebra

Scaling reductions to unit-`z` representatives, the special infinity inputs, and
the per-case algebraic certificates for the RCB/BL outputs. The
`linear_combination` coefficient polynomials were regenerated for the
(q, B_helios) instance by `tools/gen_lean_helios.py` (cofactor extraction of the
target polynomial over the ideal `(y₁² - f(x₁), y₂² - f(x₂))`, output
`tools/lean_certs_helios.txt`); since the extraction runs over ℤ with `B`
symbolic, they coincide with the Selene certificates. -/

/-- RCB addition is `(2,2)`-homogeneous: `x`-output on scaled-to-unit inputs. -/
theorem addCoords_unitize_x (X1 Y1 Z1 X2 Y2 Z2 : Fq) (h1 : Z1 ≠ 0) (h2 : Z2 ≠ 0) :
    (addCoords X1 Y1 Z1 X2 Y2 Z2).1
      = Z1 ^ 2 * Z2 ^ 2
          * (addCoords (X1 / Z1) (Y1 / Z1) 1 (X2 / Z2) (Y2 / Z2) 1).1 := by
  rw [addCoords_x, addCoords_x]
  field_simp

/-- RCB addition is `(2,2)`-homogeneous: `y`-output on scaled-to-unit inputs. -/
theorem addCoords_unitize_y (X1 Y1 Z1 X2 Y2 Z2 : Fq) (h1 : Z1 ≠ 0) (h2 : Z2 ≠ 0) :
    (addCoords X1 Y1 Z1 X2 Y2 Z2).2.1
      = Z1 ^ 2 * Z2 ^ 2
          * (addCoords (X1 / Z1) (Y1 / Z1) 1 (X2 / Z2) (Y2 / Z2) 1).2.1 := by
  rw [addCoords_y, addCoords_y]
  field_simp

/-- RCB addition is `(2,2)`-homogeneous: `z`-output on scaled-to-unit inputs. -/
theorem addCoords_unitize_z (X1 Y1 Z1 X2 Y2 Z2 : Fq) (h1 : Z1 ≠ 0) (h2 : Z2 ≠ 0) :
    (addCoords X1 Y1 Z1 X2 Y2 Z2).2.2
      = Z1 ^ 2 * Z2 ^ 2
          * (addCoords (X1 / Z1) (Y1 / Z1) 1 (X2 / Z2) (Y2 / Z2) 1).2.2 := by
  rw [addCoords_z, addCoords_z]
  field_simp

/-- RCB with left input at infinity `(0 : Y₁ : 0)` returns `Y₁²Y₂ · (right input)`. -/
theorem addCoords_inf_left_x (Y1 X2 Y2 Z2 : Fq) :
    (addCoords 0 Y1 0 X2 Y2 Z2).1 = Y1 ^ 2 * Y2 * X2 := by
  rw [addCoords_x]; ring

theorem addCoords_inf_left_y (Y1 X2 Y2 Z2 : Fq) :
    (addCoords 0 Y1 0 X2 Y2 Z2).2.1 = Y1 ^ 2 * Y2 * Y2 := by
  rw [addCoords_y]; ring

theorem addCoords_inf_left_z (Y1 X2 Y2 Z2 : Fq) :
    (addCoords 0 Y1 0 X2 Y2 Z2).2.2 = Y1 ^ 2 * Y2 * Z2 := by
  rw [addCoords_z]; ring

/-- RCB with right input at infinity `(0 : Y₂ : 0)` returns `Y₂²Y₁ · (left input)`. -/
theorem addCoords_inf_right_x (X1 Y1 Z1 Y2 : Fq) :
    (addCoords X1 Y1 Z1 0 Y2 0).1 = Y2 ^ 2 * Y1 * X1 := by
  rw [addCoords_x]; ring

theorem addCoords_inf_right_y (X1 Y1 Z1 Y2 : Fq) :
    (addCoords X1 Y1 Z1 0 Y2 0).2.1 = Y2 ^ 2 * Y1 * Y1 := by
  rw [addCoords_y]; ring

theorem addCoords_inf_right_z (X1 Y1 Z1 Y2 : Fq) :
    (addCoords X1 Y1 Z1 0 Y2 0).2.2 = Y2 ^ 2 * Y1 * Z1 := by
  rw [addCoords_z]; ring

/-! ### Chord-case certificates (unit `z`, `x₁ ≠ x₂`)

Below, `d = x₁ - x₂`, and (writing `u = y₁ + y₂`, `v = y₁ - y₂`)
`N₄ = u((2x₁+x₂)d² - u²) - y₁d³` is `d³ · y(P - Q)`,
`Nx = v² - (x₁+x₂)d²` is `d² · x(P + Q)`, and
`Ny = v((2x₁+x₂)d² - v²) - y₁d³` is `d³ · y(P + Q)`. -/

/-- CERT1: if the RCB `Z₃` output vanishes (unit `z`), so does `N₄`. -/
theorem unit_N4_of_Z3_eq_zero {x1 y1 x2 y2 : Fq}
    (hE1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + (Bcurve : Fq))
    (hE2 : y2 ^ 2 = x2 ^ 3 - 3 * x2 + (Bcurve : Fq))
    (hZ : (addCoords x1 y1 1 x2 y2 1).2.2 = 0) :
    (y1 + y2) * ((2 * x1 + x2) * (x1 - x2) ^ 2 - (y1 + y2) ^ 2)
      - y1 * (x1 - x2) ^ 3 = 0 := by
  rw [addCoords_z] at hZ
  linear_combination (-1) * hZ + (((-2)) * y2 + (-1) * y1) * hE1
    + ((-1) * y2 + ((-2)) * y1) * hE2

/-- CERT2: `N₄ = 0` makes `Nx' = R₂/d²` (with `R₂ = (y₁+y₂)² - (x₁+x₂)d²`) a root of
the curve cubic, in homogenized form. -/
theorem unit_cubic_of_N4_eq_zero {x1 y1 x2 y2 : Fq}
    (hE1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + (Bcurve : Fq))
    (hE2 : y2 ^ 2 = x2 ^ 3 - 3 * x2 + (Bcurve : Fq))
    (hN4 : (y1 + y2) * ((2 * x1 + x2) * (x1 - x2) ^ 2 - (y1 + y2) ^ 2)
      - y1 * (x1 - x2) ^ 3 = 0) :
    ((y1 + y2) ^ 2 - (x1 + x2) * (x1 - x2) ^ 2) ^ 3
      - 3 * ((y1 + y2) ^ 2 - (x1 + x2) * (x1 - x2) ^ 2) * (x1 - x2) ^ 4
      + (Bcurve : Fq) * (x1 - x2) ^ 6 = 0 := by
  linear_combination (x2 ^ 3 * y2 + (2) * y1 * x2 ^ 3 + ((-3)) * x1 * y1 * x2 ^ 2
      + ((-3)) * x1 ^ 2 * x2 * y2 + (2) * x1 ^ 3 * y2 + x1 ^ 3 * y1 + (-1) * y2 ^ 3
      + ((-3)) * y1 * y2 ^ 2 + ((-3)) * y1 ^ 2 * y2 + (-1) * y1 ^ 3) * hN4
    + ((-1) * x2 ^ 6 + (6) * x1 * x2 ^ 5 + ((-12)) * x1 ^ 2 * x2 ^ 4
      + (9) * x1 ^ 3 * x2 ^ 3 + ((-3)) * x1 ^ 5 * x2 + x1 ^ 6 + (2) * y1 * x2 ^ 3 * y2
      + y1 ^ 2 * x2 ^ 3 + ((-6)) * x1 * y1 * x2 ^ 2 * y2 + ((-3)) * x1 * y1 ^ 2 * x2 ^ 2
      + (6) * x1 ^ 2 * y1 * x2 * y2 + (3) * x1 ^ 2 * y1 ^ 2 * x2
      + ((-2)) * x1 ^ 3 * y1 * y2 + (-1) * x1 ^ 3 * y1 ^ 2 + x2 ^ 3 * (Bcurve : Fq)
      + ((-3)) * x2 ^ 4 + ((-3)) * x1 * x2 ^ 2 * (Bcurve : Fq) + (9) * x1 * x2 ^ 3
      + (3) * x1 ^ 2 * x2 * (Bcurve : Fq) + ((-9)) * x1 ^ 2 * x2 ^ 2
      + (-1) * x1 ^ 3 * (Bcurve : Fq) + (3) * x1 ^ 3 * x2) * hE1
    + (x2 ^ 6 + ((-3)) * x1 * x2 ^ 5 + (9) * x1 ^ 3 * x2 ^ 3 + ((-12)) * x1 ^ 4 * x2 ^ 2
      + (6) * x1 ^ 5 * x2 + (-1) * x1 ^ 6 + (-1) * x2 ^ 3 * y2 ^ 2
      + ((-2)) * y1 * x2 ^ 3 * y2 + (3) * x1 * x2 ^ 2 * y2 ^ 2
      + (6) * x1 * y1 * x2 ^ 2 * y2 + ((-3)) * x1 ^ 2 * x2 * y2 ^ 2
      + ((-6)) * x1 ^ 2 * y1 * x2 * y2 + x1 ^ 3 * y2 ^ 2 + (2) * x1 ^ 3 * y1 * y2
      + (-1) * x2 ^ 3 * (Bcurve : Fq) + (3) * x1 * x2 ^ 2 * (Bcurve : Fq)
      + (3) * x1 * x2 ^ 3 + ((-3)) * x1 ^ 2 * x2 * (Bcurve : Fq)
      + ((-9)) * x1 ^ 2 * x2 ^ 2 + x1 ^ 3 * (Bcurve : Fq) + (9) * x1 ^ 3 * x2
      + ((-3)) * x1 ^ 4) * hE2

/-- **RCB completeness in the chord case**: for on-curve inputs with `x₁ ≠ x₂`,
the `Z₃` output is nonzero (else `N₄ = 0` would produce a rational 2-torsion
`x`-coordinate, contradicting `cubic_no_root`). -/
theorem unit_Z3_ne_zero {x1 y1 x2 y2 : Fq}
    (hE1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + (Bcurve : Fq))
    (hE2 : y2 ^ 2 = x2 ^ 3 - 3 * x2 + (Bcurve : Fq))
    (hx : x1 ≠ x2) :
    (addCoords x1 y1 1 x2 y2 1).2.2 ≠ 0 := by
  intro hZ
  have hd : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
  have hcub := unit_cubic_of_N4_eq_zero hE1 hE2 (unit_N4_of_Z3_eq_zero hE1 hE2 hZ)
  apply cubic_no_root
    (((y1 + y2) ^ 2 - (x1 + x2) * (x1 - x2) ^ 2) / (x1 - x2) ^ 2)
  field_simp
  linear_combination hcub

/-- CERT3: cross-multiplied `x`-coordinate identity `X₃d² = Nx·Z₃`. -/
theorem unit_X3_cross {x1 y1 x2 y2 : Fq}
    (hE1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + (Bcurve : Fq))
    (hE2 : y2 ^ 2 = x2 ^ 3 - 3 * x2 + (Bcurve : Fq)) :
    (addCoords x1 y1 1 x2 y2 1).1 * (x1 - x2) ^ 2
      = ((y1 - y2) ^ 2 - (x1 + x2) * (x1 - x2) ^ 2)
          * (addCoords x1 y1 1 x2 y2 1).2.2 := by
  rw [addCoords_x, addCoords_z]
  linear_combination ((2) * x2 ^ 3 * y2 + (3) * x1 * x2 ^ 2 * y2
      + ((-3)) * x1 * y1 * x2 ^ 2 + ((-3)) * x1 ^ 2 * x2 * y2 + y2 ^ 3 + y1 * y2 ^ 2
      + (-1) * y1 ^ 2 * y2 + (2) * y2 * (Bcurve : Fq) + ((-9)) * x2 * y2
      + ((-3)) * y1 * (Bcurve : Fq) + (6) * y1 * x2 + (3) * x1 * y2 + (3) * x1 * y1) * hE1
    + (((-3)) * x1 * y1 * x2 ^ 2 + ((-3)) * x1 ^ 2 * x2 * y2 + (3) * x1 ^ 2 * y1 * x2
      + x1 ^ 3 * y2 + (3) * x1 ^ 3 * y1 + (-1) * y1 * y2 ^ 2
      + ((-2)) * y2 * (Bcurve : Fq) + (3) * x2 * y2 + (3) * y1 * (Bcurve : Fq)
      + (3) * y1 * x2 + (3) * x1 * y2 + ((-12)) * x1 * y1) * hE2

/-- CERT4: cross-multiplied `y`-coordinate identity `Y₃d³ = Ny·Z₃`. -/
theorem unit_Y3_cross {x1 y1 x2 y2 : Fq}
    (hE1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + (Bcurve : Fq))
    (hE2 : y2 ^ 2 = x2 ^ 3 - 3 * x2 + (Bcurve : Fq)) :
    (addCoords x1 y1 1 x2 y2 1).2.1 * (x1 - x2) ^ 3
      = ((y1 - y2) * ((2 * x1 + x2) * (x1 - x2) ^ 2 - (y1 - y2) ^ 2)
          - y1 * (x1 - x2) ^ 3)
          * (addCoords x1 y1 1 x2 y2 1).2.2 := by
  rw [addCoords_y, addCoords_z]
  linear_combination (((-6)) * x1 * x2 ^ 5 + (9) * x1 ^ 2 * x2 ^ 4
      + ((-2)) * x2 ^ 3 * y2 ^ 2 + ((-2)) * y1 * x2 ^ 3 * y2
      + (15) * x1 * x2 ^ 2 * y2 ^ 2 + ((-6)) * x1 * y1 * x2 ^ 2 * y2
      + (3) * x1 * y1 ^ 2 * x2 ^ 2 + ((-15)) * x1 ^ 2 * x2 * y2 ^ 2
      + (3) * x1 ^ 2 * y1 * x2 * y2 + (2) * y2 ^ 4 + ((-6)) * x2 ^ 3 * (Bcurve : Fq)
      + (12) * x2 ^ 4 + ((-2)) * y1 ^ 2 * y2 ^ 2 + y1 ^ 3 * y2
      + (12) * x1 * x2 ^ 2 * (Bcurve : Fq) + ((-12)) * x1 * x2 ^ 3
      + ((-18)) * x1 ^ 2 * x2 ^ 2 + ((-2)) * y2 ^ 2 * (Bcurve : Fq)
      + ((-9)) * x2 * y2 ^ 2 + ((-5)) * y1 * y2 * (Bcurve : Fq) + (15) * y1 * x2 * y2
      + (3) * y1 ^ 2 * (Bcurve : Fq) + ((-6)) * y1 ^ 2 * x2 + (15) * x1 * y2 ^ 2
      + ((-3)) * x1 * y1 ^ 2 + (3) * (Bcurve : Fq) ^ 2 + ((-6)) * x2 * (Bcurve : Fq)
      + ((-12)) * x1 * (Bcurve : Fq) + (18) * x1 * x2 + (9) * x1 ^ 2) * hE1
    + ((6) * x1 ^ 4 * x2 ^ 2 + ((-9)) * x1 ^ 5 * x2 + ((-3)) * x1 * y1 * x2 ^ 2 * y2
      + ((-3)) * x1 ^ 2 * x2 * y2 ^ 2 + (6) * x1 ^ 2 * y1 * x2 * y2
      + (2) * x1 ^ 3 * y2 ^ 2 + (2) * x1 ^ 3 * y1 * y2 + (-1) * y1 * y2 ^ 3
      + (15) * x1 * x2 ^ 2 * (Bcurve : Fq) + ((-27)) * x1 ^ 2 * x2 * (Bcurve : Fq)
      + ((-27)) * x1 ^ 2 * x2 ^ 2 + (6) * x1 ^ 3 * (Bcurve : Fq) + (42) * x1 ^ 3 * x2
      + (3) * x1 ^ 4 + (-1) * y2 ^ 2 * (Bcurve : Fq) + (3) * x2 * y2 ^ 2
      + (5) * y1 * y2 * (Bcurve : Fq) + ((-15)) * x1 * y1 * y2 + ((-3)) * (Bcurve : Fq) ^ 2
      + ((-3)) * x2 * (Bcurve : Fq) + ((-9)) * x2 ^ 2 + (21) * x1 * (Bcurve : Fq)
      + (27) * x1 * x2 + ((-45)) * x1 ^ 2) * hE2

/-- Pure field identity: `Nx/d²` is the chord `addX`. -/
theorem chord_x_identity {x1 y1 x2 y2 : Fq} (hd : x1 - x2 ≠ 0) :
    ((y1 - y2) ^ 2 - (x1 + x2) * (x1 - x2) ^ 2) / (x1 - x2) ^ 2
      = ((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2 := by
  field_simp
  ring

/-- Pure field identity: `Ny/d³` is the chord `addY`. -/
theorem chord_y_identity {x1 y1 x2 y2 : Fq} (hd : x1 - x2 ≠ 0) :
    ((y1 - y2) * ((2 * x1 + x2) * (x1 - x2) ^ 2 - (y1 - y2) ^ 2)
        - y1 * (x1 - x2) ^ 3) / (x1 - x2) ^ 3
      = ((y1 - y2) / (x1 - x2))
          * (x1 - (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2)) - y1 := by
  field_simp
  ring

/-! ### Anti-diagonal certificates (unit `z`, `x₂ = x₁`, `y₂ = -y₁`)

Writing `st = 3x₁² - 3`, `D = 2y₁`, `M = st² - 2x₁D²` (`= D²·x(2P)`) and
`Ndbl = st(x₁D² - M) - y₁D³` (`= D³·y(2P)`). -/

/-- The RCB `X₃` output on `(x, y) + (x, -y)` vanishes identically. -/
theorem unit_anti_X3 (x1 y1 : Fq) : (addCoords x1 y1 1 x1 (-y1) 1).1 = 0 := by
  rw [addCoords_x]; ring

/-- The RCB `Z₃` output on `(x, y) + (x, -y)` vanishes identically. -/
theorem unit_anti_Z3 (x1 y1 : Fq) : (addCoords x1 y1 1 x1 (-y1) 1).2.2 = 0 := by
  rw [addCoords_z]; ring

/-- CERT5: the RCB `Y₃` output on `(x, y) + (x, -y)` is `Ndbl`. -/
theorem unit_anti_Y3 {x1 y1 : Fq}
    (hE1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + (Bcurve : Fq)) :
    (addCoords x1 y1 1 x1 (-y1) 1).2.1
      = (3 * x1 ^ 2 - 3)
          * (x1 * (2 * y1) ^ 2 - ((3 * x1 ^ 2 - 3) ^ 2 - 2 * x1 * (2 * y1) ^ 2))
        - y1 * (2 * y1) ^ 3 := by
  rw [addCoords_y]
  linear_combination (((-27)) * x1 ^ 3 + (9) * y1 ^ 2 + (9) * (Bcurve : Fq)
    + (9) * x1) * hE1

/-- CERT6: `Ndbl = 0` makes `M/D²` a root of the curve cubic, in homogenized form. -/
theorem unit_cubic_of_Ndbl_eq_zero {x1 y1 : Fq}
    (hE1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + (Bcurve : Fq))
    (hN : (3 * x1 ^ 2 - 3)
          * (x1 * (2 * y1) ^ 2 - ((3 * x1 ^ 2 - 3) ^ 2 - 2 * x1 * (2 * y1) ^ 2))
        - y1 * (2 * y1) ^ 3 = 0) :
    ((3 * x1 ^ 2 - 3) ^ 2 - 2 * x1 * (2 * y1) ^ 2) ^ 3
      - 3 * ((3 * x1 ^ 2 - 3) ^ 2 - 2 * x1 * (2 * y1) ^ 2) * (2 * y1) ^ 4
      + (Bcurve : Fq) * (2 * y1) ^ 6 = 0 := by
  linear_combination (((-27)) * x1 ^ 6 + (36) * x1 ^ 3 * y1 ^ 2 + ((-8)) * y1 ^ 4
      + (81) * x1 ^ 4 + ((-36)) * x1 * y1 ^ 2 + ((-81)) * x1 ^ 2 + (27 : Fq)) * hN
    + (((-64)) * y1 ^ 6) * hE1

/-- No homogenized rational root of the curve cubic: if
`M³ - 3MD⁴ + BD⁶ = 0` with `D ≠ 0`, then `M/D²` would be a root of
`X³ - 3X + B` — impossible (`cubic_no_root`). -/
theorem cubic_no_root_hom (M D : Fq) (hD : D ≠ 0)
    (h : M ^ 3 - 3 * M * D ^ 4 + (Bcurve : Fq) * D ^ 6 = 0) : False := by
  apply cubic_no_root (M / D ^ 2)
  field_simp
  linear_combination h

/-- **RCB completeness in the anti-diagonal case**: the `Y₃` output on
`(x, y) + (x, -y)` is nonzero for on-curve `y ≠ 0`. -/
theorem unit_anti_Y3_ne_zero {x1 y1 : Fq}
    (hE1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + (Bcurve : Fq)) (hy : y1 ≠ 0) :
    (addCoords x1 y1 1 x1 (-y1) 1).2.1 ≠ 0 := by
  rw [unit_anti_Y3 hE1]
  intro hN
  exact cubic_no_root_hom _ _ (mul_ne_zero two_ne_zero hy)
    (unit_cubic_of_Ndbl_eq_zero hE1 hN)

/-! ### Diagonal certificates (unit `z`, `x₂ = x₁`, `y₂ = y₁`) and the BL doubling -/

/-- CERT7X: the RCB `X₃` output on `(x, y) + (x, y)` is `M·D`. -/
theorem unit_diag_X3 {x1 y1 : Fq}
    (hE1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + (Bcurve : Fq)) :
    (addCoords x1 y1 1 x1 y1 1).1
      = ((3 * x1 ^ 2 - 3) ^ 2 - 2 * x1 * (2 * y1) ^ 2) * (2 * y1) := by
  rw [addCoords_x]
  linear_combination ((18) * x1 * y1) * hE1

/-- CERT7Y: the RCB `Y₃` output on `(x, y) + (x, y)` is `Ndbl`. -/
theorem unit_diag_Y3 {x1 y1 : Fq}
    (hE1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + (Bcurve : Fq)) :
    (addCoords x1 y1 1 x1 y1 1).2.1
      = (3 * x1 ^ 2 - 3)
          * (x1 * (2 * y1) ^ 2 - ((3 * x1 ^ 2 - 3) ^ 2 - 2 * x1 * (2 * y1) ^ 2))
        - y1 * (2 * y1) ^ 3 := by
  rw [addCoords_y]
  linear_combination (((-27)) * x1 ^ 3 + (9) * y1 ^ 2 + (9) * (Bcurve : Fq)
    + (9) * x1) * hE1

/-- CERT7Z: the RCB `Z₃` output on `(x, y) + (x, y)` is `D³`. -/
theorem unit_diag_Z3 {x1 y1 : Fq}
    (hE1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + (Bcurve : Fq)) :
    (addCoords x1 y1 1 x1 y1 1).2.2 = (2 * y1) ^ 3 := by
  rw [addCoords_z]
  linear_combination (((-6)) * y1) * hE1

/-- The BL doubling `x`-output at unit `z` is `M·D` (pure ring identity). -/
theorem dbl_unit_x (x1 y1 : Fq) :
    (dblCoords x1 y1 1).1
      = ((3 * x1 ^ 2 - 3) ^ 2 - 2 * x1 * (2 * y1) ^ 2) * (2 * y1) := by
  rw [dblCoords_x]; ring

/-- The BL doubling `y`-output at unit `z` is `Ndbl` (pure ring identity). -/
theorem dbl_unit_y (x1 y1 : Fq) :
    (dblCoords x1 y1 1).2.1
      = (3 * x1 ^ 2 - 3)
          * (x1 * (2 * y1) ^ 2 - ((3 * x1 ^ 2 - 3) ^ 2 - 2 * x1 * (2 * y1) ^ 2))
        - y1 * (2 * y1) ^ 3 := by
  rw [dblCoords_y]; ring

/-- The BL doubling `z`-output at unit `z` is `D³` (pure ring identity). -/
theorem dbl_unit_z (x1 y1 : Fq) :
    (dblCoords x1 y1 1).2.2 = (2 * y1) ^ 3 := by
  rw [dblCoords_z]; ring

/-- BL doubling is degree-6 homogeneous: `x`-output on scaled-to-unit input. -/
theorem dblCoords_unitize_x (X Y Z : Fq) (hz : Z ≠ 0) :
    (dblCoords X Y Z).1 = Z ^ 6 * (dblCoords (X / Z) (Y / Z) 1).1 := by
  rw [dblCoords_x, dblCoords_x]
  field_simp

/-- BL doubling is degree-6 homogeneous: `y`-output on scaled-to-unit input. -/
theorem dblCoords_unitize_y (X Y Z : Fq) (hz : Z ≠ 0) :
    (dblCoords X Y Z).2.1 = Z ^ 6 * (dblCoords (X / Z) (Y / Z) 1).2.1 := by
  rw [dblCoords_y, dblCoords_y]
  field_simp

/-- BL doubling is degree-6 homogeneous: `z`-output on scaled-to-unit input. -/
theorem dblCoords_unitize_z (X Y Z : Fq) (hz : Z ≠ 0) :
    (dblCoords X Y Z).2.2 = Z ^ 6 * (dblCoords (X / Z) (Y / Z) 1).2.2 := by
  rw [dblCoords_z, dblCoords_z]
  field_simp

theorem four_ne_zero : (4 : Fq) ≠ 0 := by
  have h4 : (4 : Fq) = 2 * 2 := by norm_num
  rw [h4]
  exact mul_ne_zero two_ne_zero two_ne_zero

theorem eight_ne_zero : (8 : Fq) ≠ 0 := by
  have h8 : (8 : Fq) = 2 * (2 * 2) := by norm_num
  rw [h8]
  exact mul_ne_zero two_ne_zero (mul_ne_zero two_ne_zero two_ne_zero)

/-- Pure field identity: `(M·D)/D³` is the tangent `addX`. -/
theorem tangent_x_identity {x1 y1 : Fq} (hy : y1 ≠ 0) :
    (((3 * x1 ^ 2 - 3) ^ 2 - 2 * x1 * (2 * y1) ^ 2) * (2 * y1)) / (2 * y1) ^ 3
      = ((3 * x1 ^ 2 - 3) / (2 * y1)) ^ 2 - x1 - x1 := by
  field_simp [two_ne_zero, four_ne_zero, eight_ne_zero]
  ring

/-- Pure field identity: `Ndbl/D³` is the tangent `addY`. -/
theorem tangent_y_identity {x1 y1 : Fq} (hy : y1 ≠ 0) :
    ((3 * x1 ^ 2 - 3)
          * (x1 * (2 * y1) ^ 2 - ((3 * x1 ^ 2 - 3) ^ 2 - 2 * x1 * (2 * y1) ^ 2))
        - y1 * (2 * y1) ^ 3) / (2 * y1) ^ 3
      = ((3 * x1 ^ 2 - 3) / (2 * y1))
          * (x1 - (((3 * x1 ^ 2 - 3) / (2 * y1)) ^ 2 - x1 - x1)) - y1 := by
  field_simp [two_ne_zero, four_ne_zero, eight_ne_zero]
  ring

/-- On-curve `y`-dichotomy at equal `x`: `y₁ = y₂` or `y₁ = -y₂`. -/
theorem y_dichotomy {x1 y1 x2 y2 : Fq}
    (hE1 : y1 ^ 2 = x1 ^ 3 - 3 * x1 + (Bcurve : Fq))
    (hE2 : y2 ^ 2 = x2 ^ 3 - 3 * x2 + (Bcurve : Fq))
    (hx : x1 = x2) : y1 = y2 ∨ y1 = -y2 := by
  have h : (y1 - y2) * (y1 + y2) = 0 := by
    linear_combination hE1 - hE2 + (x1 ^ 2 + x1 * x2 + x2 ^ 2 - 3) * hx
  rcases mul_eq_zero.mp h with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (eq_neg_of_add_eq_zero_left h')

/-! ## 4. Per-case `Θ`-correctness of the RCB addition output -/

/-- Chord case (`z₁, z₂ ≠ 0`, distinct affine `x`): the RCB output is on-curve and
`Θ`-represents the mathlib sum. -/
theorem add_theta_chord (P Q : HPt) (R : point.helios.HeliosPoint)
    (hz1 : asFq P.1.z ≠ 0) (hz2 : asFq Q.1.z ≠ 0)
    (hRx : asFq R.x = asFq P.1.z ^ 2 * asFq Q.1.z ^ 2
      * (addCoords (asFq P.1.x / asFq P.1.z) (asFq P.1.y / asFq P.1.z) 1
          (asFq Q.1.x / asFq Q.1.z) (asFq Q.1.y / asFq Q.1.z) 1).1)
    (hRy : asFq R.y = asFq P.1.z ^ 2 * asFq Q.1.z ^ 2
      * (addCoords (asFq P.1.x / asFq P.1.z) (asFq P.1.y / asFq P.1.z) 1
          (asFq Q.1.x / asFq Q.1.z) (asFq Q.1.y / asFq Q.1.z) 1).2.1)
    (hRz : asFq R.z = asFq P.1.z ^ 2 * asFq Q.1.z ^ 2
      * (addCoords (asFq P.1.x / asFq P.1.z) (asFq P.1.y / asFq P.1.z) 1
          (asFq Q.1.x / asFq Q.1.z) (asFq Q.1.y / asFq Q.1.z) 1).2.2)
    (hxx : asFq P.1.x / asFq P.1.z ≠ asFq Q.1.x / asFq Q.1.z) :
    ∃ hOn : OnCurveP R, Θ ⟨R, hOn⟩ = Θ P + Θ Q := by
  set x1 := asFq P.1.x / asFq P.1.z with hx1
  set y1 := asFq P.1.y / asFq P.1.z with hy1
  set x2 := asFq Q.1.x / asFq Q.1.z with hx2
  set y2 := asFq Q.1.y / asFq Q.1.z with hy2
  have hE1 := affine_eq_of_onCurveP P.2 hz1
  have hE2 := affine_eq_of_onCurveP Q.2 hz2
  have hd : x1 - x2 ≠ 0 := sub_ne_zero.mpr hxx
  have hZ3 := unit_Z3_ne_zero hE1 hE2 hxx
  have hc : asFq P.1.z ^ 2 * asFq Q.1.z ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hz1) (pow_ne_zero 2 hz2)
  have hzR : asFq R.z ≠ 0 := by rw [hRz]; exact mul_ne_zero hc hZ3
  have hXm : asFq R.x / asFq R.z
      = W.toAffine.addX x1 x2 (W.toAffine.slope x1 x2 y1 y2) := by
    rw [hRx, hRz, mul_div_mul_left _ _ hc, addX_helios,
      slope_chord_helios _ _ _ _ hxx]
    have h1 : (addCoords x1 y1 1 x2 y2 1).1 / (addCoords x1 y1 1 x2 y2 1).2.2
        = ((y1 - y2) ^ 2 - (x1 + x2) * (x1 - x2) ^ 2) / (x1 - x2) ^ 2 := by
      rw [div_eq_div_iff hZ3 (pow_ne_zero 2 hd)]
      exact unit_X3_cross hE1 hE2
    rw [h1]
    exact chord_x_identity hd
  have hYm : asFq R.y / asFq R.z
      = W.toAffine.addY x1 x2 y1 (W.toAffine.slope x1 x2 y1 y2) := by
    rw [hRy, hRz, mul_div_mul_left _ _ hc, addY_helios,
      slope_chord_helios _ _ _ _ hxx]
    have h1 : (addCoords x1 y1 1 x2 y2 1).2.1 / (addCoords x1 y1 1 x2 y2 1).2.2
        = ((y1 - y2) * ((2 * x1 + x2) * (x1 - x2) ^ 2 - (y1 - y2) ^ 2)
            - y1 * (x1 - x2) ^ 3) / (x1 - x2) ^ 3 := by
      rw [div_eq_div_iff hZ3 (pow_ne_zero 3 hd)]
      exact unit_Y3_cross hE1 hE2
    rw [h1]
    exact chord_y_identity hd
  have hNSR : W.toAffine.Nonsingular (asFq R.x / asFq R.z) (asFq R.y / asFq R.z) := by
    rw [hXm, hYm]
    exact Affine.nonsingular_add (theta_ns P hz1) (theta_ns Q hz2) fun h => hxx h.1
  have hOn : OnCurveP R :=
    onCurveP_of_affine hzR ((nonsingular_iff_helios _ _).mp hNSR)
  refine ⟨hOn, ?_⟩
  rw [Θ_of_z_ne (P := ⟨R, hOn⟩) hzR, Θ_of_z_ne hz1, Θ_of_z_ne hz2,
    Affine.Point.add_of_X_ne hxx]
  simp only [Affine.Point.some.injEq]
  exact ⟨hXm, hYm⟩

/-- Tangent case (`z₁, z₂ ≠ 0`, equal affine points): the RCB output is on-curve
and `Θ`-represents the mathlib sum (which is the doubling). -/
theorem add_theta_tangent (P Q : HPt) (R : point.helios.HeliosPoint)
    (hz1 : asFq P.1.z ≠ 0) (hz2 : asFq Q.1.z ≠ 0)
    (hRx : asFq R.x = asFq P.1.z ^ 2 * asFq Q.1.z ^ 2
      * (addCoords (asFq P.1.x / asFq P.1.z) (asFq P.1.y / asFq P.1.z) 1
          (asFq Q.1.x / asFq Q.1.z) (asFq Q.1.y / asFq Q.1.z) 1).1)
    (hRy : asFq R.y = asFq P.1.z ^ 2 * asFq Q.1.z ^ 2
      * (addCoords (asFq P.1.x / asFq P.1.z) (asFq P.1.y / asFq P.1.z) 1
          (asFq Q.1.x / asFq Q.1.z) (asFq Q.1.y / asFq Q.1.z) 1).2.1)
    (hRz : asFq R.z = asFq P.1.z ^ 2 * asFq Q.1.z ^ 2
      * (addCoords (asFq P.1.x / asFq P.1.z) (asFq P.1.y / asFq P.1.z) 1
          (asFq Q.1.x / asFq Q.1.z) (asFq Q.1.y / asFq Q.1.z) 1).2.2)
    (hxx : asFq P.1.x / asFq P.1.z = asFq Q.1.x / asFq Q.1.z)
    (hyy : asFq P.1.y / asFq P.1.z = asFq Q.1.y / asFq Q.1.z) :
    ∃ hOn : OnCurveP R, Θ ⟨R, hOn⟩ = Θ P + Θ Q := by
  set x1 := asFq P.1.x / asFq P.1.z with hx1
  set y1 := asFq P.1.y / asFq P.1.z with hy1
  set x2 := asFq Q.1.x / asFq Q.1.z with hx2
  set y2 := asFq Q.1.y / asFq Q.1.z with hy2
  have hE1 := affine_eq_of_onCurveP P.2 hz1
  have hy1ne : y1 ≠ 0 := div_ne_zero (y_ne_zero_of_onCurveP P.2) hz1
  have hD3 : (2 * y1) ^ 3 ≠ 0 := pow_ne_zero 3 (mul_ne_zero two_ne_zero hy1ne)
  rw [← hxx, ← hyy] at hRx hRy hRz
  rw [unit_diag_X3 hE1] at hRx
  rw [unit_diag_Y3 hE1] at hRy
  rw [unit_diag_Z3 hE1] at hRz
  have hc : asFq P.1.z ^ 2 * asFq Q.1.z ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hz1) (pow_ne_zero 2 hz2)
  have hzR : asFq R.z ≠ 0 := by rw [hRz]; exact mul_ne_zero hc hD3
  have hne : y1 ≠ W.toAffine.negY x2 y2 := by
    rw [negY_helios, ← hyy]
    exact ne_neg_self hy1ne
  have hXm : asFq R.x / asFq R.z
      = W.toAffine.addX x1 x2 (W.toAffine.slope x1 x2 y1 y2) := by
    rw [hRx, hRz, mul_div_mul_left _ _ hc, addX_helios, ← hxx, ← hyy,
      slope_tangent_helios _ _ hy1ne]
    exact tangent_x_identity hy1ne
  have hYm : asFq R.y / asFq R.z
      = W.toAffine.addY x1 x2 y1 (W.toAffine.slope x1 x2 y1 y2) := by
    rw [hRy, hRz, mul_div_mul_left _ _ hc, addY_helios, ← hxx, ← hyy,
      slope_tangent_helios _ _ hy1ne]
    exact tangent_y_identity hy1ne
  have hNSR : W.toAffine.Nonsingular (asFq R.x / asFq R.z) (asFq R.y / asFq R.z) := by
    rw [hXm, hYm]
    exact Affine.nonsingular_add (theta_ns P hz1) (theta_ns Q hz2) fun h => hne h.2
  have hOn : OnCurveP R :=
    onCurveP_of_affine hzR ((nonsingular_iff_helios _ _).mp hNSR)
  refine ⟨hOn, ?_⟩
  rw [Θ_of_z_ne (P := ⟨R, hOn⟩) hzR, Θ_of_z_ne hz1, Θ_of_z_ne hz2,
    Affine.Point.add_of_Y_ne hne]
  simp only [Affine.Point.some.injEq]
  exact ⟨hXm, hYm⟩

/-- Vertical case (`z₁, z₂ ≠ 0`, equal affine `x`, opposite `y`): the RCB output is
an identity-class representative `(0 : Y₃ : 0)`, `Y₃ ≠ 0`, and the mathlib sum
is `0`. -/
theorem add_theta_vertical (P Q : HPt) (R : point.helios.HeliosPoint)
    (hz1 : asFq P.1.z ≠ 0) (hz2 : asFq Q.1.z ≠ 0)
    (hRx : asFq R.x = asFq P.1.z ^ 2 * asFq Q.1.z ^ 2
      * (addCoords (asFq P.1.x / asFq P.1.z) (asFq P.1.y / asFq P.1.z) 1
          (asFq Q.1.x / asFq Q.1.z) (asFq Q.1.y / asFq Q.1.z) 1).1)
    (hRy : asFq R.y = asFq P.1.z ^ 2 * asFq Q.1.z ^ 2
      * (addCoords (asFq P.1.x / asFq P.1.z) (asFq P.1.y / asFq P.1.z) 1
          (asFq Q.1.x / asFq Q.1.z) (asFq Q.1.y / asFq Q.1.z) 1).2.1)
    (hRz : asFq R.z = asFq P.1.z ^ 2 * asFq Q.1.z ^ 2
      * (addCoords (asFq P.1.x / asFq P.1.z) (asFq P.1.y / asFq P.1.z) 1
          (asFq Q.1.x / asFq Q.1.z) (asFq Q.1.y / asFq Q.1.z) 1).2.2)
    (hxx : asFq P.1.x / asFq P.1.z = asFq Q.1.x / asFq Q.1.z)
    (hyy : asFq P.1.y / asFq P.1.z = -(asFq Q.1.y / asFq Q.1.z)) :
    ∃ hOn : OnCurveP R, Θ ⟨R, hOn⟩ = Θ P + Θ Q := by
  set x1 := asFq P.1.x / asFq P.1.z with hx1
  set y1 := asFq P.1.y / asFq P.1.z with hy1
  set x2 := asFq Q.1.x / asFq Q.1.z with hx2
  set y2 := asFq Q.1.y / asFq Q.1.z with hy2
  have hE1 := affine_eq_of_onCurveP P.2 hz1
  have hy1ne : y1 ≠ 0 := div_ne_zero (y_ne_zero_of_onCurveP P.2) hz1
  have hc : asFq P.1.z ^ 2 * asFq Q.1.z ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hz1) (pow_ne_zero 2 hz2)
  have hy2eq : y2 = -y1 := by rw [hyy, neg_neg]
  rw [← hxx, hy2eq] at hRx hRy hRz
  rw [unit_anti_X3] at hRx
  rw [unit_anti_Y3 hE1] at hRy
  rw [unit_anti_Z3] at hRz
  have hxR : asFq R.x = 0 := by rw [hRx, mul_zero]
  have hzR : asFq R.z = 0 := by rw [hRz, mul_zero]
  have hyR : asFq R.y ≠ 0 := by
    rw [hRy]
    refine mul_ne_zero hc ?_
    rw [← unit_anti_Y3 hE1]
    exact unit_anti_Y3_ne_zero hE1 hy1ne
  have hOn : OnCurveP R := onCurveP_of_infinity hxR hyR hzR
  refine ⟨hOn, ?_⟩
  rw [Θ_of_z_eq (P := ⟨R, hOn⟩) hzR, Θ_of_z_ne hz1, Θ_of_z_ne hz2]
  symm
  exact Affine.Point.add_of_Y_eq hxx (by rw [negY_helios]; exact hyy)

/-- Left-infinity case (`z₁ = 0`): the RCB output is a nonzero multiple of `Q`. -/
theorem add_theta_inf_left (P Q : HPt) (R : point.helios.HeliosPoint)
    (hz1 : asFq P.1.z = 0)
    (hRx : asFq R.x = (addCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)
      (asFq Q.1.x) (asFq Q.1.y) (asFq Q.1.z)).1)
    (hRy : asFq R.y = (addCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)
      (asFq Q.1.x) (asFq Q.1.y) (asFq Q.1.z)).2.1)
    (hRz : asFq R.z = (addCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)
      (asFq Q.1.x) (asFq Q.1.y) (asFq Q.1.z)).2.2) :
    ∃ hOn : OnCurveP R, Θ ⟨R, hOn⟩ = Θ P + Θ Q := by
  have hx1 : asFq P.1.x = 0 := x_eq_zero_of_z_eq_zero P.2 hz1
  rw [hx1, hz1] at hRx hRy hRz
  rw [addCoords_inf_left_x] at hRx
  rw [addCoords_inf_left_y] at hRy
  rw [addCoords_inf_left_z] at hRz
  have hc : asFq P.1.y ^ 2 * asFq Q.1.y ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (y_ne_zero_of_onCurveP P.2))
      (y_ne_zero_of_onCurveP Q.2)
  have hOn : OnCurveP R := onCurveP_smul Q hc hRx hRy hRz
  refine ⟨hOn, ?_⟩
  rw [Θ_of_z_eq hz1, zero_add]
  exact Θ_eq_of_smul (R := ⟨R, hOn⟩) (Q := Q) hc hRx hRy hRz

/-- Right-infinity case (`z₂ = 0`): the RCB output is a nonzero multiple of `P`. -/
theorem add_theta_inf_right (P Q : HPt) (R : point.helios.HeliosPoint)
    (hz2 : asFq Q.1.z = 0)
    (hRx : asFq R.x = (addCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)
      (asFq Q.1.x) (asFq Q.1.y) (asFq Q.1.z)).1)
    (hRy : asFq R.y = (addCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)
      (asFq Q.1.x) (asFq Q.1.y) (asFq Q.1.z)).2.1)
    (hRz : asFq R.z = (addCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)
      (asFq Q.1.x) (asFq Q.1.y) (asFq Q.1.z)).2.2) :
    ∃ hOn : OnCurveP R, Θ ⟨R, hOn⟩ = Θ P + Θ Q := by
  have hx2 : asFq Q.1.x = 0 := x_eq_zero_of_z_eq_zero Q.2 hz2
  rw [hx2, hz2] at hRx hRy hRz
  rw [addCoords_inf_right_x] at hRx
  rw [addCoords_inf_right_y] at hRy
  rw [addCoords_inf_right_z] at hRz
  have hc : asFq Q.1.y ^ 2 * asFq P.1.y ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (y_ne_zero_of_onCurveP Q.2))
      (y_ne_zero_of_onCurveP P.2)
  have hOn : OnCurveP R := onCurveP_smul P hc hRx hRy hRz
  refine ⟨hOn, ?_⟩
  rw [Θ_of_z_eq hz2, add_zero]
  exact Θ_eq_of_smul (R := ⟨R, hOn⟩) (Q := P) hc hRx hRy hRz

/-- **Master case analysis for RCB addition**: any representative whose
`asFq`-coordinates are `addCoords` of two on-curve points is itself on the curve,
and `Θ`-represents the mathlib sum. -/
theorem add_theta (P Q : HPt) (R : point.helios.HeliosPoint)
    (hco : mkFq R = addCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)
      (asFq Q.1.x) (asFq Q.1.y) (asFq Q.1.z)) :
    ∃ hOn : OnCurveP R, Θ ⟨R, hOn⟩ = Θ P + Θ Q := by
  have hRx : asFq R.x = (addCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)
      (asFq Q.1.x) (asFq Q.1.y) (asFq Q.1.z)).1 := by rw [← hco]
  have hRy : asFq R.y = (addCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)
      (asFq Q.1.x) (asFq Q.1.y) (asFq Q.1.z)).2.1 := by rw [← hco]
  have hRz : asFq R.z = (addCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)
      (asFq Q.1.x) (asFq Q.1.y) (asFq Q.1.z)).2.2 := by rw [← hco]
  by_cases hz1 : asFq P.1.z = 0
  · exact add_theta_inf_left P Q R hz1 hRx hRy hRz
  by_cases hz2 : asFq Q.1.z = 0
  · exact add_theta_inf_right P Q R hz2 hRx hRy hRz
  rw [addCoords_unitize_x _ _ _ _ _ _ hz1 hz2] at hRx
  rw [addCoords_unitize_y _ _ _ _ _ _ hz1 hz2] at hRy
  rw [addCoords_unitize_z _ _ _ _ _ _ hz1 hz2] at hRz
  by_cases hxx : asFq P.1.x / asFq P.1.z = asFq Q.1.x / asFq Q.1.z
  · rcases y_dichotomy (affine_eq_of_onCurveP P.2 hz1)
      (affine_eq_of_onCurveP Q.2 hz2) hxx with hyy | hyy
    · exact add_theta_tangent P Q R hz1 hz2 hRx hRy hRz hxx hyy
    · exact add_theta_vertical P Q R hz1 hz2 hRx hRy hRz hxx hyy
  · exact add_theta_chord P Q R hz1 hz2 hRx hRy hRz hxx

/-- **Master case analysis for BL doubling with identity fix-up**: any
representative whose `asFq`-coordinates are the translated `double` output of an
on-curve point is itself on the curve, and `Θ`-represents the mathlib doubling. -/
theorem double_theta (P : HPt) (R : point.helios.HeliosPoint)
    (hco : mkFq R = if asFq P.1.x = 0 then ((0 : Fq), (1 : Fq), (0 : Fq))
      else dblCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)) :
    ∃ hOn : OnCurveP R, Θ ⟨R, hOn⟩ = Θ P + Θ P := by
  by_cases hx0 : asFq P.1.x = 0
  · -- identity branch: the input is the identity class, and so is the output
    rw [if_pos hx0] at hco
    simp only [mkFq_def, Prod.mk.injEq] at hco
    obtain ⟨hRx, hRy, hRz⟩ := hco
    have hz0 : asFq P.1.z = 0 := z_eq_zero_of_x_eq_zero P.2 hx0
    have hOn : OnCurveP R :=
      onCurveP_of_infinity hRx (by rw [hRy]; exact one_ne_zero) hRz
    refine ⟨hOn, ?_⟩
    rw [Θ_of_z_eq (P := ⟨R, hOn⟩) hRz, Θ_of_z_eq hz0, add_zero]
  · -- generic branch: dbl-2007-bl-2, which agrees with the tangent formulas
    rw [if_neg hx0] at hco
    have hz1 : asFq P.1.z ≠ 0 := fun h => hx0 (x_eq_zero_of_z_eq_zero P.2 h)
    have hRx : asFq R.x = (dblCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)).1 := by
      rw [← hco]
    have hRy : asFq R.y = (dblCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)).2.1 := by
      rw [← hco]
    have hRz : asFq R.z = (dblCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)).2.2 := by
      rw [← hco]
    rw [dblCoords_unitize_x _ _ _ hz1, dbl_unit_x] at hRx
    rw [dblCoords_unitize_y _ _ _ hz1, dbl_unit_y] at hRy
    rw [dblCoords_unitize_z _ _ _ hz1, dbl_unit_z] at hRz
    set x1 := asFq P.1.x / asFq P.1.z with hx1
    set y1 := asFq P.1.y / asFq P.1.z with hy1
    have hE1 := affine_eq_of_onCurveP P.2 hz1
    have hy1ne : y1 ≠ 0 := div_ne_zero (y_ne_zero_of_onCurveP P.2) hz1
    have hD3 : (2 * y1) ^ 3 ≠ 0 := pow_ne_zero 3 (mul_ne_zero two_ne_zero hy1ne)
    have hc : asFq P.1.z ^ 6 ≠ 0 := pow_ne_zero 6 hz1
    have hzR : asFq R.z ≠ 0 := by rw [hRz]; exact mul_ne_zero hc hD3
    have hne : y1 ≠ W.toAffine.negY x1 y1 := by
      rw [negY_helios]
      exact ne_neg_self hy1ne
    have hXm : asFq R.x / asFq R.z
        = W.toAffine.addX x1 x1 (W.toAffine.slope x1 x1 y1 y1) := by
      rw [hRx, hRz, mul_div_mul_left _ _ hc, addX_helios,
        slope_tangent_helios _ _ hy1ne]
      exact tangent_x_identity hy1ne
    have hYm : asFq R.y / asFq R.z
        = W.toAffine.addY x1 x1 y1 (W.toAffine.slope x1 x1 y1 y1) := by
      rw [hRy, hRz, mul_div_mul_left _ _ hc, addY_helios,
        slope_tangent_helios _ _ hy1ne]
      exact tangent_y_identity hy1ne
    have hNSR : W.toAffine.Nonsingular (asFq R.x / asFq R.z) (asFq R.y / asFq R.z) := by
      rw [hXm, hYm]
      exact Affine.nonsingular_add (theta_ns P hz1) (theta_ns P hz1) fun h => hne h.2
    have hOn : OnCurveP R :=
      onCurveP_of_affine hzR ((nonsingular_iff_helios _ _).mp hNSR)
    refine ⟨hOn, ?_⟩
    rw [Θ_of_z_ne (P := ⟨R, hOn⟩) hzR, Θ_of_z_ne hz1,
      Affine.Point.add_of_Y_ne hne]
    simp only [Affine.Point.some.injEq]
    exact ⟨hXm, hYm⟩

/-- Negation: `(x, -y, z)` is on the curve and `Θ`-represents the mathlib negation. -/
theorem neg_theta (P : HPt) (R : point.helios.HeliosPoint)
    (hco : mkFq R = (asFq P.1.x, -asFq P.1.y, asFq P.1.z)) :
    ∃ hOn : OnCurveP R, Θ ⟨R, hOn⟩ = -Θ P := by
  simp only [mkFq_def, Prod.mk.injEq] at hco
  obtain ⟨hRx, hRy, hRz⟩ := hco
  have hOn : OnCurveP R := by
    obtain ⟨hPeq, _⟩ := P.2
    refine ⟨?_, ?_⟩
    · rw [hRx, hRy, hRz]
      linear_combination hPeq
    · rintro ⟨_, hy0, _⟩
      rw [hRy] at hy0
      exact y_ne_zero_of_onCurveP P.2 (by linear_combination -hy0)
  refine ⟨hOn, ?_⟩
  by_cases hz : asFq P.1.z = 0
  · rw [Θ_of_z_eq (P := ⟨R, hOn⟩) (by rw [hRz]; exact hz), Θ_of_z_eq hz, neg_zero]
  · rw [Θ_of_z_ne (P := ⟨R, hOn⟩) (by rw [hRz]; exact hz), Θ_of_z_ne hz,
      Affine.Point.neg_some]
    simp only [Affine.Point.some.injEq]
    constructor
    · rw [hRx, hRz]
    · rw [hRy, hRz, negY_helios, neg_div]

/-! ## 5. The verified operations on the carrier `HPt`

Each wrapper extracts the `Exists.choose` witness of the corresponding `_ok`
contract (`Spec/Helios/Ops.lean`); the on-curve proof and the `Θ`-homomorphism
equation come from the master case analyses above. The `_ok` theorems record that
the translated Rust function returns exactly the wrapper's representative.

**Exact boundary of the definitional claim.** The `rfl`-definitional layer
(`HClass_zero/add/neg/sub_def` below) ends at these choice-extracted wrappers:
`addP P Q` is *defined* as `(add_coords_ok …).choose`, an `Exists.choose`
witness, not as the generated function applied to `P.1`/`Q.1` (the generated
functions live in the `Result` monad, so a fully definitional link is
impossible). The identification of that witness with the GENERATED Rust
function's output is *propositional*: the `*_ok` equations
(`addP_ok`/`negP_ok`/`subP_ok`/`doubleP_ok`/`idP_ok`/`genP_ok`, each of the
shape `<generated fn> … = .ok (<wrapper> …).1`) are the load-bearing link to
`Funs.lean`. An auditor checking "the group operations are the Rust code" must
check both layers: the `rfl` equations AND the `*_ok` theorems. -/

/-- Total point addition on the carrier, wrapping the translated
`HeliosPoint::add` (RCB complete formulas). -/
noncomputable def addP (P Q : HPt) : HPt :=
  ⟨(add_coords_ok P.1 Q.1).choose,
    (add_theta P Q _ (add_coords_ok P.1 Q.1).choose_spec.2).choose⟩

/-- The translated `add` returns `ok` with exactly `(addP P Q).1`. -/
theorem addP_ok (P Q : HPt) :
    point.helios.HeliosPoint.Insts.CoreOpsArithAddHeliosPointHeliosPoint.add P.1 Q.1
      = .ok (addP P Q).1 :=
  (add_coords_ok P.1 Q.1).choose_spec.1

/-- **`Θ` is additive over the translated `add`.** -/
theorem Θ_addP (P Q : HPt) : Θ (addP P Q) = Θ P + Θ Q :=
  (add_theta P Q _ (add_coords_ok P.1 Q.1).choose_spec.2).choose_spec

/-- Total point negation on the carrier, wrapping the translated
`HeliosPoint::neg`. -/
noncomputable def negP (P : HPt) : HPt :=
  ⟨(neg_coords_ok P.1).choose,
    (neg_theta P _ (neg_coords_ok P.1).choose_spec.2).choose⟩

/-- The translated `neg` returns `ok` with exactly `(negP P).1`. -/
theorem negP_ok (P : HPt) :
    point.helios.HeliosPoint.Insts.CoreOpsArithNegHeliosPoint.neg P.1
      = .ok (negP P).1 :=
  (neg_coords_ok P.1).choose_spec.1

/-- **`Θ` maps the translated `neg` to mathlib negation.** -/
theorem Θ_negP (P : HPt) : Θ (negP P) = -Θ P :=
  (neg_theta P _ (neg_coords_ok P.1).choose_spec.2).choose_spec

/-- Total point doubling on the carrier, wrapping the translated
`Group::double` (dbl-2007-bl-2 plus the `is_identity` select). -/
noncomputable def doubleP (P : HPt) : HPt :=
  ⟨(double_coords_ok P.1).choose,
    (double_theta P _ (double_coords_ok P.1).choose_spec.2).choose⟩

/-- The translated `double` returns `ok` with exactly `(doubleP P).1`. -/
theorem doubleP_ok (P : HPt) :
    point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.double P.1
      = .ok (doubleP P).1 :=
  (double_coords_ok P.1).choose_spec.1

/-- **`Θ` maps the translated `double` to mathlib point doubling.** -/
theorem Θ_doubleP (P : HPt) : Θ (doubleP P) = Θ P + Θ P :=
  (double_theta P _ (double_coords_ok P.1).choose_spec.2).choose_spec

/-- The coordinates of `negP P` are `(x, -y, z)` of `P`. -/
theorem negP_coords (P : HPt) :
    mkFq (negP P).1 = (asFq P.1.x, -asFq P.1.y, asFq P.1.z) :=
  (neg_coords_ok P.1).choose_spec.2

/-- Subtraction: the RCB output on `(P, -Q)` is on-curve and `Θ`-represents the
mathlib difference. -/
theorem sub_theta (P Q : HPt) (R : point.helios.HeliosPoint)
    (hco : mkFq R = addCoords (asFq P.1.x) (asFq P.1.y) (asFq P.1.z)
      (asFq Q.1.x) (-asFq Q.1.y) (asFq Q.1.z)) :
    ∃ hOn : OnCurveP R, Θ ⟨R, hOn⟩ = Θ P - Θ Q := by
  have hN := negP_coords Q
  simp only [mkFq_def, Prod.mk.injEq] at hN
  obtain ⟨hNx, hNy, hNz⟩ := hN
  rw [← hNx, ← hNy, ← hNz] at hco
  obtain ⟨hOn, hΘ⟩ := add_theta P (negP Q) R hco
  exact ⟨hOn, by rw [hΘ, Θ_negP, sub_eq_add_neg]⟩

/-- Total point subtraction on the carrier, wrapping the translated
`HeliosPoint::sub` (= `add ∘ neg` in the generated code). -/
noncomputable def subP (P Q : HPt) : HPt :=
  ⟨(sub_coords_ok P.1 Q.1).choose,
    (sub_theta P Q _ (sub_coords_ok P.1 Q.1).choose_spec.2).choose⟩

/-- The translated `sub` returns `ok` with exactly `(subP P Q).1`. -/
theorem subP_ok (P Q : HPt) :
    point.helios.HeliosPoint.Insts.CoreOpsArithSubHeliosPointHeliosPoint.sub P.1 Q.1
      = .ok (subP P Q).1 :=
  (sub_coords_ok P.1 Q.1).choose_spec.1

/-- **`Θ` maps the translated `sub` to mathlib subtraction.** -/
theorem Θ_subP (P Q : HPt) : Θ (subP P Q) = Θ P - Θ Q :=
  (sub_theta P Q _ (sub_coords_ok P.1 Q.1).choose_spec.2).choose_spec

/-- The identity representative on the carrier, wrapping the translated
`Group::identity` (coordinates `(0, 1, 0)`). -/
noncomputable def idP : HPt :=
  ⟨identity_coords.choose, by
    have hco := identity_coords.choose_spec.2
    have hx : asFq identity_coords.choose.x = 0 := congrArg Prod.fst hco
    have hy : asFq identity_coords.choose.y = 1 := congrArg (fun t => t.2.1) hco
    have hz : asFq identity_coords.choose.z = 0 := congrArg (fun t => t.2.2) hco
    exact onCurveP_of_infinity hx (by rw [hy]; exact one_ne_zero) hz⟩

/-- The translated `identity` returns `ok` with exactly `idP.1`. -/
theorem idP_ok :
    point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.identity
      = .ok idP.1 :=
  identity_coords.choose_spec.1

/-- The coordinates of `idP`. -/
theorem idP_coords : mkFq idP.1 = (0, 1, 0) :=
  identity_coords.choose_spec.2

/-- **`Θ` maps the translated `identity` to the mathlib zero.** -/
theorem Θ_idP : Θ idP = 0 := by
  have hco := idP_coords
  simp only [mkFq_def, Prod.mk.injEq] at hco
  exact Θ_of_z_eq hco.2.2

/-- The generator representative on the carrier, wrapping the translated
`Group::generator` (coordinates `(1, gY, 1)`). -/
noncomputable def genP : HPt :=
  ⟨generator_coords.choose, by
    have hco := generator_coords.choose_spec.2
    have hx : asFq generator_coords.choose.x = 1 := congrArg Prod.fst hco
    have hy : asFq generator_coords.choose.y = (gY : Fq) := congrArg (fun t => t.2.1) hco
    have hz : asFq generator_coords.choose.z = 1 := congrArg (fun t => t.2.2) hco
    refine onCurveP_of_affine (by rw [hz]; exact one_ne_zero) ?_
    rw [hx, hy, hz, div_one, div_one]
    linear_combination generator_on_curve_zmod⟩

/-- The translated `generator` returns `ok` with exactly `genP.1`. -/
theorem genP_ok :
    point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.generator
      = .ok genP.1 :=
  generator_coords.choose_spec.1

/-- The coordinates of `genP`. -/
theorem genP_coords : mkFq genP.1 = (1, (gY : Fq), 1) :=
  generator_coords.choose_spec.2

/-- **`Θ` maps the translated `generator` to the affine point `(1, gY)`.** -/
theorem Θ_genP : Θ genP = Affine.Point.some 1 (gY : Fq) gen_nonsingular := by
  have hco := genP_coords
  simp only [mkFq_def, Prod.mk.injEq] at hco
  rw [Θ_of_z_ne (P := genP) (by rw [hco.2.2]; exact one_ne_zero)]
  simp only [Affine.Point.some.injEq]
  rw [hco.1, hco.2.1, hco.2.2, div_one, div_one]
  exact ⟨rfl, rfl⟩

/-! ## 6. The translated equality tests decide `Θ`-equality -/

/-- `Θ`-equality is exactly the boolean condition computed by the translated
`ct_eq` (both `x`-coordinates zero, or cross-multiplied coordinate agreement). -/
theorem theta_eq_iff (P Q : HPt) :
    Θ P = Θ Q
      ↔ ((asFq P.1.x = 0 ∧ asFq Q.1.x = 0)
        ∨ (asFq P.1.x * asFq Q.1.z = asFq Q.1.x * asFq P.1.z
            ∧ asFq P.1.y * asFq Q.1.z = asFq Q.1.y * asFq P.1.z)) := by
  by_cases hz1 : asFq P.1.z = 0
  · have hx1 : asFq P.1.x = 0 := x_eq_zero_of_z_eq_zero P.2 hz1
    by_cases hz2 : asFq Q.1.z = 0
    · -- both identity class: both sides hold
      have hx2 : asFq Q.1.x = 0 := x_eq_zero_of_z_eq_zero Q.2 hz2
      rw [Θ_of_z_eq hz1, Θ_of_z_eq hz2]
      exact ⟨fun _ => Or.inl ⟨hx1, hx2⟩, fun _ => rfl⟩
    · -- P identity class, Q finite: both sides fail
      rw [Θ_of_z_eq hz1, Θ_of_z_ne hz2]
      constructor
      · intro h
        exact absurd h.symm (Affine.Point.some_ne_zero _)
      · rintro (⟨_, hx2⟩ | ⟨_, hyc⟩)
        · exact absurd (z_eq_zero_of_x_eq_zero Q.2 hx2) hz2
        · rw [hz1, mul_zero] at hyc
          rcases mul_eq_zero.mp hyc with h | h
          · exact absurd h (y_ne_zero_of_onCurveP P.2)
          · exact absurd h hz2
  · by_cases hz2 : asFq Q.1.z = 0
    · -- Q identity class, P finite: both sides fail
      rw [Θ_of_z_ne hz1, Θ_of_z_eq hz2]
      constructor
      · intro h
        exact absurd h (Affine.Point.some_ne_zero _)
      · rintro (⟨hx1, _⟩ | ⟨_, hyc⟩)
        · exact absurd (z_eq_zero_of_x_eq_zero P.2 hx1) hz1
        · rw [hz2, mul_zero] at hyc
          rcases mul_eq_zero.mp hyc.symm with h | h
          · exact absurd h (y_ne_zero_of_onCurveP Q.2)
          · exact absurd h hz1
    · -- both finite: cross-multiplied ratio equality
      rw [Θ_of_z_ne hz1, Θ_of_z_ne hz2]
      simp only [Affine.Point.some.injEq]
      constructor
      · rintro ⟨hxr, hyr⟩
        rw [div_eq_div_iff hz1 hz2] at hxr hyr
        exact Or.inr ⟨hxr, hyr⟩
      · rintro (⟨hx1, _⟩ | ⟨hxc, hyc⟩)
        · exact absurd (z_eq_zero_of_x_eq_zero P.2 hx1) hz1
        · rw [div_eq_div_iff hz1 hz2, div_eq_div_iff hz1 hz2]
          exact ⟨hxc, hyc⟩

/-- **The translated `ct_eq` decides `Θ`-equality.** -/
theorem ct_eq_correct (P Q : HPt) :
    ∃ c, point.helios.HeliosPoint.Insts.SubtleConstantTimeEq.ct_eq P.1 Q.1 = .ok c
      ∧ (c = true ↔ Θ P = Θ Q) := by
  obtain ⟨c, heq, hc⟩ := ct_eq_ok P.1 Q.1
  exact ⟨c, heq, by rw [hc, ← theta_eq_iff]⟩

/-- **The translated `PartialEq::eq` decides `Θ`-equality.** -/
theorem eq_correct (P Q : HPt) :
    ∃ c, point.helios.HeliosPoint.Insts.CoreCmpPartialEqHeliosPoint.eq P.1 Q.1 = .ok c
      ∧ (c = true ↔ Θ P = Θ Q) := by
  obtain ⟨c, heq, hc⟩ := eq_ok P.1 Q.1
  exact ⟨c, heq, by rw [hc, ← theta_eq_iff]⟩

/-- **The translated `is_identity` decides `Θ P = 0`** (soundness of the `x = 0`
test: `B` is a quadratic non-residue). -/
theorem is_identity_correct (P : HPt) :
    ∃ c, point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.is_identity P.1
      = .ok c ∧ (c = true ↔ Θ P = 0) := by
  obtain ⟨c, heq, hc⟩ := is_identity_ok P.1
  refine ⟨c, heq, ?_⟩
  rw [hc]
  constructor
  · intro hx
    exact Θ_of_z_eq (z_eq_zero_of_x_eq_zero P.2 hx)
  · intro hΘ
    by_cases hz : asFq P.1.z = 0
    · exact x_eq_zero_of_z_eq_zero P.2 hz
    · rw [Θ_of_z_ne hz] at hΘ
      exact absurd hΘ (Affine.Point.some_ne_zero _)

/-! ## 7. The quotient group `HClass` and the isomorphism with mathlib -/

/-- Carrier representatives are equivalent when they `Θ`-represent the same
mathlib point (= projective equivalence, by `theta_eq_iff`). -/
instance hptSetoid : Setoid HPt where
  r P Q := Θ P = Θ Q
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem hptSetoid_def (P Q : HPt) : P ≈ Q ↔ Θ P = Θ Q := Iff.rfl

/-- **The verified Helios group**: on-curve representatives modulo projective
equivalence. Its `0`, `+`, unary `-` and binary `-` are the descended translated
Rust operations (`identity`, `add`, `neg`, `sub`) — "descended" meaning: `rfl`
down to the choice-extracted wrappers `idP`/`addP`/`negP`/`subP`, which are tied
to the generated functions by the propositional `*_ok` equations (see the §5
header for the exact boundary of the definitional claim). -/
def HClass : Type := Quotient hptSetoid

/-- The class of a representative. -/
def HClass.mk (P : HPt) : HClass := ⟦P⟧

/-- The abstraction map on classes. -/
def Θbar : HClass → W.toAffine.Point := Quotient.lift Θ fun _ _ h => h

@[simp] theorem Θbar_mk (P : HPt) : Θbar (HClass.mk P) = Θ P := rfl

/-- Zero: the descended translated `identity`. -/
instance : Zero HClass := ⟨⟦idP⟧⟩

theorem HClass_zero_def : (0 : HClass) = HClass.mk idP := rfl

/-- Addition: the descended translated `add`. -/
instance : Add HClass :=
  ⟨Quotient.map₂ addP fun P P' hP Q Q' hQ => by
    show Θ _ = Θ _
    rw [Θ_addP, Θ_addP, (hP : Θ P = Θ P'), (hQ : Θ Q = Θ Q')]⟩

theorem HClass_add_def (P Q : HPt) :
    HClass.mk P + HClass.mk Q = HClass.mk (addP P Q) := rfl

/-- Negation: the descended translated `neg`. -/
instance : Neg HClass :=
  ⟨Quotient.map negP fun P P' hP => by
    show Θ _ = Θ _
    rw [Θ_negP, Θ_negP, (hP : Θ P = Θ P')]⟩

theorem HClass_neg_def (P : HPt) : -HClass.mk P = HClass.mk (negP P) := rfl

/-- Subtraction: the descended translated `sub`. -/
instance : Sub HClass :=
  ⟨Quotient.map₂ subP fun P P' hP Q Q' hQ => by
    show Θ _ = Θ _
    rw [Θ_subP, Θ_subP, (hP : Θ P = Θ P'), (hQ : Θ Q = Θ Q')]⟩

theorem HClass_sub_def (P Q : HPt) :
    HClass.mk P - HClass.mk Q = HClass.mk (subP P Q) := rfl

theorem Θbar_zero : Θbar 0 = 0 := Θ_idP

theorem Θbar_add (a b : HClass) : Θbar (a + b) = Θbar a + Θbar b := by
  refine Quotient.inductionOn₂ a b fun P Q => ?_
  show Θ (addP P Q) = Θ P + Θ Q
  exact Θ_addP P Q

theorem Θbar_neg (a : HClass) : Θbar (-a) = -Θbar a := by
  refine Quotient.inductionOn a fun P => ?_
  exact Θ_negP P

theorem Θbar_sub (a b : HClass) : Θbar (a - b) = Θbar a - Θbar b := by
  refine Quotient.inductionOn₂ a b fun P Q => ?_
  exact Θ_subP P Q

theorem Θbar_injective : Function.Injective Θbar := by
  intro a b h
  refine Quotient.inductionOn₂ a b (fun P Q h => Quotient.sound h) h

/-- A canonical on-curve representative `(x, y, 1)` (via `FieldElement.ofZMod`,
which `asFq` undoes definitionally) for any affine mathlib point of `W`. -/
noncomputable def ofAffine (x y : Fq) (h : W.toAffine.Nonsingular x y) : HPt :=
  ⟨{ x := .ofZMod x, y := .ofZMod y, z := .ofZMod 1 },
    onCurveP_of_affine
      (by show (1 : Fq) ≠ 0; exact one_ne_zero)
      (by
        show (y / 1) ^ 2 = (x / 1) ^ 3 - 3 * (x / 1) + (Bcurve : Fq)
        rw [div_one, div_one]
        exact (nonsingular_iff_helios x y).mp h)⟩

theorem Θ_ofAffine (x y : Fq) (h : W.toAffine.Nonsingular x y) :
    Θ (ofAffine x y h) = Affine.Point.some x y h := by
  have hz : asFq (ofAffine x y h).1.z ≠ 0 := by
    show (1 : Fq) ≠ 0
    exact one_ne_zero
  rw [Θ_of_z_ne hz]
  simp only [Affine.Point.some.injEq]
  constructor
  · show x / (1 : Fq) = x
    exact div_one x
  · show y / (1 : Fq) = y
    exact div_one y

/-- `Θbar` is surjective: every mathlib point has a verified representative. -/
theorem Θbar_surjective : Function.Surjective Θbar := by
  intro A
  cases A with
  | zero => exact ⟨⟦idP⟧, Θ_idP⟩
  | some x y h => exact ⟨⟦ofAffine x y h⟧, Θ_ofAffine x y h⟩

/-- The bijection with the mathlib point group. -/
noncomputable def ΘEquiv : HClass ≃ W.toAffine.Point :=
  Equiv.ofBijective Θbar ⟨Θbar_injective, Θbar_surjective⟩

@[simp] theorem ΘEquiv_apply (a : HClass) : ΘEquiv a = Θbar a := rfl

/-! Auxiliary scalar actions, transported through `ΘEquiv` (they are not
translated Rust operations; they only complete the `AddCommGroup` data and avoid
diamond issues — same pattern as `Spec/Field.lean` and `Spec/Selene/GroupLaw.lean`). -/

noncomputable instance : SMul ℕ HClass := ⟨fun n a => ΘEquiv.symm (n • ΘEquiv a)⟩

noncomputable instance : SMul ℤ HClass := ⟨fun n a => ΘEquiv.symm (n • ΘEquiv a)⟩

theorem Θbar_nsmul (a : HClass) (n : ℕ) : Θbar (n • a) = n • Θbar a := by
  show ΘEquiv (ΘEquiv.symm (n • ΘEquiv a)) = n • ΘEquiv a
  exact ΘEquiv.apply_symm_apply _

theorem Θbar_zsmul (a : HClass) (n : ℤ) : Θbar (n • a) = n • Θbar a := by
  show ΘEquiv (ΘEquiv.symm (n • ΘEquiv a)) = n • ΘEquiv a
  exact ΘEquiv.apply_symm_apply _

/-- **The verified Helios group is an additive commutative group**, with `0`, `+`,
`-` (unary and binary) the descended translated Rust operations (`rfl` to the
choice-extracted wrappers; propositionally tied to the generated functions by
the `*_ok` equations — §5 header). Transported along the injective `Θbar` from
mathlib's `AddCommGroup W.toAffine.Point`. -/
noncomputable instance instAddCommGroupHClass : AddCommGroup HClass :=
  Function.Injective.addCommGroup Θbar Θbar_injective
    Θbar_zero Θbar_add Θbar_neg Θbar_sub Θbar_nsmul Θbar_zsmul

/-- **THE HEADLINE**: the verified Helios group is isomorphic, as an additive
group, to mathlib's group of points of the elliptic curve
`y² = x³ - 3x + B` over `ZMod (2^255 - 19)` — via the coordinate abstraction
`Θbar`. -/
noncomputable def ΘAddEquiv : HClass ≃+ W.toAffine.Point :=
  { ΘEquiv with map_add' := Θbar_add }

@[simp] theorem ΘAddEquiv_apply (a : HClass) : ΘAddEquiv a = Θbar a := rfl

/-! ## 8. Derived class-level facts -/

/-- Smoke test: the group instance is found by type-class resolution. -/
example : AddCommGroup HClass := inferInstance

/-- The descended translated `double` agrees with `+` on classes: the dedicated
dbl-2007-bl-2 circuit computes the same class as the RCB addition of a point
with itself. -/
theorem HClass_double (P : HPt) :
    HClass.mk (doubleP P) = HClass.mk P + HClass.mk P := by
  rw [HClass_add_def]
  exact Quotient.sound (show Θ _ = Θ _ by rw [Θ_doubleP, Θ_addP])

/-- The verified generator class (descended translated `generator`). -/
noncomputable def gen : HClass := HClass.mk genP

/-- `Θbar` maps the verified generator to the affine point `(1, gY)`. -/
theorem Θbar_gen : Θbar gen = Affine.Point.some 1 (gY : Fq) gen_nonsingular :=
  Θ_genP

/-- **The translated `ct_eq` decides equality in the verified group.** -/
theorem ct_eq_decides (P Q : HPt) :
    ∃ c, point.helios.HeliosPoint.Insts.SubtleConstantTimeEq.ct_eq P.1 Q.1 = .ok c
      ∧ (c = true ↔ HClass.mk P = HClass.mk Q) := by
  obtain ⟨c, heq, hc⟩ := ct_eq_correct P Q
  refine ⟨c, heq, ?_⟩
  rw [hc]
  exact ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

/-- **The translated `PartialEq::eq` decides equality in the verified group.** -/
theorem eq_decides (P Q : HPt) :
    ∃ c, point.helios.HeliosPoint.Insts.CoreCmpPartialEqHeliosPoint.eq P.1 Q.1 = .ok c
      ∧ (c = true ↔ HClass.mk P = HClass.mk Q) := by
  obtain ⟨c, heq, hc⟩ := eq_correct P Q
  refine ⟨c, heq, ?_⟩
  rw [hc]
  exact ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

/-- **The translated `is_identity` decides being the zero class.** -/
theorem is_identity_decides (P : HPt) :
    ∃ c, point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.is_identity P.1
      = .ok c ∧ (c = true ↔ HClass.mk P = 0) := by
  obtain ⟨c, heq, hc⟩ := is_identity_correct P
  refine ⟨c, heq, ?_⟩
  rw [hc, HClass_zero_def]
  constructor
  · intro h
    exact Quotient.sound (show Θ _ = Θ _ by rw [h, Θ_idP])
  · intro h
    have h' : Θ P = Θ idP := Quotient.exact h
    rw [h', Θ_idP]

/-- **Non-degeneracy**: the verified generator class is not the zero class —
`Θbar` sends it to the affine point `(1, gY)`, not to the point at infinity.
(So the quotient `HClass` provably does not trivialize.) -/
theorem gen_ne_zero : gen ≠ 0 := by
  intro h
  have h2 : Θbar gen = Θbar 0 := by rw [h]
  rw [Θbar_gen, Θbar_zero] at h2
  exact Affine.Point.some_ne_zero _ h2

/-- **Non-degeneracy, instance form**: `HClass` has (at least) the two distinct
elements `gen` and `0`. -/
instance : Nontrivial HClass := ⟨gen, 0, gen_ne_zero⟩

/-! ## 9. Summary and axiom audit

### Theorem inventory (all PROVED — this file contains NO `sorry`)

Curve layer:
* `W` (the short-Weierstrass curve), `instIsElliptic` (`W.Δ ≠ 0`, kernel certificate);
* `equation_iff_helios`, `nonsingular_iff_helios` (`Δ ≠ 0` makes them equivalent),
  `negY_helios`, `addX_helios`, `addY_helios`, `slope_tangent_helios`,
  `slope_chord_helios`, `gen_nonsingular`.

Carrier and abstraction:
* `OnCurveP`, `HPt`, `Θ`; classification `x_eq_zero_of_z_eq_zero`,
  `z_eq_zero_of_x_eq_zero` (`B` non-residue), `y_ne_zero_of_onCurveP` (no
  2-torsion), `affine_eq_of_onCurveP`, `onCurveP_of_affine`,
  `onCurveP_of_infinity`, `onCurveP_smul`, `Θ_eq_of_smul`.
  (No `Reduced` clause anywhere — the Helios coordinate type is `Fq` itself.)

Coordinate algebra (certificates regenerated for (q, B_helios) by
`tools/gen_lean_helios.py` → `tools/lean_certs_helios.txt`; their integer
cofactors coincide with the Selene certificates because the cofactor extraction
runs over ℤ with `B` symbolic — the printed files differ only in the `Fq`-vs-`F`
spelling of the type ascriptions, NOT in any cofactor; checked by
`linear_combination`/`ring` — kernel only):
* homogeneity: `addCoords_unitize_x/y/z` (degree `(2,2)`),
  `dblCoords_unitize_x/y/z` (degree 6); infinity inputs `addCoords_inf_left_*`,
  `addCoords_inf_right_*` (output = scaled copy of the other input);
* chord: `unit_N4_of_Z3_eq_zero` (CERT1), `unit_cubic_of_N4_eq_zero` (CERT2),
  `unit_Z3_ne_zero` (RCB completeness: `Z₃ ≠ 0` needs the no-2-torsion kernel
  fact `cubic_no_root` — consumed hypotheses: both curve equations and
  `x₁ ≠ x₂`), `unit_X3_cross` (CERT3), `unit_Y3_cross` (CERT4),
  `chord_x_identity`, `chord_y_identity`;
* anti-diagonal: `unit_anti_X3`/`unit_anti_Z3` (identically 0 — pure `ring`),
  `unit_anti_Y3` (CERT5), `unit_cubic_of_Ndbl_eq_zero` (CERT6),
  `unit_anti_Y3_ne_zero` (RCB completeness: the identity-class output has
  `Y₃ ≠ 0`, again via `cubic_no_root` + `y ≠ 0`), `cubic_no_root_hom`;
* diagonal/doubling: `unit_diag_X3/Y3/Z3` (CERT7), `dbl_unit_x/y/z` (the BL
  chain equals the RCB diagonal — pure `ring`), `tangent_x_identity`,
  `tangent_y_identity`, `y_dichotomy`.

The correspondence (each consumes `add_coords_ok`/`double_coords_ok`/… from
`Spec/Helios/Ops.lean` — all of which are precondition-free):
* case lemmas `add_theta_chord`/`_tangent`/`_vertical`/`_inf_left`/`_inf_right`,
  master `add_theta`, `double_theta`, `neg_theta`, `sub_theta`;
* wrappers + homomorphism equations: `addP`/`addP_ok`/`Θ_addP`,
  `negP`/`negP_ok`/`Θ_negP`, `subP`/`subP_ok`/`Θ_subP`,
  `doubleP`/`doubleP_ok`/`Θ_doubleP`, `idP`/`idP_ok`/`Θ_idP`,
  `genP`/`genP_ok`/`Θ_genP`;
* equality deciders: `theta_eq_iff`, `ct_eq_correct`, `eq_correct`,
  `is_identity_correct`.

The group:
* `HClass` (quotient by `Θ`-equality) with `0`/`+`/`-`/binary `-` descended from
  the translated Rust `identity`/`add`/`neg`/`sub`
  (`HClass_zero_def`/`HClass_add_def`/`HClass_neg_def`/`HClass_sub_def` are `rfl`);
* `instAddCommGroupHClass : AddCommGroup HClass`;
* `ΘAddEquiv : HClass ≃+ W.toAffine.Point` — THE HEADLINE;
* `HClass_double` (the BL doubling circuit descends to `+` on classes), `gen`,
  `Θbar_gen`, `ct_eq_decides`, `eq_decides`, `is_identity_decides`;
* non-degeneracy: `gen_ne_zero : gen ≠ 0` and the `Nontrivial HClass` instance
  (the quotient provably does not trivialize).

Auxiliary-data provenance: only `0`/`+`/`-`(unary)/`-`(binary) of `HClass` wrap
translated Rust code; the `ℕ`/`ℤ`-scalar actions are `ΘEquiv`-transported
definitions (not Rust operations), present only to complete the `AddCommGroup`
data without diamonds — same pattern as `Spec/Field.lean` and
`Spec/Selene/GroupLaw.lean`.

Out of scope (exactly as for Selene, plus the dalek boundary): scalar
multiplication, the curve order / cycle property, and the point encodings
(`recover_y`, `GroupEncoding` — these go through the existence-only dalek
`sqrt`/`to_repr` axioms of FunsExternal.lean and have no coordinate contract in
`Spec/Helios/Ops.lean`; nothing in this file touches them).

### Axiom audit (`#print axioms` output re-derived on this build, 2026-07-09)

```
ΘAddEquiv, instAddCommGroupHClass, Θ_addP, Θ_subP, HClass_double, addP_ok :
    [propext, Classical.choice, Quot.sound,
     helioselene.point.helios.B._native.decide.ax_1]
Θ_genP, Θbar_gen, gen_ne_zero, instNontrivialHClass :
    [propext, Classical.choice, Quot.sound,
     helioselene.point.helios.G_Y._native.decide.ax_1]
Θ_doubleP, doubleP_ok, Θ_negP, Θ_idP, ct_eq_decides, eq_decides,
ct_eq_correct, eq_correct, is_identity_correct, is_identity_decides,
add_theta, double_theta, gen_nonsingular, W_delta_ne_zero :
    [propext, Classical.choice, Quot.sound]                        -- kernel-pure
```

(The `#print axioms` output below displays the constants without the
`helioselene.` prefix because this file `open helioselene`s.)

* **NO `sorryAx` anywhere in this file's cone** (in particular the group law does
  not depend on `Invert.step_congruence` or `Selene.sqrt_complete`, the two
  remaining Spec-tree obligations — the Helios point layer never touches the
  4-limb field or the sqrt ladder).
* **NONE of the dalek existence-only axioms** (FunsExternal.lean §dalek: `clone`,
  `sqrt`, `to_repr`, `from_repr`, …) appear in any chain above: every dalek field
  operation consumed here has a concrete `ZMod` model.
* No `native_decide` in any Spec proof; the only compiler-trusted facts in the
  cone are the two string-length autoParam axioms below (which are generated by
  the same `decide +native` mechanism — i.e. the same compiler-level, non-kernel
  trust as `native_decide` — but surfaced as per-constant named axioms rather
  than `Lean.ofReduceBool`). The `…._native.decide.ax_1` axioms are
  the string-length side conditions baked into the generated constant
  DEFINITIONS in `Funs.lean` (Aeneas `toStr` autoParam `by decide +native`,
  README §5c.3): `point.helios.B` enters every chain that evaluates the curve
  constant `B` (the RCB addition consumes it; the BL doubling does not), and
  `point.helios.G_Y` enters the generator chain. Each asserts only that a hex
  string literal is at most `U32.max` bytes; the parsed VALUES are re-proved
  kernel-only in `Spec/Helios/Curve.lean` (`B_ok`/`G_Y_ok` via `toStr_val` +
  `decide`). Unlike Selene, no `field.MODULUS`-family axiom appears anywhere:
  the Helios coordinate field is `Fq` directly, with no limb layer.
* The audit below is informational (`#print axioms` output), not build-enforced;
  an auditor should re-run the `#print axioms` commands and compare against the
  block above. -/

#print axioms ΘAddEquiv
#print axioms instAddCommGroupHClass
#print axioms Θ_addP
#print axioms Θ_doubleP
#print axioms Θ_negP
#print axioms Θ_subP
#print axioms Θ_idP
#print axioms Θ_genP
#print axioms Θbar_gen
#print axioms gen_ne_zero
#print axioms instNontrivialHClass
#print axioms HClass_double
#print axioms addP_ok
#print axioms doubleP_ok
#print axioms ct_eq_decides
#print axioms eq_decides
#print axioms ct_eq_correct
#print axioms eq_correct
#print axioms is_identity_correct
#print axioms is_identity_decides
#print axioms add_theta
#print axioms double_theta
#print axioms gen_nonsingular
#print axioms W_delta_ne_zero

end

end Helios

end HelioseleneSpec
