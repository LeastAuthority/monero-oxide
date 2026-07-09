/- Coordinate-level contracts for the Aeneas-translated Helios point operations.

   Helios sibling of `Spec/Selene/Ops.lean` (the template). It is MUCH lighter than the
   Selene file because the Helios coordinate type `dalek_ff_group.field.FieldElement`
   (TypesExternal.lean) IS `ZMod (2^255 - 19)` definitionally, and every dalek field
   operation the translated point code calls has a CONCRETE model in FunsExternal.lean
   that returns `ok` of the literal `ZMod` operation. Consequently:
   * there is no limb layer, no `Reduced` invariant and no preconditions anywhere;
   * the abstraction map is (essentially) the identity `asFq = FieldElement.toZMod`
     (Curve.lean), so the per-op `_ok` spec lemmas of the Selene file collapse to
     one-line `rfl` facts (`fadd_def` etc. below);
   * every point-level `_ok` contract is proved by unfolding the generated body,
     collapsing the `ok`-binds with `simp only [..., bind_tc_ok]`, and closing the
     coordinate identities with `ring`.

   Contents:
   * `mkFq P = (asFq P.x, asFq P.y, asFq P.z)` point plumbing;
   * `addCoords`/`dblCoords`: `Fq`-level mirrors of the exact operation chains the code
     computes (RCB add-2015-rcb-3 for `a = -3` with constant `b = Bcurve`, and
     dbl-2007-bl-2), as `let`-chains — the SAME export shape as the Selene template, so
     the Helios `GroupLaw` file consumes them identically — plus `ring`-normalized closed
     polynomial forms (`addCoords_x/y/z`, `dblCoords_x/y/z`);
   * `add_coords_ok`, `sub_coords_ok`, `neg_coords_ok`, `double_coords_ok` (including the
     `is_identity`-driven conditional select: the result is `(0,1,0)` when `asFq P.x = 0`),
     `identity_coords`, `generator_coords`, `is_identity_ok`, `ct_eq_ok`, `eq_ok`,
     `curve_equation_ok`, `from_xy_ok`.

   Scope note: `point.helios.recover_y` and the `GroupEncoding` `from_bytes`/`to_bytes`
   are OUT of scope here — they go through the dalek `ff::Field::sqrt` /
   `PrimeField::to_repr` boundary, which is kept as existence-only AXIOMS
   (FunsExternal.lean), so no coordinate contract is provable (or claimed) for them.
   Unlike Selene there is consequently no `sqrt_ok`/`recover_y_ok` section and no
   `sorry` anywhere in this file.

   No new axioms, no `native_decide`; lemmas that mention the generated hex-string
   constants (`add_coords_ok`, `sub_coords_ok`, `generator_coords`, `curve_equation_ok`,
   `from_xy_ok` via `B_ok`/`G_ok`, Curve.lean) inherit the `<const>._native.decide.ax_1`
   string-length axioms baked into Funs.lean (README §5c.3). -/
import HelioseleneCore.Spec.Helios.Curve

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std Result
open helioselene

namespace HelioseleneSpec

namespace Helios

/-! ## The concrete dalek field models, as `rfl` rewrite rules

Each translated field operation used by the Helios point code has a concrete model
`fun .. => ok ..` in FunsExternal.lean; the lemmas below are its applied, `rfl`-provable
form, phrased through `toZMod`/`ofZMod` so a single `simp only` pass turns a generated
point-op body into `ok` of an explicit `Fq` coordinate record. -/

private theorem fadd_def (a b : dalek_ff_group.field.FieldElement) :
    dalek_ff_group.field.FieldElement.Insts.CoreOpsArithAddFieldElementFieldElement.add
      a b = ok (.ofZMod (a.toZMod + b.toZMod)) := rfl

private theorem fsub_def (a b : dalek_ff_group.field.FieldElement) :
    dalek_ff_group.field.FieldElement.Insts.CoreOpsArithSubFieldElementFieldElement.sub
      a b = ok (.ofZMod (a.toZMod - b.toZMod)) := rfl

private theorem fmul_def (a b : dalek_ff_group.field.FieldElement) :
    dalek_ff_group.field.FieldElement.Insts.CoreOpsArithMulFieldElementFieldElement.mul
      a b = ok (.ofZMod (a.toZMod * b.toZMod)) := rfl

private theorem fneg_def (a : dalek_ff_group.field.FieldElement) :
    dalek_ff_group.field.FieldElement.Insts.CoreOpsArithNegFieldElement.neg a
      = ok (.ofZMod (-a.toZMod)) := rfl

private theorem fdouble_def (a : dalek_ff_group.field.FieldElement) :
    dalek_ff_group.field.FieldElement.Insts.FfField.double a
      = ok (.ofZMod (a.toZMod + a.toZMod)) := rfl

private theorem fsquare_def (a : dalek_ff_group.field.FieldElement) :
    dalek_ff_group.field.FieldElement.Insts.FfField.square a
      = ok (.ofZMod (a.toZMod * a.toZMod)) := rfl

private theorem fZERO_def :
    dalek_ff_group.field.FieldElement.Insts.FfField.ZERO = ok (.ofZMod 0) := rfl

private theorem fONE_def :
    dalek_ff_group.field.FieldElement.Insts.FfField.ONE = ok (.ofZMod 1) := rfl

private theorem fis_zero_def (a : dalek_ff_group.field.FieldElement) :
    dalek_ff_group.field.FieldElement.Insts.FfField.is_zero a
      = ok (decide (a.toZMod = 0)) := rfl

private theorem fct_eq_def (a b : dalek_ff_group.field.FieldElement) :
    dalek_ff_group.field.FieldElement.Insts.SubtleConstantTimeEq.ct_eq a b
      = ok (decide (a.toZMod = b.toZMod)) := rfl

private theorem fcond_select_def (a b : dalek_ff_group.field.FieldElement)
    (c : subtle.Choice) :
    dalek_ff_group.field.FieldElement.Insts.SubtleConditionallySelectable.conditional_select
      a b c = ok (if c then b else a) := rfl

private theorem choice_and_def (a b : subtle.Choice) :
    subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand a b = ok (a && b) := rfl

private theorem choice_or_def (a b : subtle.Choice) :
    subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor a b = ok (a || b) := rfl

private theorem ctoption_new_def {T : Type} (v : T) (c : subtle.Choice) :
    subtle.CtOption.new v c = ok (v, c) := rfl

/-! ## Point plumbing

No `Reduced` predicate: `asFq` is total and (definitionally) injective, so every
contract below is precondition-free. -/

/-- The `Fq`-image of a point's projective coordinate triple (the Helios counterpart of
Selene's `mkψ`; here the abstraction map is the definitional `asFq`). -/
abbrev mkFq (P : point.helios.HeliosPoint) : Fq × Fq × Fq :=
  (asFq P.x, asFq P.y, asFq P.z)

theorem mkFq_def (P : point.helios.HeliosPoint) :
    mkFq P = (asFq P.x, asFq P.y, asFq P.z) := rfl

/-! ## `Fq`-level coordinate formulas

`addCoords` mirrors — operation by operation, in the code's order — the complete
addition chain of `HeliosPoint::add` (RCB 2015, algorithm 4 shape, `a = -3`, constant
`b = Bcurve`); `dblCoords` mirrors `Group::double`'s dbl-2007-bl-2 chain (before the
identity fix-up select, which `double_coords_ok` handles as a top-level `if`). Same
`let`-chain export shape as `Spec/Selene/Ops.lean` (doublings spelled `u + u`, matching
the concrete dalek `double` model). -/

/-- `Fq`-level mirror of the translated RCB addition chain. Argument order:
`(x1, y1, z1)` = self, `(x2, y2, z2)` = other. -/
def addCoords (x1 y1 z1 x2 y2 z2 : Fq) : Fq × Fq × Fq :=
  let b : Fq := (Bcurve : Fq)
  let t0 := x1 * x2
  let t1 := y1 * y2
  let t2 := z1 * z2
  let t3 := (x1 + y1) * (x2 + y2) - (t0 + t1)   -- x1·y2 + x2·y1
  let t4 := (y1 + z1) * (y2 + z2) - (t1 + t2)   -- y1·z2 + y2·z1
  let t5 := (x1 + z1) * (x2 + z2) - (t0 + t2)   -- x1·z2 + x2·z1
  let u := t5 - b * t2
  let v := u + (u + u)                           -- 3·(t5 - b·t2)
  let zc := t1 - v
  let xc := t1 + v
  let w := b * t5 - (t2 + t2 + t2) - t0
  let ww := (w + w) + w                          -- 3·(b·t5 - 3·t2 - t0)
  let s := (t0 + t0) + t0 - (t2 + t2 + t2)       -- 3·t0 - 3·t2
  (t3 * xc - t4 * ww, xc * zc + s * ww, t4 * zc + t3 * s)

/-- `Fq`-level mirror of the translated dbl-2007-bl-2 doubling chain (generic branch;
the identity branch is handled by the `if` in `double_coords_ok`). -/
def dblCoords (x y z : Fq) : Fq × Fq × Fq :=
  let m := (x - z) * (x + z)
  let w := (m + m) + m                           -- 3·(x² - z²)
  let s := y * z + y * z
  let sss := s * (s * s)
  let r := y * s
  let b := x * r + x * r
  let h := w * w - (b + b)
  (h * s, w * (b - h) - (r * r + r * r), sss)

/-! ### Normalized closed forms (for the group-law development; identical statement
shapes to the Selene template, over `Fq`) -/

theorem addCoords_x (x1 y1 z1 x2 y2 z2 : Fq) :
    (addCoords x1 y1 z1 x2 y2 z2).1
      = (x1 * y2 + x2 * y1)
          * (y1 * y2 + 3 * (x1 * z2 + x2 * z1) - 3 * (Bcurve : Fq) * (z1 * z2))
        - 3 * (y1 * z2 + y2 * z1)
          * ((Bcurve : Fq) * (x1 * z2 + x2 * z1) - 3 * (z1 * z2) - x1 * x2) := by
  simp only [addCoords]
  ring

theorem addCoords_y (x1 y1 z1 x2 y2 z2 : Fq) :
    (addCoords x1 y1 z1 x2 y2 z2).2.1
      = (y1 * y2 + 3 * (x1 * z2 + x2 * z1) - 3 * (Bcurve : Fq) * (z1 * z2))
          * (y1 * y2 - 3 * (x1 * z2 + x2 * z1) + 3 * (Bcurve : Fq) * (z1 * z2))
        + (3 * (x1 * x2) - 3 * (z1 * z2)) * 3
          * ((Bcurve : Fq) * (x1 * z2 + x2 * z1) - 3 * (z1 * z2) - x1 * x2) := by
  simp only [addCoords]
  ring

theorem addCoords_z (x1 y1 z1 x2 y2 z2 : Fq) :
    (addCoords x1 y1 z1 x2 y2 z2).2.2
      = (y1 * z2 + y2 * z1)
          * (y1 * y2 - 3 * (x1 * z2 + x2 * z1) + 3 * (Bcurve : Fq) * (z1 * z2))
        + (x1 * y2 + x2 * y1) * (3 * (x1 * x2) - 3 * (z1 * z2)) := by
  simp only [addCoords]
  ring

theorem dblCoords_x (x y z : Fq) :
    (dblCoords x y z).1
      = (3 * (x ^ 2 - z ^ 2) * (3 * (x ^ 2 - z ^ 2)) - 8 * x * y ^ 2 * z) * (2 * y * z) := by
  simp only [dblCoords]
  ring

theorem dblCoords_y (x y z : Fq) :
    (dblCoords x y z).2.1
      = 3 * (x ^ 2 - z ^ 2)
          * (4 * x * y ^ 2 * z - (9 * (x ^ 2 - z ^ 2) ^ 2 - 8 * x * y ^ 2 * z))
        - 8 * y ^ 4 * z ^ 2 := by
  simp only [dblCoords]
  ring

theorem dblCoords_z (x y z : Fq) :
    (dblCoords x y z).2.2 = 8 * y ^ 3 * z ^ 3 := by
  simp only [dblCoords]
  ring

/-! ## Point addition (`HeliosPoint::add`, RCB complete formulas) -/

/-- **Point addition drives to the RCB coordinate polynomials.** The translated
`HeliosPoint::add` always returns `ok`, with `Fq`-coordinates exactly `addCoords` of the
input coordinates. (No preconditions: the coordinate type is `Fq` itself.) -/
theorem add_coords_ok (P Q : point.helios.HeliosPoint) :
    ∃ R, point.helios.HeliosPoint.Insts.CoreOpsArithAddHeliosPointHeliosPoint.add P Q
        = ok R
      ∧ mkFq R = addCoords (asFq P.x) (asFq P.y) (asFq P.z) (asFq Q.x) (asFq Q.y) (asFq Q.z) := by
  unfold point.helios.HeliosPoint.Insts.CoreOpsArithAddHeliosPointHeliosPoint.add
  simp only [fmul_def, fadd_def, fsub_def, fdouble_def, B_ok, bind_tc_ok, toZMod_ofZMod]
  refine ⟨_, rfl, ?_⟩
  -- the mirror chain is operation-exact: after collapsing `toZMod ∘ ofZMod` the two
  -- sides are syntactically equal
  simp only [mkFq, addCoords, toZMod_ofZMod]

/-! ## Negation and subtraction -/

/-- **Point negation negates the `y`-coordinate.** -/
theorem neg_coords_ok (P : point.helios.HeliosPoint) :
    ∃ R, point.helios.HeliosPoint.Insts.CoreOpsArithNegHeliosPoint.neg P = ok R
      ∧ mkFq R = (asFq P.x, -asFq P.y, asFq P.z) := by
  unfold point.helios.HeliosPoint.Insts.CoreOpsArithNegHeliosPoint.neg
  simp only [fneg_def, bind_tc_ok]
  exact ⟨_, rfl, rfl⟩

/-- **Point subtraction is `add ∘ neg`**: the coordinates are `addCoords` of `P` and the
negated `Q`. -/
theorem sub_coords_ok (P Q : point.helios.HeliosPoint) :
    ∃ R, point.helios.HeliosPoint.Insts.CoreOpsArithSubHeliosPointHeliosPoint.sub P Q
        = ok R
      ∧ mkFq R = addCoords (asFq P.x) (asFq P.y) (asFq P.z) (asFq Q.x) (-asFq Q.y) (asFq Q.z) := by
  obtain ⟨N, hNeq, hNco⟩ := neg_coords_ok Q
  obtain ⟨R, hReq, hRco⟩ := add_coords_ok P N
  refine ⟨R, ?_, ?_⟩
  · unfold point.helios.HeliosPoint.Insts.CoreOpsArithSubHeliosPointHeliosPoint.sub
    rw [hNeq]
    simp only [bind_tc_ok]
    exact hReq
  · rw [hRco]
    simp only [mkFq, Prod.mk.injEq] at hNco
    rw [hNco.1, hNco.2.1, hNco.2.2]

/-! ## Identity, generator, `is_identity` -/

/-- **The translated identity has coordinates `(0, 1, 0)`.** -/
theorem identity_coords :
    ∃ I, point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.identity
        = ok I
      ∧ mkFq I = (0, 1, 0) := by
  unfold point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.identity
  simp only [fZERO_def, fONE_def, bind_tc_ok]
  exact ⟨_, rfl, rfl⟩

/-- **The translated generator has coordinates `(1, gY, 1)`** (consumes `G_ok`,
Curve.lean). -/
theorem generator_coords :
    ∃ G, point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.generator
        = ok G
      ∧ mkFq G = (1, (gY : Fq), 1) := by
  unfold point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.generator
  rw [G_ok]
  exact ⟨_, rfl, rfl⟩

/-- **`is_identity` tests `x = 0`** (sound as an identity test because `B` is a
non-residue — `no_affine_x_zero`, Curve.lean; note it does NOT test `z = 0`). -/
theorem is_identity_ok (P : point.helios.HeliosPoint) :
    ∃ c, point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.is_identity P
        = ok c
      ∧ (c = true ↔ asFq P.x = 0) := by
  unfold point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.is_identity
  simp only [fZERO_def, fct_eq_def, bind_tc_ok, toZMod_ofZMod]
  exact ⟨_, rfl, by simp only [decide_eq_true_eq, asFq]⟩

/-! ## Doubling (dbl-2007-bl-2 with the identity fix-up select) -/

/-- **Doubling drives to the dbl-2007-bl-2 coordinate polynomials**, with the
identity-flagged case (`is_identity`, i.e. `asFq P.x = 0` — with the concrete
`ct_eq`/`conditional_select` models this is a `decide` case split) returning
`(0, 1, 0)`. -/
theorem double_coords_ok (P : point.helios.HeliosPoint) :
    ∃ R, point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.double P
        = ok R
      ∧ mkFq R = if asFq P.x = 0 then ((0 : Fq), (1 : Fq), (0 : Fq))
                 else dblCoords (asFq P.x) (asFq P.y) (asFq P.z) := by
  unfold point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.double
  unfold point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.identity
  unfold point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.is_identity
  unfold point.helios.HeliosPoint.Insts.SubtleConditionallySelectable.conditional_select
  simp only [fmul_def, fadd_def, fsub_def, fdouble_def, fsquare_def, fZERO_def, fONE_def,
    fct_eq_def, fcond_select_def, bind_tc_ok, toZMod_ofZMod]
  refine ⟨_, rfl, ?_⟩
  by_cases hx : asFq P.x = 0
  · rw [if_pos hx]
    simp only [mkFq, hx, decide_true, if_true, toZMod_ofZMod]
  · rw [if_neg hx]
    simp only [mkFq, decide_eq_true_eq, hx, if_false, dblCoords, toZMod_ofZMod]

/-! ## Constant-time point equality and `PartialEq` -/

/-- **`ct_eq` computes projective coordinate equality**: true iff both `x`-coordinates
are zero, or the cross-multiplied `x`- and `y`-coordinates agree. (Exactly the boolean
combination the code computes, over `Fq`.) -/
theorem ct_eq_ok (P Q : point.helios.HeliosPoint) :
    ∃ c, point.helios.HeliosPoint.Insts.SubtleConstantTimeEq.ct_eq P Q = ok c
      ∧ (c = true ↔
          ((asFq P.x = 0 ∧ asFq Q.x = 0) ∨
           (asFq P.x * asFq Q.z = asFq Q.x * asFq P.z ∧
            asFq P.y * asFq Q.z = asFq Q.y * asFq P.z))) := by
  unfold point.helios.HeliosPoint.Insts.SubtleConstantTimeEq.ct_eq
  simp only [fmul_def, fis_zero_def, fct_eq_def, choice_and_def, choice_or_def,
    bind_tc_ok, toZMod_ofZMod]
  exact ⟨_, rfl, by
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, asFq]⟩

/-- **`PartialEq::eq` is `ct_eq` converted to `bool`** (the model conversion is the
identity), so it satisfies the same contract. -/
theorem eq_ok (P Q : point.helios.HeliosPoint) :
    ∃ c, point.helios.HeliosPoint.Insts.CoreCmpPartialEqHeliosPoint.eq P Q = ok c
      ∧ (c = true ↔
          ((asFq P.x = 0 ∧ asFq Q.x = 0) ∨
           (asFq P.x * asFq Q.z = asFq Q.x * asFq P.z ∧
            asFq P.y * asFq Q.z = asFq Q.y * asFq P.z))) := by
  obtain ⟨c, heq, hc⟩ := ct_eq_ok P Q
  refine ⟨c, ?_, hc⟩
  unfold point.helios.HeliosPoint.Insts.CoreCmpPartialEqHeliosPoint.eq
  rw [heq]
  simp only [bind_tc_ok]
  rfl

/-! ## `curve_equation` and `from_xy` -/

/-- **`curve_equation` computes the RHS of the curve equation**, exactly as the code
does: `(x·x)·x - 2·x - x + B`. -/
theorem curve_equation_ok (x : dalek_ff_group.field.FieldElement) :
    ∃ r, point.helios.curve_equation x = ok r
      ∧ asFq r = (asFq x * asFq x) * asFq x - 2 * asFq x - asFq x + (Bcurve : Fq) := by
  unfold point.helios.curve_equation
  simp only [fsquare_def, fmul_def, fdouble_def, fsub_def, fadd_def, B_ok, bind_tc_ok,
    toZMod_ofZMod]
  refine ⟨_, rfl, ?_⟩
  simp only [asFq, toZMod_ofZMod]
  ring

/-- **`from_xy` builds `(x : y : 1)` and flags whether the affine curve equation
holds**: `y·y = (x·x)·x - 2·x - x + B`. -/
theorem from_xy_ok (x y : dalek_ff_group.field.FieldElement) :
    ∃ P flag, point.helios.HeliosPoint.from_xy x y = ok (P, flag)
      ∧ mkFq P = (asFq x, asFq y, 1)
      ∧ (flag = true ↔
          asFq y * asFq y
            = (asFq x * asFq x) * asFq x - 2 * asFq x - asFq x + (Bcurve : Fq)) := by
  obtain ⟨r, hreq, hr⟩ := curve_equation_ok x
  unfold point.helios.HeliosPoint.from_xy
  simp only [fONE_def, fsquare_def, hreq, fct_eq_def, ctoption_new_def, bind_tc_ok,
    toZMod_ofZMod]
  refine ⟨_, _, rfl, rfl, ?_⟩
  rw [decide_eq_true_eq, ← hr]

end Helios

end HelioseleneSpec
