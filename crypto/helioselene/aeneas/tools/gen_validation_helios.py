#!/usr/bin/env python3
"""Generate HelioseleneCore/ValidationHelios.lean from helios_vectors.json.

Validates the Aeneas-generated Helios group-law translation (point.helios.*)
against independent ground-truth vectors. Mirrors ValidationSelene.lean, with
two Helios-specific differences:
  * Helios field elements ARE ZMod (2^255 - 19) (concrete models, no limbs),
    so points are built from ZMod literals and read back via .val;
  * there is no translated field inversion (dalek invert stays an axiom), so
    affinization uses ZMod's computable Inv (gcd-based), which #eval/native
    code evaluates fine.

Run:  python3 gen_validation_helios.py
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
VECS = os.path.join(HERE, "helios_vectors.json")
OUT = "/home/user/monero-oxide/crypto/helioselene/aeneas/HelioseleneCore/ValidationHelios.lean"

# Ground truth (independently double-checked; also proved about the
# translation in Spec/Helios): q = 2^255 - 19, curve y^2 = x^3 - 3x + B.
Q = 57896044618658097711785492504343953926634992332820282019728792003956564819949
B = 17523451383230374900436292617863907649717438939964238673872692863501483215968
G_X = 1
G_Y = 43927350165885181914572701368652294970994947138804342515295004363921039321018

with open(VECS) as f:
    data = json.load(f)

# --- sanity: the JSON's constants must match the known ground truth ----------
assert int(data["q"]) == Q, "vector file q mismatch"
assert int(data["B"]) == B, "vector file B mismatch"
assert int(data["G_X"]) == G_X, "vector file G_X mismatch"
assert int(data["G_Y"]) == G_Y, "vector file G_Y mismatch"

# --- sanity: re-verify every vector against an independent Python model ------
def inv(a):
    return pow(a, Q - 2, Q)

def to_affine(p):
    x, y, z = (int(c) % Q for c in p)
    if z == 0:
        return None
    zi = inv(z)
    return ((x * zi) % Q, (y * zi) % Q)

def on_curve(a):
    if a is None:
        return True
    x, y = a
    return (y * y - (x * x * x - 3 * x + B)) % Q == 0

def ec_add(a1, a2):
    if a1 is None:
        return a2
    if a2 is None:
        return a1
    (x1, y1), (x2, y2) = a1, a2
    if x1 == x2 and (y1 + y2) % Q == 0:
        return None
    if a1 == a2:
        lam = (3 * x1 * x1 - 3) * inv(2 * y1) % Q
    else:
        lam = (y2 - y1) * inv(x2 - x1) % Q
    x3 = (lam * lam - x1 - x2) % Q
    return (x3, (lam * (x1 - x3) - y1) % Q)

def expect(v):
    if v.get("out_inf"):
        return None
    return (int(v["out_x"]) % Q, int(v["out_y"]) % Q)

for i, v in enumerate(data["add"]):
    a1, a2 = to_affine(v["p1"]), to_affine(v["p2"])
    assert on_curve(a1) and on_curve(a2), f"add[{i}] input off-curve"
    assert ec_add(a1, a2) == expect(v), f"add[{i}] ground truth mismatch"
for i, v in enumerate(data["double"]):
    a = to_affine(v["pt"])
    assert on_curve(a), f"double[{i}] input off-curve"
    assert ec_add(a, a) == expect(v), f"double[{i}] ground truth mismatch"
for i, v in enumerate(data["neg"]):
    a = to_affine(v["pt"])
    assert a is not None and on_curve(a), f"neg[{i}] input bad"
    x, y = a
    assert (x, (Q - y) % Q) == (int(v["out_x"]), int(v["out_y"])), \
        f"neg[{i}] ground truth mismatch"
for i, v in enumerate(data["ct_eq"]):
    assert (to_affine(v["p1"]) == to_affine(v["p2"])) == v["eq"], \
        f"ct_eq[{i}] ground truth mismatch"
for i, v in enumerate(data["from_xy"]):
    assert on_curve((int(v["x"]) % Q, int(v["y"]) % Q)) == v["ok"], \
        f"from_xy[{i}] ground truth mismatch"

# --- Lean rendering -----------------------------------------------------------
def triple(p):
    return f"({int(p[0])}, {int(p[1])}, {int(p[2])})"

def aff(v):
    if v.get("out_inf"):
        return "none"
    return f"some ({int(v['out_x'])}, {int(v['out_y'])})"

add_lines = [f"  ({triple(v['p1'])}, {triple(v['p2'])}, {aff(v)})"
             for v in data["add"]]
dbl_lines = [f"  ({triple(v['pt'])}, {aff(v)})" for v in data["double"]]
neg_lines = [f"  ({triple(v['pt'])}, {int(v['out_x'])}, {int(v['out_y'])})"
             for v in data["neg"]]
cte_lines = [f"  ({triple(v['p1'])}, {triple(v['p2'])}, "
             f"{'true' if v['eq'] else 'false'})" for v in data["ct_eq"]]
fxy_lines = [f"  ({int(v['x'])}, {int(v['y'])}, "
             f"{'true' if v['ok'] else 'false'})" for v in data["from_xy"]]

def vec_list(name, ty, lines):
    body = ",\n".join(lines)
    return f"def {name} : List ({ty}) := [\n{body}]\n"

# Negative-control raw material (taken from the vectors themselves).
add0 = data["add"][0]
add_inf = next(v for v in data["add"] if v["out_inf"])
add_inf_p1_aff = to_affine(add_inf["p1"])
dbl0 = data["double"][0]
neg0 = data["neg"][0]
cte0 = data["ct_eq"][0]
fxy0 = data["from_xy"][0]

neg_controls = f"""def negControls : List (String × Bool) := [
  ("add/out_x+1", chkAdd ({triple(add0['p1'])}, {triple(add0['p2'])}, some ({int(add0['out_x']) + 1}, {int(add0['out_y'])}))),
  ("add/out_y+1", chkAdd ({triple(add0['p1'])}, {triple(add0['p2'])}, some ({int(add0['out_x'])}, {int(add0['out_y']) + 1}))),
  ("add/inf-flip", chkAdd ({triple(add0['p1'])}, {triple(add0['p2'])}, none)),
  ("add/inf-flip'", chkAdd ({triple(add_inf['p1'])}, {triple(add_inf['p2'])}, some ({add_inf_p1_aff[0]}, {add_inf_p1_aff[1]}))),
  ("double/out_y+1", chkDouble ({triple(dbl0['pt'])}, some ({int(dbl0['out_x'])}, {int(dbl0['out_y']) + 1}))),
  ("neg/out_x+1", chkNeg ({triple(neg0['pt'])}, {int(neg0['out_x']) + 1}, {int(neg0['out_y'])})),
  ("ct_eq/flip", chkCtEq ({triple(cte0['p1'])}, {triple(cte0['p2'])}, {'false' if cte0['eq'] else 'true'})),
  ("from_xy/flip", chkFromXy ({int(fxy0['x'])}, {int(fxy0['y'])}, {'false' if fxy0['ok'] else 'true'}))]
"""

lean = f"""-- Validation of the Aeneas-generated Helios group-law translation
-- (point.helios.*) against independent ground-truth test vectors
-- (75 vectors; source: scratchpad helios/helios_vectors.json, generated by
-- helios/gen_validation_helios.py — do not edit the vector lists by hand).
--
-- This file is imported by nothing. Like Validation.lean / ValidationSelene.lean
-- it is allowed to use `native_decide` (the per-theorem native-decide axioms
-- stay quarantined here).
--
-- ***Scope caveat (Helios vs Selene):*** the Helios coordinate type
-- `dalek_ff_group.field.FieldElement` is DEFINED as `ZMod (2^255 - 19)` and its
-- arithmetic models in FunsExternal.lean are the literal ZMod operations
-- (`ok (a * b)` etc.) — there is no limb representation and no reduction code
-- on this side of the boundary. So these vectors validate the TRANSLATION of
-- the group-law formulas plus the model plumbing (constants via from_u256 /
-- from_be_hex, Choice/CtOption conventions, conditional_select, projective
-- identity handling), NOT any field-arithmetic implementation: the field ops
-- are ideal by construction. This is a strictly weaker signal than
-- ValidationSelene.lean, where the vectors also exercise the verified
-- limb-level field code end-to-end. (The dalek field ops themselves are
-- trusted axioms/models — see the FunsExternal.lean dalek boundary section.)
--
-- Conventions (mirroring the Rust code and the extraction models):
--   * HeliosPoint is projective (x, y, z); the vectors' group-law outputs are
--     given in AFFINE coordinates (or the identity class, `out_inf`), so the
--     checker normalizes the projective output before comparing. There is no
--     translated Helios field inversion (dalek `invert` remains an
--     existence-only axiom), so affinization uses ZMod's computable `Inv`
--     (gcd-based; harness-side only, not part of the validated code).
--   * The identity class is x = 0 (what the translated `is_identity` tests);
--     on the curve this coincides with z = 0 because B is a quadratic
--     non-residue mod 2^255 - 19 (no affine point has x = 0; kernel-proved in
--     Spec/Helios). The checker requires BOTH, so a degenerate (x = 0, z ≠ 0)
--     or (x ≠ 0, z = 0) output is flagged.
--   * Choice = Bool, CtOption T = T × Bool (value, is_some).
import HelioseleneCore.Funs

open Aeneas Aeneas.Std Result
open helioselene

namespace HelioseleneValidationHelios

set_option maxRecDepth 4096

/-! ## Harness -/

/-- The Helios base field: `dalek_ff_group.field.FieldElement` is (by
    definition, TypesExternal.lean) exactly this `ZMod`. -/
abbrev Fq := ZMod (2 ^ 255 - 19)

abbrev Fe := dalek_ff_group.field.FieldElement
abbrev Pt := point.helios.HeliosPoint

/-- Embed a natural number as a Helios field element (reduced by the cast). -/
def ofN (n : Nat) : Fe := dalek_ff_group.field.FieldElement.ofZMod (n : Fq)

/-- The canonical `Nat` value (< 2^255 - 19) of a Helios field element. -/
def feVal (a : Fe) : Nat := (dalek_ff_group.field.FieldElement.toZMod a).val

/-- Build a projective Helios point from `Nat` coordinates. -/
def mkPt (v : Nat × Nat × Nat) : Pt := {{ x := ofN v.1, y := ofN v.2.1, z := ofN v.2.2 }}

/-- Expected affine result of a projective group-law output; `none` = identity. -/
abbrev Aff := Option (Nat × Nat)

/-- Normalize a projective group-law output and compare against ground truth.
    Identity is decided exactly as the translated code does (`is_identity`,
    i.e. x = 0) AND as z = 0 (the on-curve-equivalent predicate); a
    non-identity output is affinized with ZMod's computable field inverse
    (x/z, y/z) — harness-side, since no translated Helios inversion exists. -/
def chkProjOut (r : Result Pt) (exp : Aff) : Bool :=
  match r with
  | .ok p =>
    match
      point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.is_identity
        p with
    | .ok idFlag =>
      match exp with
      | none => idFlag && feVal p.z == 0
      | some (ex, ey) =>
        !idFlag && feVal p.z != 0 &&
        (let zinv : Fq := (dalek_ff_group.field.FieldElement.toZMod p.z)⁻¹
         (dalek_ff_group.field.FieldElement.toZMod p.x * zinv).val == ex &&
         (dalek_ff_group.field.FieldElement.toZMod p.y * zinv).val == ey)
    | _ => false
  | _ => false

def chkAdd (v : (Nat × Nat × Nat) × (Nat × Nat × Nat) × Aff) : Bool :=
  chkProjOut
    (point.helios.HeliosPoint.Insts.CoreOpsArithAddHeliosPointHeliosPoint.add
      (mkPt v.1) (mkPt v.2.1)) v.2.2

def chkDouble (v : (Nat × Nat × Nat) × Aff) : Bool :=
  chkProjOut
    (point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.double
      (mkPt v.1)) v.2

def chkNeg (v : (Nat × Nat × Nat) × Nat × Nat) : Bool :=
  chkProjOut
    (point.helios.HeliosPoint.Insts.CoreOpsArithNegHeliosPoint.neg (mkPt v.1))
    (some (v.2.1, v.2.2))

/-- Projective (class) equality; `Choice = Bool` against the expected flag. -/
def chkCtEq (v : (Nat × Nat × Nat) × (Nat × Nat × Nat) × Bool) : Bool :=
  match
    point.helios.HeliosPoint.Insts.SubtleConstantTimeEq.ct_eq (mkPt v.1)
      (mkPt v.2.1) with
  | .ok c => c == v.2.2
  | _ => false

/-- `from_xy` returns `CtOption Pt`; the flag must match `ok` and the stored
    point (kept even when invalid, subtle semantics) must be (x, y, 1). -/
def chkFromXy (v : Nat × Nat × Bool) : Bool :=
  match point.helios.HeliosPoint.from_xy (ofN v.1) (ofN v.2.1) with
  | .ok (p, flag) =>
    flag == v.2.2 && feVal p.x == v.1 && feVal p.y == v.2.1 && feVal p.z == 1
  | _ => false

/-- Indices of failing vectors (empty ↔ all pass). -/
def failIdxs {{α}} [Inhabited α] (chk : α → Bool) (vs : List α) : List Nat :=
  (List.range vs.length).filter (fun i => !chk vs[i]!)

/-- Run one vector class in IO, reporting failures and interpreted wall clock. -/
def run {{α}} [Inhabited α] (label : String) (chk : α → Bool) (vs : List α) :
    IO Unit := do
  -- `IO.lazyPure` keeps the checker run (a) from being lifted out as a closed
  -- term and pre-evaluated, and (b) from being sunk below the second timestamp
  -- (both compiler transformations make naive timers report 0).
  let vs ← IO.lazyPure (fun _ => vs)
  let t0 ← IO.monoMsNow
  let bad ← IO.lazyPure (fun _ => failIdxs chk vs)
  let t1 ← IO.monoMsNow
  if bad.isEmpty then
    IO.println s!"{{label}}: {{vs.length}}/{{vs.length}} ok ({{t1 - t0}} ms interpreted)"
  else
    IO.println s!"{{label}}: FAIL at indices {{bad}} of {{vs.length}} ({{t1 - t0}} ms)"

/-! ## Ground-truth vectors (independent of the Rust/Lean implementation)

Inputs are projective (some are the affine point rescaled by a random z);
expected outputs are affine, `none` = point at infinity. -/

/-- q = 2^255 - 19 -/
def qVal : Nat := {Q}

{vec_list("addVecs", "(Nat × Nat × Nat) × (Nat × Nat × Nat) × Aff", add_lines)}
{vec_list("doubleVecs", "(Nat × Nat × Nat) × Aff", dbl_lines)}
{vec_list("negVecs", "(Nat × Nat × Nat) × Nat × Nat", neg_lines)}
{vec_list("ctEqVecs", "(Nat × Nat × Nat) × (Nat × Nat × Nat) × Bool", cte_lines)}
{vec_list("fromXyVecs", "Nat × Nat × Bool", fxy_lines)}
/-! ## Ad-hoc structural checks -/

/-- The translated curve constants match the independent ground truth
    (the same literals fixed in the Spec/Helios COMMON section). -/
def chkConstants : Bool :=
  match point.helios.G_X, point.helios.G_Y, point.helios.B with
  | .ok gx, .ok gy, .ok bb =>
    feVal gx == {G_X} &&
    feVal gy == {G_Y} &&
    feVal bb == {B}
  | _, _, _ => false

/-- The generator satisfies the curve equation: G_Y² = curve_equation(G_X),
    with z = 1 (both sides computed by the translated code). -/
def chkGeneratorOnCurve : Bool :=
  match point.helios.G with
  | .ok g =>
    (match dalek_ff_group.field.FieldElement.Insts.FfField.square g.y,
        point.helios.curve_equation g.x with
     | .ok l, .ok r => feVal l == feVal r && feVal g.z == 1
     | _, _ => false)
  | _ => false

/-- `is_identity identity = true` and `identity = (0, 1, 0)`. -/
def chkIdentityIsIdentity : Bool :=
  match
    point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.identity with
  | .ok id =>
    (match
       point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.is_identity
         id with
     | .ok c => c && feVal id.x == 0 && feVal id.y == 1 && feVal id.z == 0
     | _ => false)
  | _ => false

/-- `is_identity generator = false`. -/
def chkGeneratorNotIdentity : Bool :=
  match
    point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.generator with
  | .ok g =>
    (match
       point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.is_identity
         g with
     | .ok c => !c
     | _ => false)
  | _ => false

def adHocChecks : List (String × Bool) := [
  ("constants", chkConstants),
  ("generator-on-curve", chkGeneratorOnCurve),
  ("identity-is-identity", chkIdentityIsIdentity),
  ("generator-not-identity", chkGeneratorNotIdentity)]

/-! ## Negative controls

One corrupted vector per class (expected value bumped / flag flipped /
identity-class flag flipped both ways). Every checker MUST report `false` on
its corrupted vector — this shows the harness actually detects mismatches and
the positive theorems below are not vacuous. -/

{neg_controls}
/-! ## Interpreted runs (mismatch localization + per-class timing) -/

#eval run "helios add    " chkAdd addVecs
#eval run "helios double " chkDouble doubleVecs
#eval run "helios neg    " chkNeg negVecs
#eval run "helios ct_eq  " chkCtEq ctEqVecs
#eval run "helios from_xy" chkFromXy fromXyVecs
#eval run "helios ad-hoc " (fun (c : String × Bool) => c.2) adHocChecks
#eval run "helios negctrl" (fun (c : String × Bool) => !c.2) negControls

/-! ## Machine-checked theorems (`native_decide`; one
`validationHelios_*._native.native_decide.ax_1_1` axiom each) -/

theorem validationHelios_add : addVecs.all chkAdd = true := by native_decide
theorem validationHelios_double : doubleVecs.all chkDouble = true := by
  native_decide
theorem validationHelios_neg : negVecs.all chkNeg = true := by native_decide
theorem validationHelios_ct_eq : ctEqVecs.all chkCtEq = true := by native_decide
theorem validationHelios_from_xy : fromXyVecs.all chkFromXy = true := by
  native_decide
theorem validationHelios_adhoc : adHocChecks.all (·.2) = true := by
  native_decide
/-- Every deliberately corrupted vector is detected (checker returns false). -/
theorem validationHelios_negative_controls :
    negControls.all (fun c => !c.2) = true := by native_decide

end HelioseleneValidationHelios
"""

with open(OUT, "w") as f:
    f.write(lean)
print(f"wrote {OUT} ({len(lean.splitlines())} lines)")
print(f"classes: add={len(data['add'])} double={len(data['double'])} "
      f"neg={len(data['neg'])} ct_eq={len(data['ct_eq'])} "
      f"from_xy={len(data['from_xy'])}")
