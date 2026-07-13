/- Final assembly: the Aeneas-translated helioselene field IS a mathlib `Field`.

   This file wraps the verified `Result`-valued field operations of the generated
   code (`helioselene.field.*`, specified by the `_ok` contract lemmas of the
   sibling Spec files) into total operations on the reduced-representative carrier

     `HField := { u : Uint4 // u.toNat < p }`      (defined in `Spec.Phi`)

   and proves

     `instance : Field HField`                     (`instFieldHField`)
     `def φRing : HField ≃+* ZMod p`               (ring isomorphism with mathlib)

   i.e. the transpiled helioselene field is, as a ring (hence as a field), exactly
   `ZMod p` for the (kernel-proved, `Spec.Prime`) prime
   `p = 2^255 - 0x8cab7e2e6960ce8067af49720ee20ad`.

   Sorry status: this file and its inversion dependency cone are sorry-free.
   `invert_ok` consumes the proved `Invert.step_congruence` theorem for the
   repaired four-limb 0/p/2p carry chain. Consequently `HField.inv`, the
   `Inv`/`Div` instances, `φ_inv`, `φ_div`, `instFieldHField` and the
   `example : Field HField` smoke check contain no `sorryAx`. See the axiom
   audit at the bottom of this file.

   Provenance of the instance data: only `add`/`sub`/`neg`/`mul`/`inv` wrap
   Aeneas-translated Rust functions — `Div` (Rust exposes no division), `Zero`/`One`
   (spec-side literals matching the Rust constants' values) and every
   `ZMod`-transported auxiliary field (`nsmul`/`npow`/`natCast`/… — including `^`,
   which is NOT the Rust `pow`, excluded from the translation) are not
   Rust-translated operations. The axiom audit at the bottom of this file is
   informational (`#print axioms` output), not build-enforced. -/
import HelioseleneCore.Spec.Externals
import HelioseleneCore.Spec.Phi
import HelioseleneCore.Spec.Linear
import HelioseleneCore.Spec.Repr
import HelioseleneCore.Spec.Reduction
import HelioseleneCore.Spec.Invert
import HelioseleneCore.Spec.Prime
import Mathlib

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std Result
open helioselene

-- The wrappers extract `Exists.choose` witnesses from the `_ok` contract lemmas
-- (Classical.choice); none of this file needs to execute.
noncomputable section

namespace HelioseleneSpec

open crypto_bigint.uint HelioseleneModel

/-! ## Primality of `p`, in the `HelioseleneSpec.p` spelling

`Spec.Prime` proves `Fact (Nat.Prime <literal>)`; `p` is a plain `def` of that
literal, so the transport is definitional. This gives `Field (ZMod p)`. -/

instance instFactPPrime : Fact (Nat.Prime p) := ⟨p_prime⟩

example : Field (ZMod p) := inferInstance

/-! ## Extensionality for `HField` -/

/-- Two reduced representatives with equal `toNat` values are equal
    (`Uint.toNat` is injective, `Spec.Externals`). -/
theorem HField.ext_toNat {x y : HField} (h : x.val.toNat = y.val.toNat) : x = y :=
  Subtype.ext (Uint.toNat_inj h)

/-! ## Total wrappers around the verified operations

Each `_ok` contract lemma states `∃ r, <generated op> = .ok r ∧ r.toNat = <math>`;
the wrapper extracts the witness (`Classical.choice` via `Exists.choose`), and the
`% p` shape of the value equation provides reducedness via `Nat.mod_lt`. -/

/-- The additive identity: the 4-limb encoding of `0`, as a spec-side literal.
    Equal in value to the translated `field.HelioseleneField.Insts.FfField.ZERO`
    (Rust `Field::ZERO = Self(U256::ZERO)`; the private `FfField_ZERO_spec` in
    `Spec.Linear` proves its `toNat` is 0), but not defined through it. -/
def HField.zero : HField :=
  ⟨Uint.ofNat 4#usize 0, by
    rw [Uint4.toNat_ofNat (by norm_num)]; exact p_pos⟩

/-- The multiplicative identity: the 4-limb encoding of `1`, as a spec-side literal.
    Matches the value of the (untranslated) Rust constant `Field::ONE = Self(U256::ONE)`;
    `ff::Field::ONE` has no counterpart in Funs.lean — it was dropped together with the
    excluded `pow`/`Product` code. -/
def HField.one : HField :=
  ⟨Uint.ofNat 4#usize 1, by
    rw [Uint4.toNat_ofNat (by norm_num)]; exact one_lt_p⟩

/-- Total field addition, extracted from the verified
    `field.HelioseleneField.Insts.CoreOpsArithAddHelioseleneFieldHelioseleneField.add`. -/
def HField.add (x y : HField) : HField :=
  ⟨(add_ok x.val y.val x.property y.property).choose, by
    rw [(add_ok x.val y.val x.property y.property).choose_spec.2]
    exact Nat.mod_lt _ p_pos⟩

/-- Total field subtraction, extracted from the verified
    `...CoreOpsArithSubHelioseleneFieldHelioseleneField.sub`. -/
def HField.sub (x y : HField) : HField :=
  ⟨(sub_ok x.val y.val x.property y.property).choose, by
    rw [(sub_ok x.val y.val x.property y.property).choose_spec.2]
    exact Nat.mod_lt _ p_pos⟩

/-- Total field negation, extracted from the verified
    `...CoreOpsArithNegHelioseleneField.neg`. -/
def HField.neg (x : HField) : HField :=
  ⟨(neg_ok x.val x.property).choose, by
    rw [(neg_ok x.val x.property).choose_spec.2]
    exact Nat.mod_lt _ p_pos⟩

/-- Total field multiplication, extracted from the verified
    `...CoreOpsArithMulHelioseleneFieldHelioseleneField.mul`. -/
def HField.mul (x y : HField) : HField :=
  ⟨(mul_ok x.val y.val).choose, by
    rw [(mul_ok x.val y.val).choose_spec.2]
    exact Nat.mod_lt _ p_pos⟩

/-- Total field doubling, extracted from the verified `field.verified.double`. -/
def HField.double (x : HField) : HField :=
  ⟨(double_ok x.val x.property).choose, by
    rw [(double_ok x.val x.property).choose_spec.2]
    exact Nat.mod_lt _ p_pos⟩

/-- Total field squaring, extracted from the verified `field.verified.square`. -/
def HField.square (x : HField) : HField :=
  ⟨(square_ok x.val).choose, by
    rw [(square_ok x.val).choose_spec.2]
    exact Nat.mod_lt _ p_pos⟩

/-- Total field inversion (with mathlib's `0⁻¹ = 0` convention), extracted from the
    verified `field.verified.invert.invert`; `invert_ok` and its
    `Invert.step_congruence` dependency are fully proved. -/
def HField.inv (x : HField) : HField :=
  ⟨(invert_ok x.val x.property).choose,
    (invert_ok x.val x.property).choose_spec.choose_spec.2.1⟩

/-! ## Data instances -/

instance : Zero HField := ⟨HField.zero⟩
instance : One HField := ⟨HField.one⟩
instance : Add HField := ⟨HField.add⟩
instance : Mul HField := ⟨HField.mul⟩
instance : Neg HField := ⟨HField.neg⟩
instance : Sub HField := ⟨HField.sub⟩
instance : Inv HField := ⟨HField.inv⟩

/-- Rust defines no division for `HelioseleneField`; mathlib's `a / b` is defined
    here as `a * b⁻¹`, i.e. multiplication (Rust `mul`) by the Rust-verified
    inverse — it does not wrap any translated Rust operation of its own. -/
instance : Div HField := ⟨fun x y => x * y⁻¹⟩

/-! ## Value lemmas (the notation reduces definitionally to the wrappers) -/

@[simp] theorem HField.zero_val : (0 : HField).val.toNat = 0 :=
  Uint4.toNat_ofNat (by norm_num)

@[simp] theorem HField.one_val : (1 : HField).val.toNat = 1 :=
  Uint4.toNat_ofNat (by norm_num)

theorem HField.add_val (x y : HField) :
    (x + y).val.toNat = (x.val.toNat + y.val.toNat) % p :=
  (add_ok x.val y.val x.property y.property).choose_spec.2

theorem HField.sub_val (x y : HField) :
    (x - y).val.toNat = (x.val.toNat + (p - y.val.toNat)) % p :=
  (sub_ok x.val y.val x.property y.property).choose_spec.2

theorem HField.neg_val (x : HField) :
    (-x).val.toNat = (p - x.val.toNat) % p :=
  (neg_ok x.val x.property).choose_spec.2

theorem HField.mul_val (x y : HField) :
    (x * y).val.toNat = (x.val.toNat * y.val.toNat) % p :=
  (mul_ok x.val y.val).choose_spec.2

theorem HField.double_val (x : HField) :
    (HField.double x).val.toNat = (2 * x.val.toNat) % p :=
  (double_ok x.val x.property).choose_spec.2

theorem HField.square_val (x : HField) :
    (HField.square x).val.toNat = (x.val.toNat * x.val.toNat) % p :=
  (square_ok x.val).choose_spec.2

/-- At zero, the verified inversion returns the mathlib convention `0⁻¹ = 0`. -/
theorem HField.inv_val_of_zero (x : HField) (h : x.val.toNat = 0) :
    (x⁻¹ : HField).val.toNat = 0 :=
  (invert_ok x.val x.property).choose_spec.choose_spec.2.2.2.1 h

/-- Away from zero, the verified inversion is a genuine modular inverse. -/
theorem HField.inv_val_of_ne_zero (x : HField) (h : x.val.toNat ≠ 0) :
    (x.val.toNat * (x⁻¹ : HField).val.toNat) % p = 1 :=
  (invert_ok x.val x.property).choose_spec.choose_spec.2.2.2.2 h

/-- Consistency of the dedicated doubling circuit with addition. -/
theorem HField.double_eq_add_self (x : HField) : HField.double x = x + x := by
  apply HField.ext_toNat
  rw [HField.double_val, HField.add_val]
  congr 1
  ring

/-- Consistency of the dedicated squaring circuit with multiplication. -/
theorem HField.square_eq_mul_self (x : HField) : HField.square x = x * x := by
  apply HField.ext_toNat
  rw [HField.square_val, HField.mul_val]

/-! ## Auxiliary structure, transported through `equivZMod`

These make every remaining field of `Function.Injective.field` an
`Equiv.apply_symm_apply` one-liner and avoid all diamond issues: the final
`Field` structure literally reuses these instances as its data.

None of these correspond to translated Rust code — in particular `^` (npow/zpow)
is NOT the Rust `pow`, which was excluded from the translation (see README §1),
and the casts do not go through the Rust `From<uN>` impls; they are the unique
`ZMod`-transported extensions and only matter for avoiding mathlib diamond
issues. -/

instance : SMul ℕ HField := ⟨fun n x => equivZMod.symm (n • equivZMod x)⟩
instance : SMul ℤ HField := ⟨fun n x => equivZMod.symm (n • equivZMod x)⟩
instance : SMul NNRat HField := ⟨fun q x => equivZMod.symm (q • equivZMod x)⟩
instance : SMul ℚ HField := ⟨fun q x => equivZMod.symm (q • equivZMod x)⟩
instance : Pow HField ℕ := ⟨fun x n => equivZMod.symm (equivZMod x ^ n)⟩
instance : Pow HField ℤ := ⟨fun x n => equivZMod.symm (equivZMod x ^ n)⟩
instance : NatCast HField := ⟨fun n => equivZMod.symm (n : ZMod p)⟩
instance : IntCast HField := ⟨fun n => equivZMod.symm (n : ZMod p)⟩
instance : NNRatCast HField := ⟨fun q => equivZMod.symm (q : ZMod p)⟩
instance : RatCast HField := ⟨fun q => equivZMod.symm (q : ZMod p)⟩

/-! ## The homomorphism equations for `φ : HField → ZMod p` -/

theorem φ_zero : φ (0 : HField) = 0 := by
  show ((0 : HField).val.toNat : ZMod p) = 0
  rw [HField.zero_val]
  exact Nat.cast_zero

theorem φ_one : φ (1 : HField) = 1 := by
  show ((1 : HField).val.toNat : ZMod p) = 1
  rw [HField.one_val]
  exact Nat.cast_one

theorem φ_add (x y : HField) : φ (x + y) = φ x + φ y := by
  unfold φ
  rw [HField.add_val]
  push_cast [ZMod.natCast_mod]
  ring

theorem φ_mul (x y : HField) : φ (x * y) = φ x * φ y := by
  unfold φ
  rw [HField.mul_val]
  push_cast [ZMod.natCast_mod]
  ring

theorem φ_neg (x : HField) : φ (-x) = -φ x := by
  unfold φ
  rw [HField.neg_val]
  push_cast [ZMod.natCast_mod, Nat.cast_sub (le_of_lt x.property)]
  rw [ZMod.natCast_self]
  ring

theorem φ_sub (x y : HField) : φ (x - y) = φ x - φ y := by
  unfold φ
  rw [HField.sub_val]
  push_cast [ZMod.natCast_mod, Nat.cast_sub (le_of_lt y.property)]
  rw [ZMod.natCast_self]
  ring

theorem φ_inv (x : HField) : φ x⁻¹ = (φ x)⁻¹ := by
  by_cases h : x.val.toNat = 0
  · show ((x⁻¹ : HField).val.toNat : ZMod p) = ((x.val.toNat : ℕ) : ZMod p)⁻¹
    rw [HField.inv_val_of_zero x h, h]
    simp
  · have key : φ x * φ x⁻¹ = 1 := by
      show ((x.val.toNat : ℕ) : ZMod p) * ((x⁻¹ : HField).val.toNat : ZMod p) = 1
      rw [← Nat.cast_mul, ← ZMod.natCast_mod, HField.inv_val_of_ne_zero x h, Nat.cast_one]
    exact eq_inv_of_mul_eq_one_right key

theorem φ_div (x y : HField) : φ (x / y) = φ x / φ y := by
  show φ (x * y⁻¹) = φ x / φ y
  rw [φ_mul, φ_inv, div_eq_mul_inv]

/-! ### Transported auxiliary equations: all `Equiv.apply_symm_apply` -/

theorem φ_nsmul (n : ℕ) (x : HField) : φ (n • x) = n • φ x := by
  show equivZMod (equivZMod.symm (n • equivZMod x)) = n • equivZMod x
  exact equivZMod.apply_symm_apply _

theorem φ_zsmul (n : ℤ) (x : HField) : φ (n • x) = n • φ x := by
  show equivZMod (equivZMod.symm (n • equivZMod x)) = n • equivZMod x
  exact equivZMod.apply_symm_apply _

theorem φ_nnqsmul (q : NNRat) (x : HField) : φ (q • x) = q • φ x := by
  show equivZMod (equivZMod.symm (q • equivZMod x)) = q • equivZMod x
  exact equivZMod.apply_symm_apply _

theorem φ_qsmul (q : ℚ) (x : HField) : φ (q • x) = q • φ x := by
  show equivZMod (equivZMod.symm (q • equivZMod x)) = q • equivZMod x
  exact equivZMod.apply_symm_apply _

theorem φ_npow (x : HField) (n : ℕ) : φ (x ^ n) = φ x ^ n := by
  show equivZMod (equivZMod.symm (equivZMod x ^ n)) = equivZMod x ^ n
  exact equivZMod.apply_symm_apply _

theorem φ_zpow (x : HField) (n : ℤ) : φ (x ^ n) = φ x ^ n := by
  show equivZMod (equivZMod.symm (equivZMod x ^ n)) = equivZMod x ^ n
  exact equivZMod.apply_symm_apply _

theorem φ_natCast (n : ℕ) : φ (n : HField) = n := by
  show equivZMod (equivZMod.symm ((n : ℕ) : ZMod p)) = ((n : ℕ) : ZMod p)
  exact equivZMod.apply_symm_apply _

theorem φ_intCast (n : ℤ) : φ (n : HField) = n := by
  show equivZMod (equivZMod.symm ((n : ℤ) : ZMod p)) = ((n : ℤ) : ZMod p)
  exact equivZMod.apply_symm_apply _

theorem φ_nnratCast (q : NNRat) : φ (q : HField) = q := by
  show equivZMod (equivZMod.symm ((q : NNRat) : ZMod p)) = ((q : NNRat) : ZMod p)
  exact equivZMod.apply_symm_apply _

theorem φ_ratCast (q : ℚ) : φ (q : HField) = q := by
  show equivZMod (equivZMod.symm ((q : ℚ) : ZMod p)) = ((q : ℚ) : ZMod p)
  exact equivZMod.apply_symm_apply _

/-! ## THE instance -/

/-- **The Aeneas-translated helioselene field is a mathlib `Field`.**
    Pulled back from `Field (ZMod p)` along the injection `φ`, whose hom equations
    are exactly the verified `_ok` contracts of the generated code. -/
instance instFieldHField : Field HField :=
  Function.Injective.field φ φ_injective φ_zero φ_one φ_add φ_mul φ_neg φ_sub
    φ_inv φ_div φ_nsmul φ_zsmul φ_nnqsmul φ_qsmul φ_npow φ_zpow
    φ_natCast φ_intCast φ_nnratCast φ_ratCast

/-- Smoke check: the instance is found by type-class resolution. -/
example : Field HField := inferInstance

/-! ## Ring equivalence: `HField ≃+* ZMod p` -/

/-- The transpiled helioselene field is, as a ring, exactly `ZMod p`. -/
def φRing : HField ≃+* ZMod p where
  toEquiv := equivZMod
  map_mul' := φ_mul
  map_add' := φ_add

@[simp] theorem φRing_apply (x : HField) : φRing x = φ x := rfl

@[simp] theorem φRing_symm_apply (z : ZMod p) : φRing.symm z = ofZMod z := rfl

/-! ## Re-exported corollaries (proved in `Spec.Phi`) -/

example : Fintype HField := inferInstance
example : Finite HField := inferInstance
example : Fintype.card HField = p := card_hfield
example : Fintype.card HField =
    57896044618658097711785492504343953926623305935230693509004809574567321395027 :=
  card_hfield

/-! ## Axiom audit

`#print axioms` output observed on this build (2026-07-10):

```
instFieldHField : [propext, Classical.choice, Quot.sound,
    field.MODULUS._native.decide.ax_1,
    field.verified.MODULUS_255_DISTANCE._native.decide.ax_1,
    field.verified.red.TWO_MODULUS_255_DISTANCE._native.decide.ax_1,
    field.verified.invert.invert.step.MODULUS_XOR_TWO_MODULUS._native.decide.ax_1]
φRing           : [propext, Classical.choice, Quot.sound,
    field.MODULUS._native.decide.ax_1,
    field.verified.MODULUS_255_DISTANCE._native.decide.ax_1,
    field.verified.red.TWO_MODULUS_255_DISTANCE._native.decide.ax_1]     -- NO sorryAx
φ_add           : [propext, Classical.choice, Quot.sound, field.MODULUS._native.decide.ax_1]
φ_mul           : like φRing (adds the two reduction-distance constants)   -- NO sorryAx
φ_neg, φ_sub    : like φ_add                                              -- NO sorryAx
φ_inv           : [propext, Classical.choice, Quot.sound,
    field.MODULUS._native.decide.ax_1,
    field.verified.invert.invert.step.MODULUS_XOR_TWO_MODULUS._native.decide.ax_1]
HField.mul_val  : like φ_mul                                               -- NO sorryAx
card_hfield     : [propext, Classical.choice, Quot.sound]
p_prime         : [propext, Classical.choice, Quot.sound]                  -- kernel-only Pratt
```

Notes:
* `propext`, `Classical.choice`, `Quot.sound` — the three standard mathlib axioms.
* The `…._native.decide.ax_1` axioms are embedded in the generated DEFINITIONS in
  `Funs.lean`: the four hex-literal constants (`field.MODULUS`,
  `field.verified.MODULUS_255_DISTANCE`, `field.verified.red.TWO_MODULUS_255_DISTANCE`,
  `field.verified.invert.invert.step.MODULUS_XOR_TWO_MODULUS`) call
  `Aeneas.Std.toStr`, whose length side-condition autoParam is `by decide +native`.
  Every statement mentioning those constants inherits them; no proof in the Spec
  tree itself uses `native_decide` (the Spec constants lemmas re-prove the parses
  with kernel `decide`).
* No declaration listed above contains `sorryAx`; in particular the former
  inversion taint on `HField.inv`, `φ_inv`, `φ_div` and `instFieldHField` is gone.
* The remaining dependencies are the three standard mathlib axioms plus the
  generated constant-parser axioms listed above. -/

#print axioms instFieldHField
#print axioms φRing
#print axioms φ_add
#print axioms φ_mul
#print axioms φ_neg
#print axioms φ_sub
#print axioms φ_inv
#print axioms HField.mul_val
#print axioms card_hfield
#print axioms p_prime

/-! ## Whole-tree proof status

The project-local `HelioseleneCore/Spec` tree contains no proof holes.
`Invert.step_congruence` and `Selene.sqrt_complete`, the final two historical
obligations, are both proved. The `sorry` declarations reported while building
the upstream Aeneas support library are outside this project's theorem cone;
the `#print axioms` results above contain no `sorryAx`. -/

end HelioseleneSpec

end
