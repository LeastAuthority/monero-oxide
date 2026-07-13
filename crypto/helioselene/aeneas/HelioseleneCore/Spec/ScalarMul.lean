/- Mathlib-facing type adapters for the Aeneas-translated scalar ladders.

   Aeneas translates Rust's total `Point -> Scalar -> Point` methods to
   `Point -> Scalar -> Result Point`: the `Result` records possible failures
   introduced by the translation of indexing and machine arithmetic.  Lean's
   `SMul R M`, in contrast, contains a pure operation `R -> M -> M`.

   The exact, assumption-free bridge is therefore an action on `Result Point`.
   Its generic `resultSmul_ok` equation is definitional (`rfl`); the two named
   `*_apply_ok` theorems expose the selected instance and apply that equation.
   On a successful point input, the action is therefore exactly the generated
   ladder, with no replacement implementation and no default value on failure.

   `SMul` carries no algebraic laws.  This file certifies the operation's Lean
   type and its definitional connection to generated code;
   `Spec/ScalarMulLaws.lean` proves both generated ladders equal repeated group
   addition and descends them to the corresponding law-bearing actions. -/
import HelioseleneCore.Funs

open Aeneas Aeneas.Std Result
open helioselene

namespace HelioseleneSpec

noncomputable section

/-- Lift an Aeneas-translated endomorphism across a point `Result`.  The scalar
argument is moved first, as required by Lean's `SMul` convention. -/
noncomputable def resultSmul {Point Scalar : Type}
    (mul : Point → Scalar → Result Point)
    (scalar : Scalar) (pointResult : Result Point) : Result Point := do
  let point ← pointResult
  mul point scalar

@[simp] theorem resultSmul_ok {Point Scalar : Type}
    (mul : Point → Scalar → Result Point) (scalar : Scalar) (P : Point) :
    resultSmul mul scalar (.ok P) = mul P scalar :=
  rfl

/-- The translated Selene `Point * Scalar` implementation, exposed as `SMul`
without removing Aeneas's `Result` boundary. -/
noncomputable instance instSMulDalekScalarResultSelenePoint :
    SMul dalek_ff_group.field.FieldElement (Result point.selene.SelenePoint) where
  smul := resultSmul
    point.selene.SelenePoint.Insts.CoreOpsArithMulFieldElementSelenePoint.mul

/-- Applying the Selene `SMul` adapter to a successful point is definitionally
the generated scalar ladder. -/
@[simp] theorem selene_smul_apply_ok
    (scalar : dalek_ff_group.field.FieldElement) (P : point.selene.SelenePoint) :
    scalar • (.ok P : Result point.selene.SelenePoint) =
      point.selene.SelenePoint.Insts.CoreOpsArithMulFieldElementSelenePoint.mul
        P scalar :=
  by
    change instSMulDalekScalarResultSelenePoint.smul scalar (.ok P) = _
    exact resultSmul_ok _ scalar P

/-- The translated Helios `Point * Scalar` implementation, exposed as `SMul`
without removing Aeneas's `Result` boundary. -/
noncomputable instance instSMulHelioseleneFieldResultHeliosPoint :
    SMul field.HelioseleneField (Result point.helios.HeliosPoint) where
  smul := resultSmul
    point.helios.HeliosPoint.Insts.CoreOpsArithMulHelioseleneFieldHeliosPoint.mul

/-- Applying the Helios `SMul` adapter to a successful point is definitionally
the generated scalar ladder. -/
@[simp] theorem helios_smul_apply_ok
    (scalar : field.HelioseleneField) (P : point.helios.HeliosPoint) :
    scalar • (.ok P : Result point.helios.HeliosPoint) =
      point.helios.HeliosPoint.Insts.CoreOpsArithMulHelioseleneFieldHeliosPoint.mul
        P scalar :=
  by
    change instSMulHelioseleneFieldResultHeliosPoint.smul scalar (.ok P) = _
    exact resultSmul_ok _ scalar P

end
end HelioseleneSpec
