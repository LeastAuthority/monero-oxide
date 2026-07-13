/- Axiom audit for the proved inversion contract and translated scalar ladders. -/
import HelioseleneCore.Spec.Invert
import HelioseleneCore.Spec.ScalarMul
import HelioseleneCore.Spec.ScalarMulLaws

open HelioseleneSpec

#print axioms invert_ok
#print axioms Invert.step_congruence
#print axioms Invert.step_loop0_value_spec
#print axioms Invert.step_loop1_value_spec
#print axioms Invert.step_loop2_value_spec
#print axioms Invert.step_loop3_value_spec
#print axioms Invert.step_loop4_value_spec
#print axioms Invert.cong_of_double

#print axioms helioselene.point.selene.SelenePoint.Insts.CoreOpsArithMulFieldElementSelenePoint.mul
#print axioms helioselene.point.helios.HeliosPoint.Insts.CoreOpsArithMulHelioseleneFieldHeliosPoint.mul
#print axioms dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.to_repr
#print axioms selene_smul_apply_ok
#print axioms helios_smul_apply_ok
#print axioms ScalarMul.SeleneLadder.mul_spec
#print axioms ScalarMul.HeliosLadder.mul_spec
#print axioms ScalarMul.SeleneAction.result_smul_eq_generated_rep
#print axioms ScalarMul.HeliosAction.result_smul_eq_generated_rep
#print axioms ScalarMul.SeleneAction.moduleOfExponent
#print axioms ScalarMul.HeliosAction.moduleOfExponent
