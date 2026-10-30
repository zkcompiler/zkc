import ZkcSecurity.Families.Stark.ConstraintBatching
import ZkcSecurity.Families.Stark.DeepBatching
import ZkcTools.DeclarationAudit

/-! Literal transitive axiom receipts for every authored mathematical root.
The computed audits additionally cover generated/private declarations and all
direct upstream roots appearing in types or bodies. -/

#print axioms ZkcSecurity.Families.Stark.vanishing
#print axioms ZkcSecurity.Families.Stark.vanishing_monic
#print axioms ZkcSecurity.Families.Stark.vanishing_natDegree
#print axioms ZkcSecurity.Families.Stark.vanishing_eval_zero_iff
#print axioms ZkcSecurity.Families.Stark.factor_degree_lt
#print axioms ZkcSecurity.Families.Stark.vanishes_iff_exists_quotient
#print axioms ZkcSecurity.Families.Stark.residual
#print axioms ZkcSecurity.Families.Stark.residual_eq_zero_iff
#print axioms ZkcSecurity.Families.Stark.residual_degree_le
#print axioms ZkcSecurity.Families.Stark.interpolate
#print axioms ZkcSecurity.Families.Stark.interpolate_eval
#print axioms ZkcSecurity.Families.Stark.interpolate_degree_lt
#print axioms ZkcSecurity.Families.Stark.deepQuotient
#print axioms ZkcSecurity.Families.Stark.deepQuotient_reconstruct
#print axioms ZkcSecurity.Families.Stark.deepQuotient_degree_lt
#print axioms ZkcSecurity.Families.Stark.deepQuotient_eval
#print axioms ZkcSecurity.Families.Stark.lift_answers
#print axioms ZkcSecurity.Families.Stark.powerBatch
#print axioms ZkcSecurity.Families.Stark.powerBatch_eval
#print axioms ZkcSecurity.Families.Stark.coefficientTest
#print axioms ZkcSecurity.Families.Stark.coefficientTest_coeff
#print axioms ZkcSecurity.Families.Stark.coefficientTest_eval
#print axioms ZkcSecurity.Families.Stark.powerBatch_degree_lt
#print axioms ZkcSecurity.Families.Stark.powerBatch_residual
#print axioms ZkcSecurity.Families.Stark.powerBatch_zero_uniform_le
#print axioms ZkcSecurity.Families.Stark.multivariate_zero_uniform_le
#print axioms ZkcSecurity.Families.Stark.outsidePoints
#print axioms ZkcSecurity.Families.Stark.mem_outsidePoints
#print axioms ZkcSecurity.Families.Stark.outsidePoints_card
#print axioms ZkcSecurity.Families.Stark.outsidePoints_nonempty_iff
#print axioms ZkcSecurity.Families.Stark.roots_on_set_uniform_le
#print axioms ZkcSecurity.Families.Stark.outside_agreement_uniform_le
#print axioms ZkcSecurity.Families.Stark.outside_error_lt_one
#print axioms ZkcSecurity.Families.Stark.interpolate_powerBatch
#print axioms ZkcSecurity.Families.Stark.deepQuotient_powerBatch
#print axioms ZkcSecurity.Families.Stark.deepBatch_degree_lt
#print axioms ZkcSecurity.Families.Stark.lift_agreement
#print axioms ZkcSecurity.Families.Stark.constraint_test_uniform_le

#print axioms Polynomial.prod_X_sub_C_dvd
#print axioms Polynomial.card_eval_zero_le_natDegree
#print axioms Polynomial.divByMonic_eq_div
#print axioms Lagrange.degree_interpolate_lt
#print axioms Lagrange.eq_interpolate_of_eval_eq
#print axioms MvPolynomial.schwartz_zippel_totalDegree
#print axioms ZkcSecurity.Algebra.Polynomial.root_uniform_le
#print axioms prEvent_bind_le_prEvent_add_of_support

run_cmd ZkcTools.DeclarationAudit.check [`ZkcSecurity.Families.Stark] "STARK-SECURITY-AXIOMS-PASS"
run_cmd ZkcTools.DeclarationAudit.checkBoundary [`ZkcSecurity.Families.Stark] [`Mathlib, `CompPoly, `VCVio, `ZkcSecurity.Algebra.Polynomial] [] "STARK-SECURITY-BOUNDARY-PASS"

-- Print, as well as check, every computed upstream root's transitive closure.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Std.HashSet Name := {}
  let upstream := [`Mathlib, `CompPoly, `VCVio, `ZkcSecurity.Algebra.Polynomial]
  for index in [:env.header.moduleData.size] do
    unless (`ZkcSecurity.Families.Stark).isPrefixOf env.header.modules[index]!.module do continue
    for info in env.header.moduleData[index]!.constants do
      let values := (info.value? true).map Expr.getUsedConstants |>.getD #[]
      for dependency in info.type.getUsedConstants ++ values do
        let some owner := ZkcTools.DeclarationAudit.moduleOf env dependency | continue
        if upstream.any (·.isPrefixOf owner) then roots := roots.insert dependency
  for root in roots.toArray.qsort Name.lt do
    elabCommand (← `(#print axioms $(mkIdent root)))
