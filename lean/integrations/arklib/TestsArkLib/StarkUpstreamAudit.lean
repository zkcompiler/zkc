import ArkLib.ProofSystem.Stir.OutOfDomSmpl
import ArkLib.ProofSystem.Stir.Quotienting
import ArkLib.ProofSystem.Stir.Combine
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Powers
import ZkcSecurity.Mathematics.Algebra.Polynomial
import ZkcTools.DeclarationAudit

/-! Transitive dependency audit of the pinned STIR reuse candidates. The general
combination theorem is inspected here, not used as an established result. -/

#print axioms OutOfDomSmpl.single_coord_bound
#print axioms OutOfDomSmpl.pair_agree_bound
#print axioms OutOfDomSmpl.out_of_dom_smpl_1
#print axioms OutOfDomSmpl.out_of_dom_smpl_2
#print axioms Quotienting.degree_polyQuotient_lt
#print axioms Quotienting.vanishingPoly_mul_polyQuotient
#print axioms Quotienting.quotienting
#print axioms Combine.combine_theorem
#print axioms ProximityGap.correlatedAgreement_affine_curves
#print axioms Combine.master_lemma
#print axioms Combine.combine_eq_cases
#print axioms Combine.degreeCor_eq
#print axioms ProximityGap.RS_jointAgreement_of_goodCoeffs_card_gt
#print axioms ProximityGap.card_RS_goodCoeffs_gt_of_prob_gt_n_div_q
#print axioms ProximityGap.large_agreement_set_on_line_implies_correlated_agreement
#print axioms Polynomial.card_eval_zero_le_natDegree
#print axioms Lagrange.degree_interpolate_lt
#print axioms ZkcSecurity.Algebra.Polynomial.root_uniform_le

-- This capacity-bound route is independent of the admitted BCIKS20 curve root.
#print axioms CodingTheory.linear_mcaError_powers_le
#print axioms CoreDefinitions.mcaError
#print axioms CoreDefinitions.not_isMCA_univariatePowersGenerator_iff
run_cmd (ZkcTools.DeclarationAudit.checkBoundary [] []
  [`CodingTheory.linear_mcaError_powers_le, `CoreDefinitions.mcaError,
    `CoreDefinitions.not_isMCA_univariatePowersGenerator_iff]
  "STARK-POWER-UPSTREAM-AXIOMS-PASS")

open Lean Elab Command in
run_cmd do
  for root in [`Combine.combine_theorem, `ProximityGap.correlatedAgreement_affine_curves] do
    unless (← Lean.collectAxioms root).contains ``sorryAx do
      throwError "excluded combination root changed axiom status: {root}"
  logInfo "STARK-EXCLUDED-COMBINATION-CONTROL-PASS"
