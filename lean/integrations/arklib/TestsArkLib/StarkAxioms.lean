import ZkcArkLib.Stark.OutOfDomain
import ZkcArkLib.Stark.DeepBatching
import ZkcTools.DeclarationAudit

/-! Transitive receipts for the exact optional adapters and the proved
upstream roots they consume. General STIR combination is audited separately. -/

#print axioms ZkcArkLib.Stark.domainComplement_eq
#print axioms ZkcArkLib.Stark.list_collision_le
#print axioms ZkcArkLib.Stark.vanishing_eq
#print axioms ZkcArkLib.Stark.interpolate_eq
#print axioms ZkcArkLib.Stark.deepQuotient_eq
#print axioms ZkcArkLib.Stark.quotient_distance_gt
#print axioms ZkcArkLib.Stark.affine_jointAgreement
#print axioms ZkcArkLib.Stark.powerBatch_bad_implies_isMCA
#print axioms ZkcArkLib.Stark.powerBatch_distance_gt_of_not_isMCA
#print axioms ZkcArkLib.Stark.powerBatchError
#print axioms ZkcArkLib.Stark.powerBatch_distance_uniform_le
#print axioms ZkcArkLib.Stark.powerBatch_close_uniform_le
#print axioms ZkcArkLib.Stark.quotient_powerBatch_close_uniform_le

#print axioms OutOfDomSmpl.out_of_dom_smpl_1
#print axioms Quotienting.quotienting
#print axioms ProximityGap.RS_jointAgreement_of_goodCoeffs_card_gt
#print axioms ProximityGap.card_RS_goodCoeffs_gt_of_prob_gt_n_div_q
#print axioms CodingTheory.linear_mcaError_powers_le

run_cmd ZkcTools.DeclarationAudit.check [`ZkcArkLib.Stark] "STARK-ARKLIB-AXIOMS-PASS"
run_cmd ZkcTools.DeclarationAudit.checkBoundary [`ZkcArkLib.Stark] [`ArkLib] [] "STARK-ARKLIB-BOUNDARY-PASS"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Std.HashSet Name := {}
  for index in [:env.header.moduleData.size] do
    unless (`ZkcArkLib.Stark).isPrefixOf env.header.modules[index]!.module do continue
    for info in env.header.moduleData[index]!.constants do
      let values := (info.value? true).map Expr.getUsedConstants |>.getD #[]
      for dependency in info.type.getUsedConstants ++ values do
        let some owner := ZkcTools.DeclarationAudit.moduleOf env dependency | continue
        if (`ArkLib).isPrefixOf owner then roots := roots.insert dependency
  for root in roots.toArray.qsort Name.lt do
    elabCommand (← `(#print axioms $(mkIdent root)))
