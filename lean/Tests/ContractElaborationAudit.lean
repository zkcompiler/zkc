import Tests.ContractElaborationSources
import Tests.ContractElaborationControls
import ZkcTools.DeclarationAudit

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Source.Structured.ContractElaboration, `Tests.ContractElaborationSources,
      `Tests.ContractElaborationControls]
    "CONTRACT-ELABORATION-AUDIT-PASS" true

#print axioms Zkc.Source.Structured.ContractElaboration.uniqueIndex?_sound
#print axioms Tests.ContractElaborationSources.Schnorr.formula_law
#print axioms Tests.ContractElaborationSources.Sumcheck.formula_eq
#print axioms Tests.ContractElaborationSources.Sumcheck.reduction_formula_eq
#print axioms Tests.ContractElaborationControls.formula_adequate
#print axioms Tests.ContractElaborationControls.changed_rejects_old_law
