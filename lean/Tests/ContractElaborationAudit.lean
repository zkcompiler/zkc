import Tests.ContractElaborationSources
import Tests.ContractElaborationControls
import ZkcTools.DeclarationAudit

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Source.Structured.ContractElaboration, `Tests.ContractElaborationSources,
      `Tests.ContractElaborationControls]
    "CONTRACT-ELABORATION-AUDIT-PASS" true
