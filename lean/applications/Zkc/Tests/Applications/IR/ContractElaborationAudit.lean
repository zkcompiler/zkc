import Zkc.Tests.Applications.IR.ContractElaborationSources
import Zkc.Tests.IR.ContractElaborationControls
import Zkc.Tools.Program.DeclarationAudit

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.IR.Source.Structured.ContractElaboration, `Zkc.Tests.Applications.IR.ContractElaborationSources, `Zkc.Tests.IR.ContractElaborationControls]
    "CONTRACT-ELABORATION-AUDIT-PASS" true
