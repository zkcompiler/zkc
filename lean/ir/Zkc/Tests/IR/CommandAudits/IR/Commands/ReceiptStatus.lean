-- Maintained by audit_imports.py; legacy imports load private bodies.
import Zkc.Tools.IR.Commands.ReceiptStatus
import Zkc.Tools.Program.DeclarationAudit

run_cmd do
  let env ← Lean.getEnv
  let families : List Lean.Name := [`Zkc.Tools.IR.Commands.ReceiptStatus]
  for imported in env.header.modules do
    if families.any (·.isPrefixOf imported.module) && !imported.importAll then
      throwError "audit requires private module data: {imported.module}"
  ZkcTools.DeclarationAudit.check families "COMMAND-AUDIT-PASS"
