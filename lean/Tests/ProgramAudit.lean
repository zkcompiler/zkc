-- Maintained by audit_imports.py; legacy imports load full private module data.
import ZkcProgram
import ZkcProgram.Execution
import ZkcProgram.Interaction
import ZkcProgram.Interpretation
import ZkcProgram.MonadExecution
import ZkcProgram.Region.Basic
import ZkcProgram.Region.Context
import ZkcProgram.Region.Operations
import ZkcTools.DeclarationAudit

run_cmd do
  let env ← Lean.getEnv
  for imported in env.header.modules do
    if (`ZkcProgram).isPrefixOf imported.module && !imported.importAll then
      throwError "shared program audit requires private module data: {imported.module}"
  ZkcTools.DeclarationAudit.check [`ZkcProgram] "PROGRAM-AUDIT-PASS"
