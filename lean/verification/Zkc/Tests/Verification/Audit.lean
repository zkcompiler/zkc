-- Maintained by audit_imports.py; legacy imports load private bodies.
import Zkc.Tests.Verification.LibraryImports
import Zkc.Tools.Program.DeclarationAudit

run_cmd do
  let env ← Lean.getEnv
  let families : List Lean.Name := [`Zkc.Verification, `Zkc.Tools.Verification, `Zkc.Tests.Verification]
  for imported in env.header.modules do
    if families.any (·.isPrefixOf imported.module) && !imported.importAll then
      throwError "audit requires private module data: {imported.module}"
  ZkcTools.DeclarationAudit.check families "VERIFICATION-AUDIT-PASS"
