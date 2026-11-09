-- Maintained by audit_imports.py; legacy imports load private bodies.
import Zkc.Tests.Program.LibraryImports
import Zkc.Tools.Program.DeclarationAudit

run_cmd do
  let env ← Lean.getEnv
  let families : List Lean.Name := [`Zkc.Program, `Zkc.Tools.Program, `Zkc.Tests.Program]
  for imported in env.header.modules do
    if families.any (·.isPrefixOf imported.module) && !imported.importAll then
      throwError "audit requires private module data: {imported.module}"
  ZkcTools.DeclarationAudit.check families "PROGRAM-AUDIT-PASS"
