-- Maintained by audit_imports.py; legacy imports load private bodies.
import Zkc.Tests.Protocol.LibraryImports
import Zkc.Tools.Program.DeclarationAudit

run_cmd do
  let env ← Lean.getEnv
  let families : List Lean.Name := [`Zkc.Protocol, `Zkc.Tools.Protocol, `Zkc.Tests.Protocol]
  for imported in env.header.modules do
    if families.any (·.isPrefixOf imported.module) && !imported.importAll then
      throwError "audit requires private module data: {imported.module}"
  ZkcTools.DeclarationAudit.check families "PROTOCOL-AUDIT-PASS"
