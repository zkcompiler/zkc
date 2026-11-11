-- Maintained by audit_imports.py; legacy imports load private bodies.
import Zkc.Tests.Verification.LibraryImports
import Zkc.Tests.Program.LibraryImports
import Zkc.Tests.IR.LibraryImports
import Zkc.Tests.Protocol.LibraryImports
import Zkc.Tools.Program.DeclarationAudit

run_cmd do
  let env ← Lean.getEnv
  let families : List Lean.Name := [`Zkc.Verification, `Zkc.Tools.Verification, `Zkc.Tests.Verification]
  for imported in env.header.modules do
    if families.any (·.isPrefixOf imported.module) && !imported.importAll then
      throwError "audit requires private module data: {imported.module}"
  ZkcTools.DeclarationAudit.check families "VERIFICATION-AUDIT-PASS"

run_cmd ZkcTools.DeclarationAudit.checkRegistry ZkcSecurity.Registry.audited [`Zkc.Protocol.Bindings, `Zkc.Protocol.Library.Families, `Zkc.Protocol.Library.Mathematics, `Zkc.Protocol.Library.Security, `Zkc.Protocol.Library.Transformations, `Zkc.Protocol.Logic, `Zkc.Tools.IR.SourceProperties, `Zkc.Tools.IR.TableCapacity, `Zkc.Tools.Protocol, `Zkc.Verification.Bindings, `Zkc.Verification.Claims, `Zkc.Verification.Families, `Zkc.Verification.ProgramLogic] "REGISTRY-AUDIT-PASS"
