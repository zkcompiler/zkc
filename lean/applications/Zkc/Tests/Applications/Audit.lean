-- Maintained by audit_imports.py; legacy imports load private bodies.
import Zkc.Tests.Applications.LibraryImports
import Zkc.Tools.Program.DeclarationAudit
import Zkc.Tests.Program.LibraryImports
import Zkc.Tests.IR.LibraryImports
import Zkc.Tests.Protocol.LibraryImports
import Zkc.Tests.Verification.LibraryImports
import Zkc.Tests.ArkLib.LibraryImports
import Zkc.Tests.Clean.LibraryImports

run_cmd do
  let env ← Lean.getEnv
  let families : List Lean.Name := [`Zkc.Applications, `Zkc.Tests.Applications]
  for imported in env.header.modules do
    if families.any (·.isPrefixOf imported.module) && !imported.importAll then
      throwError "audit requires private module data: {imported.module}"
  ZkcTools.DeclarationAudit.check families "APPLICATIONS-AUDIT-PASS"

run_cmd ZkcTools.DeclarationAudit.checkRegistry ZkcSecurity.Registry.audited [`Zkc.Applications.Security, `Zkc.Protocol.Bindings, `Zkc.Protocol.Library.Families, `Zkc.Protocol.Library.Mathematics, `Zkc.Protocol.Library.Security, `Zkc.Protocol.Library.Transformations, `Zkc.Protocol.Logic, `Zkc.Tools.IR.SourceProperties, `Zkc.Tools.IR.TableCapacity, `Zkc.Tools.Protocol, `Zkc.Tools.Verification.Bindings, `Zkc.Tools.Verification.ClaimConstruction, `Zkc.Tools.Verification.ComponentAuthoringReport, `Zkc.Tools.Verification.ComponentBridge, `Zkc.Tools.Verification.ComponentDerivation, `Zkc.Tools.Verification.ComponentReadback, `Zkc.Tools.Verification.ComponentView, `Zkc.Tools.Verification.Components, `Zkc.Tools.Verification.Generation, `Zkc.Tools.Verification.InputLaws, `Zkc.Tools.Verification.PairConstruction, `Zkc.Tools.Verification.SigmaReadback, `Zkc.Tools.Verification.SourceInputClauses, `Zkc.Tools.Verification.SourceInputReadback, `Zkc.Tools.Verification.SourceProperties, `Zkc.Tools.Verification.SubjectABI, `Zkc.Tools.Verification.Sumcheck, `Zkc.Tools.Verification.TargetEvaluation, `Zkc.Verification.Bindings, `Zkc.Verification.Claims, `Zkc.Verification.Families, `Zkc.Verification.Mathematics, `Zkc.Verification.ProgramLogic, `Zkc.Verification.Transformations] "REGISTRY-AUDIT-PASS"
run_cmd ZkcTools.DeclarationAudit.checkRegistry (ZkcSecurity.Registry.audited ++ ZkcArkLib.Registry.audited) [`Zkc.Adapters.ArkLib, `Zkc.Applications.ArkLib] "ARKLIB-REGISTRY-AUDIT-PASS"
