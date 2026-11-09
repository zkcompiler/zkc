import Zkc.Tests.Verification.LocalCouplingClients
import Zkc.Tools.Program.DeclarationAudit

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Protocol.Library.Mathematics.Oracle.Coupling, `Zkc.Tests.Verification.LocalCoupling, `Zkc.Tests.Verification.LocalCouplingClients] "LOCAL-COUPLING-AUDIT-PASS" (exactModules := true)
