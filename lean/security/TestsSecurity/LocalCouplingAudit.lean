import TestsSecurity.LocalCouplingClients
import ZkcTools.DeclarationAudit

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`ZkcSecurity.Mathematics.Oracle.Coupling, `TestsSecurity.LocalCoupling,
     `TestsSecurity.LocalCouplingClients] "LOCAL-COUPLING-AUDIT-PASS" (exactModules := true)
