import Tests.CommittedSumcheck
import Tests.PolynomialLayout
import Tools.DeclarationAudit

run_cmd Tools.DeclarationAudit.check [`Zkc.Polynomial.Layout, `Zkc.Protocols.Sumcheck.Committed,
   `Tests.CommittedSumcheck, `Tests.PolynomialLayout] "COMMITTED-AUDIT-PASS"
