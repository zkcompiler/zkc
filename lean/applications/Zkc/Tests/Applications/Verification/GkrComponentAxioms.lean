import Zkc.Applications.Security.Gkr.SourceValidator
import Zkc.Applications.Security.Gkr.CanonicalReadback
import Zkc.Tests.Applications.Verification.GkrComponentContracts
import Zkc.Tools.Program.DeclarationAudit

/-! This local audit covers all declarations owned by the new GKR modules,
including generated association proofs and private helpers. It does not edit
the package's global import or audit inventories. -/

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Protocol.Library.Families.Gkr, `Zkc.Protocol.Bindings, `Zkc.Verification.Bindings.Gkr, `Zkc.Applications.Security.Gkr, `Zkc.Verification.Bindings.Source, `Zkc.Tests.Applications.Verification.GkrComponentContracts]
    "GKR-COMPONENTS-AUDIT-PASS"

#print axioms ZkcSecurity.Realizations.Gkr.SourceValidator.rejected
#print axioms ZkcSecurity.Realizations.Gkr.SourceValidator.costs
#print axioms ZkcSecurity.Realizations.Gkr.CanonicalReadback.actual
