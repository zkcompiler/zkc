import ZkcSecurity.Realizations.Gkr.SourceValidator
import ZkcSecurity.Realizations.Gkr.CanonicalReadback
import ZkcSecurity.Realizations.Gkr.ProducerHelpers
import TestsSecurity.GkrComponentContracts
import ZkcTools.DeclarationAudit

/-! This local audit covers all declarations owned by the new GKR modules,
including generated association proofs and private helpers. It does not edit
the package's global import or audit inventories. -/

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`ZkcSecurity.Families.Gkr, `ZkcSecurity.Realizations.Gkr,
      `ZkcSecurity.Source, `TestsSecurity.GkrComponentContracts]
    "GKR-COMPONENTS-AUDIT-PASS"

#print axioms ZkcSecurity.Realizations.Gkr.SourceValidator.rejected
#print axioms ZkcSecurity.Realizations.Gkr.SourceValidator.costs
#print axioms ZkcSecurity.Realizations.Gkr.CanonicalReadback.actual
#print axioms ZkcSecurity.Realizations.Gkr.ProducerHelpers.producer_binding
