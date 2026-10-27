import ZkcSecurity.Realizations.Gkr.RootContract
import ZkcSecurity.Realizations.Gkr.ProducerHelpers
import TestsSecurity.GkrComponentContracts
import ZkcTools.DeclarationAudit

/-! This local audit covers all declarations owned by the new GKR modules,
including generated association proofs and private helpers. It does not edit
the package's global import or audit inventories. -/

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`ZkcSecurity.Families.Gkr, `ZkcSecurity.Realizations.Gkr,
      `TestsSecurity.GkrComponentContracts]
    "GKR-COMPONENTS-AUDIT-PASS"

#print axioms ZkcSecurity.Realizations.Gkr.Root.soundness
#print axioms ZkcSecurity.Realizations.Gkr.Source.soundness
#print axioms ZkcSecurity.Realizations.Gkr.Rounds.honest
#print axioms ZkcSecurity.Realizations.Gkr.Combination.honest
#print axioms ZkcSecurity.Realizations.Gkr.ProducerHelpers.producer_binding
