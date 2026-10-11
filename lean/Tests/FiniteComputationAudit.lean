import Tests.FiniteComputation
import Tools.DeclarationAudit

/-! Audit the imported model and controls, including generated declarations. -/

run_cmd
  Tools.DeclarationAudit.check [`Zkc.Semantics.FiniteComputation, `Tests.FiniteComputation]
    "FINITE-COMPUTATION-AUDIT-PASS"

#print axioms Zkc.FiniteComputation.Local.materialize_total_step
#print axioms Zkc.FiniteComputation.Domain.zip_ok
#print axioms Zkc.FiniteComputation.matrix_contraction
