import ZkcSecurity.Tools.PairConstruction
import ZkcExamples.Structured.SumcheckContractBindings

set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option smartUnfolding false
noncomputable section

namespace TestsSecurity.InputFormulaBindings
open Zkc.Source.Structured Zkc.Construction ZkcSecurity.Claims.HonestPair
open ZkcExamples.Structured.SumcheckContractBindings

/-- A genuinely present input clause exercises the data-producing branch of
the generic finite builder. Empty root input contracts alone would not do so. -/
def meanings : (index : Fin reductionOwner.contract.clauses.length) →
    (reductionOwner.clause index).kind = .input →
      RetainedClause ZkcExamples.Structured.SumcheckReduceViews.imported reductionOwner
        (reductionOwner.clause index).subject (assignment Int Int) OpaqueRegistry.empty := by
  bind_input_meanings

example : (match (meanings ⟨0, by decide⟩ rfl).meaning with
    | .formula binding => binding.original = reductionShapeFormula.original
    | .opaque _ => False) := rfl

-- Metadata construction cannot discharge an arbitrary mathematical proposition.
example : True := by
  fail_if_success bind_input_meanings
  trivial

#print axioms meanings
end TestsSecurity.InputFormulaBindings
