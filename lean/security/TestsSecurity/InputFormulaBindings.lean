import ZkcSecurity.Tools.PairConstruction
import ZkcExamples.Structured.SumcheckContractBindings

set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
noncomputable section

namespace TestsSecurity.InputFormulaBindings
open Zkc.Source.Structured ZkcSecurity.Claims.HonestPair
open ZkcExamples.Structured.SumcheckContractBindings

/-- A genuinely present input clause exercises the data-producing branch of
the generic finite builder. Empty root input contracts alone would not do so. -/
def formulas : (index : Fin reductionOwner.contract.clauses.length) →
    (reductionOwner.clause index).kind = .input →
      FormulaClause ZkcExamples.Structured.SumcheckReduceViews.imported reductionOwner
        (reductionOwner.clause index).subject := by
  bind_input_formulas

example : (formulas ⟨0, by decide⟩ rfl).formula.original = reductionFormula.original := rfl

-- Metadata construction cannot discharge an arbitrary mathematical proposition.
example : True := by
  fail_if_success bind_input_formulas
  trivial

#print axioms formulas
end TestsSecurity.InputFormulaBindings
