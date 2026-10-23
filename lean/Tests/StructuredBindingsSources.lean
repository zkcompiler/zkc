import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckSumcheck
import ZkcExamples.Structured.Generated.Bindings.TwoSumsSumcheck
import ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate

/-! Structural mutations of the actual admitted sources. These transformations
only change existing typed Region data; they introduce no execution language. -/

namespace Tests.StructuredBindingsSources
open Zkc.Source Zkc.Source.Structured
open Zkc.Source.Structured.NormalForm
open ZkcExamples.Structured.Generated.Bindings

mutual
  def dropGuards {inputs outputs : List Ty} : Region protocolDialect inputs outputs →
      Region protocolDialect inputs outputs
    | .ret values => .ret values
    | .stop reason => .stop reason
    | .bind body next => .bind (dropGuards body) (dropGuards next)
    | .letOp (.guard _ _) _ .nil next => dropGuards next
    | .letOp op args bodies next => .letOp op args (dropGuardsRegions bodies) (dropGuards next)
  def dropGuardsRegions {signatures : List (List Ty × List Ty)} :
      Regions protocolDialect signatures → Regions protocolDialect signatures
    | .nil => .nil
    | .cons body rest => .cons (dropGuards body) (dropGuardsRegions rest)
end

def swapPrivate {inputs : List Ty} {field : String} {rest : List Ty} :
    Region protocolDialect inputs (.vector field :: .vector field :: rest) →
      Region protocolDialect inputs (.vector field :: .vector field :: rest)
  | .ret (.cons first (.cons second rest)) => .ret (.cons second (.cons first rest))
  | .stop reason => .stop reason
  | .bind body next => .bind body (swapPrivate next)
  | .letOp op args bodies next => .letOp op args bodies (swapPrivate next)

/-- A syntactic diagnostic for the final ABI operands, without evaluation. -/
def terminalPositions {Ty Op : Type} : RawRegion Ty Op → List Nat
  | .ret positions => positions
  | .stop _ => []
  | .letOp _ _ _ _ next => terminalPositions next
  | .bind _ _ next => terminalPositions next

def changedAppend : Region dialect SmallSumcheckInputs.helper19Helper.inputs
    SmallSumcheckInputs.helper19Helper.outputs := .ret (.cons .here .nil)

theorem same_name_changed_body :
    SmallSumcheckInputs.helper19Helper = ZkcExamples.Structured.SumcheckHelperBodies.appendHelper ∧
    changedAppend.erase ≠ SmallSumcheckInputs.helper19Body.erase := by
  constructor
  · rfl
  · intro same
    cases same

theorem actual_guard_removed :
    (dropGuards SmallSumcheckCallbacks.protocol0Role1Callback0Body).erase ≠
      SmallSumcheckCallbacks.protocol0Role1Callback0Body.erase := by
  intro same
  cases same

theorem actual_private_return_changed :
    (swapPrivate TwoSums.definition0.body).erase ≠ TwoSums.definition0.body.erase := by
  intro same
  have distinct : terminalPositions (swapPrivate TwoSums.definition0.body).erase ≠
      terminalPositions TwoSums.definition0.body.erase := by decide +kernel
  exact distinct (congrArg terminalPositions same)

theorem actual_operand_order :
    Zkc.Protocols.AlgebraicRounds.Gate.value (1 : ℚ) 2 3 4 ≠
      Zkc.Protocols.AlgebraicRounds.Gate.value (2 : ℚ) 1 3 4 := by
  decide +kernel

-- All four wrong structural certificates are separately rejected by the
-- Python orchestration check, which verifies actual kernel-rfl failures.
#print axioms SmallSumcheck.protocol0Role1_certificate
#print axioms TwoSums.protocol1Role1_certificate
#print axioms GkrRounds.protocol0Role1_certificate
end Tests.StructuredBindingsSources
