import ZkcSecurityExamples.Gkr.HonestCircuitValues

/-! Narrow controls for the source-selected backward traversal, including its
complete callback output, strict indices and every dependency stop reason. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TestsSecurity.GkrTraversalCompanions
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.Examples.Components
open ZkcSecurity.Realizations.Gkr.HonestCircuit

private abbrev model := ringModel ℚ ℚ
private def circuit : ZkcSecurity.Families.Gkr.Circuit ℚ 0 :=
  ⟨fun _ => 3, fun _ _ => 2, fun _ _ => 1⟩

private theorem add_encoding : StackedEncoding [2, 91, 92, 93] 1 2 circuit.add := by
  refine ⟨by decide, ?_⟩
  intro position inside
  have : position = 0 := by omega
  subst position
  change ofList? 0 [2] = some (circuit.add 0)
  have encoded : GkrRoundsLayout.encode (circuit.add 0) = [2] := by
    norm_num [circuit, GkrRoundsLayout.encode]
  rw [← encoded, GkrRoundsLayout.decode_encode]

private theorem mul_encoding : StackedEncoding [1, 81, 82, 83] 1 2 circuit.mul := by
  refine ⟨by decide, ?_⟩
  intro position inside
  have : position = 0 := by omega
  subst position
  change ofList? 0 [1] = some (circuit.mul 0)
  have encoded : GkrRoundsLayout.encode (circuit.mul 0) = [1] := by
    norm_num [circuit, GkrRoundsLayout.encode]
  rw [← encoded, GkrRoundsLayout.decode_encode]

example : HelperCallbacks.Selected GkrSourceBodies.helper34Body none Goals.traversalCallback_selection :=
  Goals.traversalCallback_association

/-- The actual step decrements the backward index and keeps all four captures,
including distinct selector/width coordinates and inactive padding blocks. -/
theorem complete_callback :
    Goals.TraversalStep.body.denote (meaning ℚ ℚ (helpers (F := ℚ) (G := ℚ)))
      (Goals.TraversalStepArguments.pack
        { iteration := 0, values := [3], current := 1, addWeights := [2, 91, 92, 93],
          mulWeights := [1, 81, 82, 83], selector := 2, width := 0 }).get =
      .done (Goals.TraversalStep.encode model
        { values := [21], current := 0, addWeights := [2, 91, 92, 93],
          mulWeights := [1, 81, 82, 83], selector := 2, width := 0 }) := by
  have actual := values_step (G := ℚ) [2, 91, 92, 93] [1, 81, 82, 83] 1 2 circuit
    add_encoding mul_encoding (by decide) (by decide) (by decide +kernel) 0 (by decide)
  norm_num [circuit, ZkcSecurity.Families.Gkr.Circuit.wires, Zkc.Protocols.Gkr.values,
    Zkc.Protocols.Gkr.layer, Zkc.Protocols.Gkr.gates, Zkc.Protocols.Gkr.sumTable,
    Zkc.Protocols.Gkr.productTable, Zkc.Protocols.AlgebraicRounds.Gate.value,
    booleanSum, GkrRoundsLayout.encode, vertex] at actual ⊢
  exact actual

theorem wrong_capture_rejected :
    Goals.TraversalStep.body.denote (meaning ℚ ℚ (helpers (F := ℚ) (G := ℚ)))
      (Goals.TraversalStepArguments.pack
        { iteration := 0, values := [3], current := 1, addWeights := [2, 91, 92, 93],
          mulWeights := [1, 81, 82, 83], selector := 2, width := 0 }).get ≠
      .done (Goals.TraversalStep.encode model
        { values := [21], current := 0, addWeights := [1, 81, 82, 83],
          mulWeights := [2, 91, 92, 93], selector := 2, width := 0 }) := by
  rw [complete_callback]
  intro wrong
  have captures := congrArg (fun row => (Goals.TraversalStep.decode model row).addWeights)
    (PIR.Process.done.inj wrong)
  norm_num [Goals.TraversalStep.decode_encode] at captures

private def changedCallback : Region dialect Goals.TraversalStepArguments.types
    (Goals.TraversalState.types ++ Goals.TraversalCaptures.types) := .stop .abort

theorem changed_callback_rejected : changedCallback ≠ Goals.TraversalStep.body := by
  intro same
  have actual := complete_callback
  rw [← same] at actual
  cases actual

/-- Both outer subtractions and the reached callback decrement retain refusal,
even when no helper implementation or well-formed wiring is supplied. -/
example (table : Evaluation.MeaningsOn model.toCarriers closedInterface) :
    Goals.Traversal.run model table [] [] [] 2 1 1 3 = .halt .refused := by rfl

example (table : Evaluation.MeaningsOn model.toCarriers closedInterface) :
    Goals.Traversal.run model table [] [] [] 2 1 1 2 = .halt .refused := by rfl

example (table : Evaluation.MeaningsOn model.toCarriers closedInterface) :
    Goals.TraversalStep.run model table 77 [] 0 [] [] 9 13 = .halt .refused := by rfl

example (table : Evaluation.MeaningsOn model.toCarriers closedInterface) :
    Goals.Traversal.run model table [] [] [] indexLimit 1 1 0 = .halt .refused := by rfl

example (table : Evaluation.MeaningsOn model.toCarriers closedInterface) :
    Goals.Traversal.run model table [] [] [] 2 1 1 indexLimit = .halt .refused := by rfl

example (table : Evaluation.MeaningsOn model.toCarriers closedInterface) :
    Goals.TraversalStep.run model table 0 [] indexLimit [] [] 1 1 = .halt .refused := by rfl

/-- An empty traversal returns the exact input vector without a callback. -/
example (table : Evaluation.MeaningsOn model.toCarriers closedInterface) :
    Goals.Traversal.run model table [] [] [7, 11] 2 3 5 1 =
      .done (⟨[7, 11]⟩ : Goals.Traversal.Output model) := by rfl

private def stoppingBlock (reason : PIR.Stop) : Evaluation.MeaningsOn model.toCarriers closedInterface :=
  [⟨GkrSourceBodies.selectBlockHelper, fun _ => .halt reason⟩]

private def stoppingSecondBlock (reason : PIR.Stop) : Evaluation.MeaningsOn model.toCarriers closedInterface :=
  [⟨GkrSourceBodies.selectBlockHelper, fun arguments =>
    if (Goals.BlockArguments.unpack arguments).source.isEmpty then .halt reason
    else .done (Goals.BlockResult.pack ⟨[2]⟩)⟩]

private def stoppingLayer (reason : PIR.Stop) : Evaluation.MeaningsOn model.toCarriers closedInterface :=
  [⟨GkrSourceBodies.selectBlockHelper, fun _ => .done (Goals.BlockResult.pack ⟨[2]⟩)⟩,
   ⟨GkrSourceBodies.helper33Helper, fun _ => .halt reason⟩]

example (reason : PIR.Stop) :
    Goals.TraversalStep.run model (stoppingBlock reason) 0 [3] 1 [2] [1] 0 0 = .halt reason := by rfl

example (reason : PIR.Stop) :
    Goals.TraversalStep.run model (stoppingSecondBlock reason) 0 [3] 1 [2] [] 0 0 = .halt reason := by rfl

example (reason : PIR.Stop) :
    Goals.TraversalStep.run model (stoppingLayer reason) 0 [3] 1 [2] [1] 0 0 = .halt reason := by rfl

example (reason : PIR.Stop) :
    Goals.Traversal.run model (stoppingBlock reason) [] [] [3] 2 0 0 0 = .halt reason := by rfl

#print axioms Goals.traversalCallback_association
#print axioms Goals.TraversalStep.equation
#print axioms Goals.traversalStepProcess_equation
#print axioms Goals.valuesProcess_equation
#print axioms values_step
#print axioms values_below
#print axioms complete_callback
#print axioms wrong_capture_rejected
#print axioms changed_callback_rejected
end TestsSecurity.GkrTraversalCompanions
