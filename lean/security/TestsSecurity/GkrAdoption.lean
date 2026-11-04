import TestsSecurity.GkrCollectionCompanions
import TestsSecurity.GkrReadbackCompanions
import TestsSecurity.GkrCircuitCompanions
import TestsSecurity.GkrLineCompanions
import ZkcTools.StructuredSource.NamedEquations

/-! Canonical-law adoption controls, including the actual installed gate map.
The imported controls retain collection zero loops, readback overflow/defaults,
complete nested captures, changed-body refusals and optional component custody. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TestsSecurity.GkrAdoption
open Zkc Source Structured ZkcExamples.Structured
open ZkcSecurity.Realizations.Gkr
attribute [local implicit_reducible] Op.arguments Op.results Op.regions

private abbrev model := ringModel ℚ ℚ

/-- The actual installed map retains every ordered shape failure and every
successful result, for arbitrary raw vectors rather than only encoded tables. -/
theorem gate_map_all_outcomes (add mul left right : List ℚ) :
    invoke (GkrSourceLaws.helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper57Helper
      (GkrGateGoals.Map.Inputs.pack
        { addWeights := add, mulWeights := mul, lefts := left, rights := right }) =
      primitiveOutcome (GkrGateGoals.Map.encodeOutcome model
        (GkrGateCompanion.mapReference model add mul left right)) := by
  rw [(GkrGateCompanion.mapLaw model).invokeUniform
    (F := ℚ) (G := ℚ) (helper := GkrSourceBodies.helper57Helper)
    GkrSourceViews.unit.definitions GkrSourceViews.unit.linked HonestCircuit.gate_bodies.map]
  · rw [GkrGateCompanion.map_reference]
  · exact HonestCircuit.gate_map_dependencies add mul left right

example : invoke (GkrSourceLaws.helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper57Helper
    (GkrGateGoals.Map.Inputs.pack
      { addWeights := [], mulWeights := [], lefts := [], rights := [] }) =
      .done (GkrGateGoals.Map.encode model ⟨[]⟩) := by
  rw [gate_map_all_outcomes]
  rfl

example : invoke (GkrSourceLaws.helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper57Helper
    (GkrGateGoals.Map.Inputs.pack
      { addWeights := [1, 2], mulWeights := [3], lefts := [4, 5], rights := [6, 7] }) =
      .halt .refused := by
  rw [gate_map_all_outcomes]
  rfl

/-- Installation cannot replace a missing actual body with its dependency law. -/
example : ¬ GkrGateGoals.Bodies [] := by
  intro bodies
  obtain ⟨definition, member, _, _⟩ := bodies.value
  cases member

/-- The canonical laws themselves still name the complete admitted bodies. -/
example (model : DomainModel) :
    (GkrGateCompanion.callbackLaw model).body = GkrGateGoals.Callback.body := rfl

example (model : DomainModel) :
    (HonestHelpers.ReadbackCompanion.wrapperLaw model).body =
      HonestHelpers.ReadbackGoals.ScanWrapper.body := rfl

/-- Both transported callbacks are selected from their complete actual helpers. -/
theorem layer_callback_selected :
    HelperCallbacks.Selected HonestCircuit.Goals.Layer.body none
      HonestCircuit.Goals.layerCallback_selection :=
  HonestCircuit.Goals.layerCallback_association

theorem traversal_callback_selected :
    HelperCallbacks.Selected HonestCircuit.Goals.Traversal.body none
      HonestCircuit.Goals.traversalCallback_selection :=
  HonestCircuit.Goals.traversalCallback_association

/-- Placement retains subtraction refusal outside the honest traversal invariant,
before any dependency is invoked, for arbitrary raw vectors and other captures. -/
theorem traversal_zero_refused (iteration selector width : Nat)
    (values add mul : List ℚ) :
    HonestCircuit.Goals.TraversalStep.body.denote (meaning ℚ ℚ [])
      (HonestCircuit.Goals.TraversalStepArguments.pack
        { iteration, values, current := 0, addWeights := add, mulWeights := mul,
          selector, width }).get = .halt .refused := by
  dsimp only [HonestCircuit.Goals.TraversalStepArguments.pack]
  named_process HonestCircuit.Goals.traversalStepProcess over ℚ ℚ
  norm_num [Primitive.evaluateOn, primitiveOutcome, checkedIndices, indexLimit,
    PIR.Process.bind, SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get]

#print axioms gate_map_all_outcomes
#print axioms GkrGateCompanion.installScalars
#print axioms HonestLine.Companion.installScalars
#print axioms HonestHelpers.ReadbackCompanion.install
#print axioms HonestHelpers.CollectionCompanion.install

run_elab do
  for declaration in [``gate_map_all_outcomes, ``GkrGateCompanion.installScalars,
      ``HonestLine.Companion.installScalars, ``HonestHelpers.ReadbackCompanion.install,
      ``HonestHelpers.CollectionCompanion.install, ``HonestCircuit.Companion.step,
      ``HonestCircuit.Companion.layer, ``HonestCircuit.values_below,
      ``HonestCircuit.Companion.layer_encoded_body, ``HonestCircuit.values_step,
      ``layer_callback_selected, ``traversal_callback_selected, ``traversal_zero_refused,
      ``Evaluation.denoteLoopOn_callback_eq, ``Evaluation.denoteLoopOn_states_of_equation,
      ``TestsSecurity.GkrCollectionCompanions.variant_actual,
      ``TestsSecurity.GkrReadbackCompanions.variant_actual] do
    for dependency in ← Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "nonstandard axiom in an adopted GKR law: {declaration}: {dependency}"
end TestsSecurity.GkrAdoption
