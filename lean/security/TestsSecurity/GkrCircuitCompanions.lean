import ZkcSecurityExamples.Gkr.HonestCircuitSource

/-! Focused controls for the actual selected layer body and its complete
callback schema. These do not build a canonical GKR security root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace TestsSecurity.GkrCircuitCompanions
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws
open Zkc.Polynomial.Multilinear
open ZkcSecurity.Examples.Components
open ZkcSecurity.Realizations.Gkr.HonestCircuit

private abbrev model := ringModel ℚ ℚ
private def add : Zkc.Protocols.Gkr.Wiring ℚ 0 := fun _ => 2
private def mul : Zkc.Protocols.Gkr.Wiring ℚ 0 := fun _ => 1
private def below : Table ℚ 0 := fun _ => 3

/-- A scalar layer exercises both independent addition and multiplication. -/
theorem actual_layer :
    invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper33Helper
      (Goals.LayerArguments.pack { addWeights := [2], mulWeights := [1], below := [3], width := 0 }) =
      .done (Goals.Layer.encode model ⟨[21]⟩) := by
  have actual := layer_encoded (G := ℚ) add mul below (by decide +kernel)
  norm_num [add, mul, below, GkrRoundsLayout.encode, Zkc.Protocols.Gkr.layer,
    Zkc.Protocols.Gkr.gates, Zkc.Protocols.Gkr.sumTable, Zkc.Protocols.Gkr.productTable,
    booleanSum, Zkc.Protocols.AlgebraicRounds.Gate.value, vertex] at actual ⊢
  exact actual

/-- The actual callback keeps its initial prefix and all five captures. -/
theorem complete_callback :
    Goals.Step.body.denote (meaning ℚ ℚ (helpers (F := ℚ) (G := ℚ)))
      (Goals.StepArguments.pack
        { position := 0, values := [7, 11], addWeights := [2], mulWeights := [1],
          width := 0, left := [3], right := [3] }).get =
      .done (Goals.Step.encode model
        { values := [7, 11, 21], addWeights := [2], mulWeights := [1], width := 0,
          left := [3], right := [3] }) := by
  have actual := layer_step_encodes (G := ℚ) add mul below [7, 11] ⟨0, by decide⟩ (by decide +kernel)
  norm_num [add, mul, below, GkrRoundsLayout.encode, GkrRoundsLayout.replicate,
    GkrRoundsLayout.tile, Zkc.Protocols.Gkr.layer, Zkc.Protocols.Gkr.gates,
    Zkc.Protocols.Gkr.sumTable, Zkc.Protocols.Gkr.productTable,
    booleanSum, Zkc.Protocols.AlgebraicRounds.Gate.value, vertex] at actual ⊢
  exact actual

/-- Equal carrier types do not make source coordinates interchangeable. -/
example : Goals.LayerArguments.pack (Value := assignment ℚ ℚ)
    { addWeights := [2], mulWeights := [1], below := [3], width := 0 } ≠
    Goals.LayerArguments.pack
      { addWeights := [1], mulWeights := [2], below := [3], width := 0 } := by
  intro same
  have weights := congrArg (fun row => (Goals.LayerArguments.unpack row).addWeights) same
  norm_num [Goals.LayerArguments.unpack_pack] at weights

private def changedLayer : CheckedDefinition :=
  .ofBody GkrSourceBodies.helper33Helper (.stop .abort)

/-- An unchanged name and signature do not associate a different actual body. -/
theorem changed_body_refused :
    ¬ BodyIn [changedLayer] GkrSourceBodies.helper33Helper Goals.Layer.body := by
  rintro ⟨selected, member, signature, same⟩
  simp only [List.mem_singleton] at member
  subst selected
  change RawRegion.stop PIR.Stop.abort = RawRegion.letOp _ _ _ _ _ at same
  cases same

/-- The complete source-generated equation retains the original early guard. -/
theorem boundary_refused :
    invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper34Helper
      (Goals.ValuesArguments.pack
        { addWeights := [], mulWeights := [], inputValues := [], layers := 2,
          selector := 1, width := 1, layerIndex := 2 }) = .halt .refused := by
  rw [circuit_bodies.values.invoke GkrSourceViews.unit.linked]
  simp only [meaning]
  rw [Evaluation.denote_meaning_eq_meaningOn, Goals.valuesProcess_equation]
  dsimp only [Goals.valuesProcess, Goals.valuesProcess_certificate]
  norm_num [Primitive.evaluateOn, primitiveOutcome, checkedIndices, indexLimit,
    PIR.Process.bind, SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    Environment.prepend, Environment.push, Values.get_head, Values.get_tail, Values.get]

/-- Changing a dependency's actual implementation invalidates the installed
mathematical premises, even though all source signatures are unchanged. -/
theorem missing_dependencies : ¬ Companion.Dependencies ([] : Meanings ℚ ℚ) := by
  intro dependencies
  have impossible := dependencies.power 0 (by decide +kernel)
  cases impossible

#print axioms Goals.Step.equation
#print axioms Goals.Layer.equation
#print axioms Companion.step
#print axioms Companion.layer
#print axioms dependencies
#print axioms actual_layer
#print axioms complete_callback
#print axioms boundary_refused
#print axioms changed_body_refused
#print axioms missing_dependencies
end TestsSecurity.GkrCircuitCompanions
