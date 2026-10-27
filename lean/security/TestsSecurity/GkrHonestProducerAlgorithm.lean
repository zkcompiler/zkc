import ZkcSecurity.Realizations.Gkr.HonestProducerExecution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace TestsSecurity.GkrHonestProducerAlgorithm
open Zkc Source Structured Construction
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers
open ZkcSecurity.Realizations.Gkr

/-- Both operations occur in both layers; width one forces nonempty rounds. -/
def mixed : CircuitEncoding ℚ where
  inputs := List.replicate 2 2
  add := List.replicate 16 1
  mul := List.replicate 16 1
  layers := 2
  selector := 1
  width := 1

theorem replicate_decode {A : Type} (n : Nat) (value : A) :
    ofList? n (List.replicate (2 ^ n) value) = some (fun _ => value) := by
  simp only [ofList?, List.length_replicate, dite_true, List.getElem_replicate]
  congr 1

theorem inputs : mixed.circuit.inputs = fun _ => 2 := by
  change (ofList? 1 (List.replicate (2 ^ 1) (2 : ℚ))).getD 0 = _
  rw [replicate_decode]
  rfl

theorem add_zero : mixed.circuit.add 0 = fun _ => 1 := by
  change (ofList? 3 (List.replicate (2 ^ 3) (1 : ℚ))).getD 0 = _
  rw [replicate_decode]
  rfl

theorem add_one : mixed.circuit.add 1 = fun _ => 1 := by
  change (ofList? 3 (List.replicate (2 ^ 3) (1 : ℚ))).getD 0 = _
  rw [replicate_decode]
  rfl

theorem mul_zero : mixed.circuit.mul 0 = fun _ => 1 := add_zero

theorem mul_one : mixed.circuit.mul 1 = fun _ => 1 := add_one

theorem first_layer : mixed.circuit.wires 1 1 = fun _ => 32 := by
  funext gate
  simp only [ZkcSecurity.Families.Gkr.Circuit.wires, Protocols.Gkr.values, add_one, mul_one, inputs,
    Protocols.Gkr.layer, Protocols.Gkr.gates, Protocols.Gkr.sumTable, Protocols.Gkr.productTable,
    booleanSum, half]
  norm_num

theorem second_layer : mixed.circuit.wires 2 0 = fun _ => 4352 := by
  change Protocols.Gkr.layer (mixed.circuit.add 0) (mixed.circuit.mul 0) (mixed.circuit.wires 1 1) = _
  rw [first_layer, add_zero, mul_zero]
  funext gate
  norm_num [Protocols.Gkr.layer, Protocols.Gkr.gates, Protocols.Gkr.sumTable, Protocols.Gkr.productTable,
    booleanSum, half]

theorem shape : mixed.Shape := by norm_num [CircuitEncoding.Shape, mixed]

theorem admitted : mixed.Admitted 4 4 [4352, 4352] := by
  norm_num [CircuitEncoding.Admitted, CircuitEncoding.Shape, mixed]

theorem correct : mixed.Outputs [4352, 4352] := by
  refine ⟨shape, ?_⟩
  change ofList? 1 (List.replicate (2 ^ 1) (4352 : ℚ)) = some (mixed.circuit.wires 2 0)
  rw [replicate_decode, second_layer]
  rfl

/-- A changed output is excluded by independent target truth, not by an
assumption about a producer run. -/
theorem wrong_output : ¬ mixed.Outputs [4353, 4352] := by
  intro wrong
  have entry := ofList?_entry _ _ wrong.2 (0 : Fin 2)
  change [4353, 4352][0]? = some (mixed.circuit.wires 2 0 (vertex 1 (0 : Fin 2))) at entry
  rw [second_layer] at entry
  norm_num at entry

/-- Wrong shape is refused by the explicit honest input policy. -/
theorem wrong_shape : ¬ ({ mixed with inputs := [2] } : CircuitEncoding ℚ).Admitted 4 4 [4352, 4352] := by
  norm_num [CircuitEncoding.Admitted, CircuitEncoding.Shape, mixed]

/-- The full mixed circuit pair specializes to different scalar and group
carriers, retaining all histories and every possible challenge reply. -/
theorem mixed_pair_distinct_group (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (handle : Nat) (sites : HonestProducerObserved.Sites)
    (state : HonestProducerComposition.State (F := ℚ) (G := ℚ × ℚ))
    (outputRoutes : ∀ i, HonestProducer.OutputRoutes routing ctx
      (state.frames ++ [⟨sites.output, i⟩]) handle)
    (layerRoutes : ∀ i, HonestProducerObservedLayers.Routes routing ctx
      (state.frames ++ [⟨sites.layers, i⟩]) handle sites.layer) :
    ZkcSecurity.FiatShamir.Readback (fun left right => ∃ history,
      left = (.cons none .nil, { state with history := history }) ∧
      right = (some true, { state with history := history }))
      (Original.fold { routing with mode := .producer }
        (HonestProducerObserved.producer ctx sites mixed) state)
      (Original.fold { routing with mode := .validator }
        (HonestProducerObserved.validator ctx handle sites mixed [4352, 4352]) state) :=
  HonestProducerObserved.pair routing replacement profile ctx handle sites mixed [4352, 4352]
    correct state outputRoutes layerRoutes

/-- An invalid actual close refuses, preserving the actual stop. -/
theorem unmatched_frame (routing : Original.Routing) :
    Original.fold (carriers := uniformCarriers ℚ (ℚ × ℚ)) routing
      (.call (.leave ⟨"layer", 1⟩) .done) {} = .halt .refused := by rfl

/-- Corrupted coefficients stop in the same common verifier check. -/
theorem changed_coefficients :
    GkrVerifier.roundCheck (F := ℚ) (G := ℚ × ℚ) {} 0 ([], 1) 0 0 0 = .halt .reject := by
  norm_num [GkrVerifier.roundCheck]

#print axioms HonestProducerRounds.execute_yields
#print axioms HonestProducer.pair
#print axioms HonestProducerOccurrences.validatorRounds_prefix
#print axioms HonestProducerOccurrences.rounds
#print axioms HonestProducerObservedLayers.layer_pair
#print axioms HonestProducerObserved.pair
#print axioms HonestProducerExecution.producer_returns
#print axioms HonestProducerExecution.pair_returns
#print axioms HonestProducerOccurrences.producerRounds_prefix
#print axioms mixed_pair_distinct_group
#print axioms correct
#print axioms wrong_output
#print axioms changed_coefficients
#print axioms unmatched_frame

end TestsSecurity.GkrHonestProducerAlgorithm
