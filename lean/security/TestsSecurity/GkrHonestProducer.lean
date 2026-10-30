import ZkcSecurityExamples.Gkr.CanonicalReadback
import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
import Zkc.Protocols.Gkr.Source.VerifierProcess

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace TestsSecurity.GkrHonestProducer
open Zkc Source Structured Construction
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers
open ZkcSecurity.Realizations.Gkr
open ZkcSecurity.FiatShamir HonestProducerSource
open OracleComp OracleSpec

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

/-- The actual source helper computes the mixed arithmetic layer. -/
theorem actual_layer :
    invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).closed
      GkrSourceBodies.helper33Helper
      (.cons (List.replicate 8 1) (.cons (List.replicate 8 1) (.cons [2, 2] (.cons 1 .nil)))) =
        .done (.cons [32, 32] .nil) := by
  have decodedWiring : ofList? 3 (List.replicate 8 (1 : ℚ)) = some (fun _ => 1) := replicate_decode 3 1
  have decodedInputs : ofList? 1 ([2, 2] : List ℚ) = some (fun _ => 2) := by
    simpa only [show List.replicate (2 ^ 1) (2 : ℚ) = [2, 2] from rfl] using replicate_decode 1 (2 : ℚ)
  rw [HonestCircuit.layer_plain (width := 1) (List.replicate 8 1) (List.replicate 8 1) [2, 2]
    (fun _ => 1) (fun _ => 1) (fun _ => 2) decodedWiring decodedWiring decodedInputs (by decide)]
  have math : Protocols.Gkr.layer (fun _ : Fin 3 → Bool => (1 : ℚ)) (fun _ => 1)
      (fun _ : Fin 1 → Bool => 2) = fun _ => 32 := by
    funext gate
    norm_num [Protocols.Gkr.layer, Protocols.Gkr.gates, Protocols.Gkr.sumTable,
      Protocols.Gkr.productTable, booleanSum, half]
  rw [math]
  rfl

/-- Altering the helper result does not preserve the actual source equation. -/
theorem changed_helper :
    invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).closed
      GkrSourceBodies.helper33Helper
      (.cons (List.replicate 8 1) (.cons (List.replicate 8 1) (.cons [2, 2] (.cons 1 .nil)))) ≠
        .done (.cons [33, 32] .nil) := by
  rw [actual_layer]
  intro wrong
  have values := congrArg (fun result => result.get .here) (PIR.Process.done.inj wrong)
  norm_num [Values.get] at values

/-- The current source refuses a count outside its admitted repeat bound. -/
theorem refused_round_count :
    Generated.Presentations.Gkr.Rounds.proverRoundsProcess (F := ℚ) (G := ℚ) {} none none none none (some 5) =
      .halt .refused := by
  unfold Generated.Presentations.Gkr.Rounds.proverRoundsProcess
  change (invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).closed
    GkrSourceBodies.emptyHelper .nil).bind _ = _
  rw [HonestProducerRounds.empty_plain]
  norm_num [PIR.Process.bind, denoteRepeat, Generated.Presentations.Gkr.Rounds.roundSpec, ProtocolContext.roles]

/-- The source association also elaborates for an independently chosen group
carrier. No field/group equality or finite enumeration is used. -/
theorem current_distinct_group :
    GkrSourceViews.program.participant ℚ (ℚ × ℚ) 0
      (.cons (some mixed.inputs) (.cons (some [4352, 4352]) (.cons (some mixed.add)
        (.cons (some mixed.mul) (.cons (some mixed.layers) (.cons (some mixed.selector)
          (.cons (some mixed.width) (.cons none .nil)))))))) =
      HonestProducerSource.producer (G := ℚ × ℚ) {} mixed :=
  HonestProducerSource.original mixed [4352, 4352] admitted none

/-- The actual mixed-circuit source pair returns both complete rows, including
the absent private producer Boolean and the present accepting validator Boolean.
Every challenge reply and the missing producer service are retained. -/
theorem actual_generated_proof (scope : ZkcSecurity.Source.PairScope)
    (roles : scope.producer = 0 ∧ scope.validator = 1) (handle : Nat)
    (outputDelivery : (GkrVerifier.outputSite {}, GkrVerifier.outputDeliverySite {}) ∈ scope.deliveries)
    (leftDelivery : (GkrVerifier.challengeSite (GkrVerifier.leftContext {}),
      GkrVerifier.deliverySite (GkrVerifier.leftContext {})) ∈ scope.deliveries)
    (rightDelivery : (GkrVerifier.challengeSite (GkrVerifier.rightContext {}),
      GkrVerifier.deliverySite (GkrVerifier.rightContext {})) ∈ scope.deliveries)
    (lineDelivery : (GkrVerifier.lineChallengeSite {}, GkrVerifier.lineDeliverySite {}) ∈ scope.deliveries) :
    ZkcSecurity.Source.Pair scope CanonicalReadback.Post
      (Occurrence.participant (ringModel ℚ (ℚ × ℚ)) GkrSourceViews.program 0
        (currentInputs mixed [4352, 4352] none))
      (Occurrence.participant (ringModel ℚ (ℚ × ℚ)) GkrSourceViews.program 1
        (currentInputs mixed [4352, 4352] (some handle))) :=
  CanonicalReadback.actual mixed [4352, 4352] admitted correct handle none scope roles
    outputDelivery leftDelivery rightDelivery lineDelivery

/-- An invalid actual close refuses, preserving the actual stop. -/
theorem unmatched_frame (routing : Original.Routing) :
    Original.fold (carriers := uniformCarriers ℚ (ℚ × ℚ)) routing
      (.call (.leave ⟨"layer", 1⟩) .done) {} = .halt .refused := by rfl

#print axioms HonestProducerSource.observed
#print axioms HonestProducerSource.layer_actual
#print axioms actual_generated_proof
#print axioms HonestProducerSource.original
#print axioms HonestProducerOccurrences.rounds
#print axioms HonestProducerObservedLayers.layer_pair
#print axioms HonestProducerObserved.pair
#print axioms HonestProducerOccurrences.producerRounds_prefix
#print axioms current_distinct_group
#print axioms unmatched_frame
#print axioms correct
#print axioms wrong_output
#print axioms actual_layer
#print axioms changed_helper
#print axioms refused_round_count

end TestsSecurity.GkrHonestProducer
