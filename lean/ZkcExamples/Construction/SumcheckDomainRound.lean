module

public import ZkcExamples.Construction.SumcheckDomainConnection
public import Zkc.Construction.Uniform.DomainIteration
public import Zkc.Construction.OriginalSimulation
public meta import Zkc.Construction.ArtifactBindingTactic

@[expose] public section
/-! All-reply reductions of the actual Sumcheck round. These are equations of
the authoritative Process, with its observations and request-dependent replies.
Only administrative checkpoints are projected away. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Construction.SumcheckDomainConnection
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured
open Zkc.Construction.Uniform.DomainAdapter
open Zkc.Construction.ArtifactBinding
open ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem context_suite : SumcheckProof.context.suite = "merlin3.bls12-381.fr64be/0" := by kernel_rfl

def roundInputs (captured : Domain.Environment (uniformCarriers F G)) (index : Nat)
    (point : List F) (scalar : F) (history : Domain.History (uniformCarriers F G)) :=
  captured ++ [.data (.index index), .data (.vector "bls12-381.fr" point),
    .data (.field "bls12-381.fr" scalar), .transcript SumcheckProof.context.suite history]

def carried (point : List F) (scalar : F) (history : Domain.History (uniformCarriers F G)) :
    Domain.Environment (uniformCarriers F G) :=
  [.data (.vector "bls12-381.fr" point), .data (.field "bls12-381.fr" scalar),
    .transcript SumcheckProof.context.suite history]

structure RoundState (F G : Type) where
  point : List F
  scalar : F
  history : Domain.History (uniformCarriers F G)

def RoundState.values (state : RoundState F G) := carried state.point state.scalar state.history

/-- Expose the already checked request so reply types reduce without transport.
The equality below checks the complete origin, including its actual index. -/
abbrev roundDrawOrigin (index : Nat) : Origin :=
  ⟨(Domain.atCoordinates (staticOrigin drawTemplate) [index]).entry,
    (Domain.atCoordinates (staticOrigin drawTemplate) [index]).event,
    some ⟨"draw", [], .field "bls12-381.fr"⟩⟩

theorem roundDrawOrigin_actual (index : Nat) :
    roundDrawOrigin index = Domain.atCoordinates (staticOrigin drawTemplate) [index] := by kernel_rfl

def roundState (index : Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) :
    PIR.Process (Domain.effects (uniformCarriers F G)) (RoundState F G) :=
  .call (.receive (.field "bls12-381.fr") "apply_18_label_726564756365_label_726f756e64_0"
      "apply_18_label_726564756365_label_726f756e64_0" "role00000000") fun low =>
    let lowEvent := Domain.Event.message (Domain.atCoordinates (staticOrigin lowTemplate) [index])
      (.field "bls12-381.fr" low)
    .call (.observe lowEvent) fun _ =>
      .call (.receive (.field "bls12-381.fr") "apply_18_label_726564756365_label_726f756e64_1"
          "apply_18_label_726564756365_label_726f756e64_1" "role00000000") fun high =>
        let highEvent := Domain.Event.message (Domain.atCoordinates (staticOrigin highTemplate) [index])
          (.field "bls12-381.fr" high)
        .call (.observe highEvent) fun _ =>
          if scalar = low + high then
            let origin := roundDrawOrigin index
            .call (.query (history ++ [lowEvent, highEvent]) origin) fun (answer : F) =>
              let delivery := Domain.Event.message (Domain.atCoordinates (staticOrigin deliveryTemplate) [index])
                (.field "bls12-381.fr" answer)
              .call (.observe delivery) fun _ =>
                .done ⟨point ++ [answer], (1 - answer) * low + answer * high,
                  history ++ [lowEvent, highEvent, .challenge origin, delivery]⟩
          else .halt .reject

def roundProcess (index : Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) :=
  (roundState index point scalar history).bind fun state => .done state.values

def roundProjection (captured : Domain.Environment (uniformCarriers F G)) (index : Nat)
    (point : List F) (scalar : F) (history : Domain.History (uniformCarriers F G)) :=
  ((bodyStep2Body (ringModel F G) SumcheckProof.program SumcheckProof.context
      (roundInputs captured index point scalar history)).bind
    (yieldValues [29, 34, 28] roundInstruction.results)).interpret Original.forgetCheckpoints

theorem round_projection (a b c d e f g h : Domain.Value (uniformCarriers F G))
    (index : Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) :
    roundProjection [a, b, c, d, e, f, g, h] index point scalar history = roundProcess index point scalar history := by
  have lowResolved := low_origin index
  have highResolved := high_origin index
  have drawResolved := draw_origin index
  have deliveryResolved := delivery_origin index
  have requests := message_requests index
  have drawRequest := draw_request index
  have appendResult (point : List F) (answer : F) := append_helper (G := G) point answer
  have loopResults : (SumcheckProof.participant.instructions[2]'(by decide +kernel)).results =
      [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"),
        .transcript "merlin3.bls12-381.fr64be/0"] := by kernel_rfl
  simp only [lowTemplate, highTemplate, drawTemplate, deliveryTemplate, roundBody, roundInstruction,
      SumcheckProof.participant, SumcheckProofParticipant.participant, List.getElem_cons_zero, List.getElem_cons_succ]
    at lowResolved highResolved drawResolved deliveryResolved requests drawRequest
  simp only [context_suite] at drawResolved
  simp only [roundProjection, roundInputs, bodyStep2Body,
    bodyStep2BodyStep0, bodyStep2BodyStep1, bodyStep2BodyStep2, bodyStep2BodyStep3,
    bodyStep2BodyStep4, bodyStep2BodyStep5, bodyStep2BodyStep6, bodyStep2BodyStep7,
    bodyStep2BodyStep8, bodyStep2BodyStep9, bodyStep2BodyStep10, bodyStep2BodyStep11,
    bodyStep2BodyStep12, bodyStep2BodyStep13, bodyStep2BodyStep14, bodyStep2BodyStep15,
    bodyStep2BodyStep16, bodyStep2BodyStep17, bodyStep2BodyStep18, bodyStep2BodyStep19,
    bodyStep2BodyStep20, bodyStep2BodyStep21, bodyStep2BodyStep22]
  normalize_artifact_operations [roundDrawOrigin_actual, appendResult, lowResolved, highResolved, drawResolved, deliveryResolved, context_suite,
      requests.1, requests.2.1, requests.2.2, drawRequest,
      Domain.Calculations.fieldAdd (F := F) (G := G),
      Domain.Calculations.fieldEqual (F := F) (G := G),
      Domain.Calculations.fieldConstant (F := F) (G := G),
      Domain.Calculations.fieldSubtract (F := F) (G := G),
      Domain.Calculations.fieldMultiply (F := F) (G := G)]
    unfolding [roundProcess, roundState, RoundState.values, carried, roundInstruction, PIR.Process.interpret, Original.forgetCheckpoints,
      Structured.Ty.isHandle, Bool.not_false, Bool.not_true]
  congr 1
  funext low
  simp only [PIR.Process.bind]
  congr 1
  funext ignoredLow
  congr 1
  funext high
  congr 1
  funext ignoredHigh
  by_cases valid : scalar = low + high
  all_goals simp only [valid, decide_true, decide_false, ite_true, ite_false]
  all_goals normalize_artifact_operations [loopResults, appendResult, lowResolved, highResolved, drawResolved, deliveryResolved, context_suite,
      requests.1, requests.2.1, requests.2.2, drawRequest,
      Domain.Calculations.fieldAdd (F := F) (G := G),
      Domain.Calculations.fieldEqual (F := F) (G := G),
      Domain.Calculations.fieldConstant (F := F) (G := G),
      Domain.Calculations.fieldSubtract (F := F) (G := G),
      Domain.Calculations.fieldMultiply (F := F) (G := G)]
    unfolding [PIR.Process.interpret, Original.forgetCheckpoints, Structured.Ty.isHandle,
      Bool.not_false, Bool.not_true, List.append_assoc, Nat.cast_one, yieldValues]
  all_goals rfl

end ZkcExamples.Construction.SumcheckDomainConnection
