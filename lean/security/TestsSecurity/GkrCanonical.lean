import ZkcSecurity.Realizations.Gkr.Canonical
import TestsSecurity.GkrRootEncoding
import ZkcSecurity.Realizations.Gkr.CanonicalReadback
import Zkc.Construction.DomainProducer

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 50000

noncomputable section
namespace TestsSecurity.GkrCanonical
open Zkc.Source.Structured
open Zkc.Construction
open ZkcSecurity.Realizations.Gkr
open TestsSecurity.GkrRootEncoding

private def model : DomainModel := ringModel ℚ ℚ

private def refusingOracle : Domain.Oracle Id model.toCarriers Unit :=
  fun _ _ state => (.stopped .refused, state)

/-- Run the actual constructed validator with the canonical public input
frame and an empty proof. This oracle refuses every request. -/
private def validatorExecution (runtime : Source.Invocation ℚ) :=
  let env := ((Canonical.subject model).runtimeInputs
    (Canonical.sourceInputs model runtime)).getD ([], []) |>.2
  Domain.validate model Canonical.imported.program (Canonical.subject model).selection.context
    Canonical.artifacts.validator env [] refusingOracle ()

private def validatorDecision (runtime : Source.Invocation ℚ) : Option Bool :=
  match (validatorExecution runtime).outcome with
  | .returned returned =>
    match returned.values[0]? with
    | some (Domain.Value.data (Domain.Payload.boolean accepted)) => some accepted
    | _ => none
  | .stopped _ => none

theorem actual_zero_layers : validatorDecision zeroLayers = some true := by kernel_rfl

theorem actual_false_zero_layers :
    validatorDecision { zeroLayers with outputs := [4] } = some false := by kernel_rfl

example : (validatorExecution malformedZeroLayerAdd).outcome = .stopped .reject := by kernel_rfl
example : (validatorExecution malformedZeroLayerMul).outcome = .stopped .reject := by kernel_rfl
example : (validatorExecution zeroLayers).state.proof = [] := by kernel_rfl

/-- A concrete current-source pair control. The actual constructed producer
computes the proof, and its actual oracle state is passed to validation. The
constant oracle is only a deterministic test interpretation. -/
private def zeroOracle : Domain.Oracle Id model.toCarriers Nat
  | _, .challenge ⟨_, _, some ⟨_, _, .field _⟩⟩, state => (.returned 0, state + 1)
  | _, .challenge ⟨_, _, some ⟨_, _, .boolean⟩⟩, state => (.returned (), state)
  | _, .challenge ⟨_, _, some ⟨_, _, .group _⟩⟩, state => (.returned (), state)
  | _, .challenge ⟨_, _, some ⟨_, _, .groups _⟩⟩, state => (.returned (), state)
  | _, .challenge ⟨_, _, some ⟨_, _, .indices⟩⟩, state => (.returned (), state)
  | _, .challenge ⟨_, _, some ⟨_, _, .oracle _⟩⟩, state => (.returned (), state)
  | _, .challenge ⟨_, _, some ⟨_, _, .oracleSequence _ _⟩⟩, state => (.returned (), state)
  | _, .challenge ⟨_, _, some ⟨_, _, .service _⟩⟩, state => (.returned (), state)
  | _, .challenge ⟨_, _, some ⟨_, _, .index⟩⟩, state => (.returned (), state)
  | _, .challenge ⟨_, _, some ⟨_, _, .vector _⟩⟩, state => (.returned (), state)
  | _, .challenge ⟨_, _, some ⟨_, _, .sequence _⟩⟩, state => (.returned (), state)
  | _, .challenge ⟨_, _, some ⟨_, _, .product _ _ _⟩⟩, state => (.returned (), state)
  | _, .challenge ⟨_, _, none⟩, state => (.returned (), state)
  | _, .message _ _, state => (.returned (), state)
  | _, .publicBinding _, state => (.returned (), state)
private def pairedExecution :=
  let env := ((Canonical.subject model).runtimeInputs
    (Canonical.sourceInputs model oneLayer)).getD ([], [])
  Domain.executePair model Canonical.imported.program (Canonical.subject model).selection.context
    Canonical.artifacts.producer Canonical.artifacts.validator env.1 env.2 zeroOracle 0

theorem actual_one_layer_proof : pairedExecution.producer.state.proof =
    [Domain.Payload.field "bls12-381.fr" 3] := by kernel_rfl

example : pairedExecution.producer.state.oracle = 1 := by kernel_rfl
example : pairedExecution.validator.map (fun result => result.state.oracle) = some 2 := by kernel_rfl
example : pairedExecution.validator.map (fun result => result.state.proof) = some [] := by kernel_rfl
/-- The universal source pair retains arbitrary replies and every occurrence
boundary. Concrete producer output and endpoint decisions remain separate controls. -/
example (encoding : CircuitEncoding ℚ) (outputs : List ℚ)
    (admitted : encoding.Admitted 4 4 outputs) (correct : encoding.Outputs outputs)
    (handle : Nat) (service : Option Nat) (scope : ZkcSecurity.Source.PairScope)
    (roles : scope.producer = 0 ∧ scope.validator = 1)
    (outputDelivery : (ZkcExamples.Structured.GkrVerifier.outputSite {},
      ZkcExamples.Structured.GkrVerifier.outputDeliverySite {}) ∈ scope.deliveries)
    (leftDelivery : (ZkcExamples.Structured.GkrVerifier.challengeSite
      (ZkcExamples.Structured.GkrVerifier.leftContext {}),
      ZkcExamples.Structured.GkrVerifier.deliverySite
      (ZkcExamples.Structured.GkrVerifier.leftContext {})) ∈ scope.deliveries)
    (rightDelivery : (ZkcExamples.Structured.GkrVerifier.challengeSite
      (ZkcExamples.Structured.GkrVerifier.rightContext {}),
      ZkcExamples.Structured.GkrVerifier.deliverySite
      (ZkcExamples.Structured.GkrVerifier.rightContext {})) ∈ scope.deliveries)
    (lineDelivery : (ZkcExamples.Structured.GkrVerifier.lineChallengeSite {},
      ZkcExamples.Structured.GkrVerifier.lineDeliverySite {}) ∈ scope.deliveries) :
    ZkcSecurity.Source.Pair scope CanonicalReadback.Post
      (Occurrence.participant (ringModel ℚ ℚ) ZkcExamples.Structured.GkrSourceViews.program 0
        (HonestProducerSource.currentInputs encoding outputs service))
      (Occurrence.participant (ringModel ℚ ℚ) ZkcExamples.Structured.GkrSourceViews.program 1
        (HonestProducerSource.currentInputs encoding outputs (some handle))) :=
  CanonicalReadback.actual encoding outputs admitted correct handle service scope roles
    outputDelivery leftDelivery rightDelivery lineDelivery

theorem actual_one_layer_accepts : (pairedExecution.validator.map (fun result =>
    match result.outcome with
    | .returned returned => returned.values[0]?
    | .stopped _ => none)) = some (some (.data (.boolean true))) := by kernel_rfl

example : (Canonical.subject model).Relation (Canonical.sourceInputs model oneLayer) :=
  (Canonical.relation_exact model oneLayer).mpr correct

example : (Canonical.validatorSubject model).Holds (Canonical.statement model oneLayer)
    (fun _ _ => none) :=
  (Canonical.holds_exact model oneLayer _).mpr correct

example : (Canonical.validatorSubject model).FalseStatement
    (Canonical.statement model falseOutput) :=
  (Canonical.false_statement_exact model falseOutput).mpr false_output

example : (Canonical.validatorSubject model).FalseStatement
    (Canonical.statement model malformedZeroLayerAdd) :=
  (Canonical.false_statement_exact model malformedZeroLayerAdd).mpr malformed_zero_add_false

example : (Canonical.validatorSubject model).FalseStatement
    (Canonical.statement model malformedZeroLayerMul) :=
  (Canonical.false_statement_exact model malformedZeroLayerMul).mpr malformed_zero_mul_false

/-- A shape-valid false output remains inside the source input policy. -/
example : (Canonical.subject model).inputClause (Canonical.sourceInputs model falseOutput)
    ⟨0, by decide⟩ rfl :=
  (Canonical.input_clause_exact model falseOutput).mpr false_output_admitted

example : (Canonical.subject model).Relation (Canonical.sourceInputs model zeroLayers) :=
  (Canonical.relation_exact model zeroLayers).mpr zero_correct

example : (Canonical.validatorSubject model).targetReference =
    .retained Canonical.original.entry 1 "circuit_outputs" := rfl

example (values : (Canonical.subject model).validatorArtifacts.Statement model) (handle : Nat) :
    Canonical.statement model (Canonical.invocation model values handle) = values :=
  Canonical.statement_invocation model values handle

#print axioms Canonical.subject
#print axioms Canonical.relation_exact
#print axioms Canonical.input_clause_exact
#print axioms Canonical.holds_exact
#print axioms Canonical.false_statement_exact
#print axioms Canonical.holds_all
#print axioms Canonical.statement_invocation
#print axioms Canonical.validatorSites
#print axioms actual_zero_layers
#print axioms actual_false_zero_layers
#print axioms actual_one_layer_proof
#print axioms actual_one_layer_accepts

end TestsSecurity.GkrCanonical
