module

public import ZkcSecurity.Bindings.Transcript.SamplingControl
public import ZkcSecurity.Claims.Completeness
public import ZkcSecurityExamples.Generated.Components.SampledAbortABI
public import ZkcExamples.Structured.Generated.Constructed.SampledAbortProducer
public import ZkcExamples.Structured.Generated.Constructed.SampledAbortValidator
public import Zkc.Construction.DomainCalculations
public meta import ZkcSecurityTools.Bindings.ExecutionReadback

@[expose] public section

/-! Exact nonzero canonical completeness error for the source-admitted
abort-on-zero client. Runtime and source equations come from generated views;
the probability rule does not alter the fixed canonical success event. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
namespace ZkcSecurity.Examples.SampledAbort
open OracleComp OracleSpec ZkcSecurity.FiatShamir
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir.SamplingControl
noncomputable section
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Domains.PrimeField
open ZkcSecurity.Examples.Generated.SampledAbort (subject)
open ZkcSecurity.Examples.Generated.Components.SampledAbortABI

abbrev Scalar := ZMod blsModulus
local instance : SampleableType Scalar := SampleableType.ofFintype Scalar
local instance : ∀ event : Domain.Event subject.domainModel.toCarriers,
    SampleableType (Domain.Raw event) := rawSampleable blsModulus

theorem acceptance_position : subject.selection.position = 0 := rfl

/-- This is the retained Equal(value, expected) formula, with genuine data
inputs and no condition on the subsequently sampled private coin. -/
theorem relation_iff (value expected : Scalar) (nonces challenges : Option Nat) :
    subject.Relation (inputs value expected nonces challenges) ↔ value = expected := by
  rw [Subject.relation_iff_of_read subject _ _ (application_read value expected nonces challenges)]
  change (PIR.Process.done (Values.cons (decide (value = expected)) .nil) :
    PIR.Process Structured.closedInterface (Values subject.domainModel.Value [.boolean])) =
    .done (.cons true .nil) ↔ _
  simp

theorem nonvacuous : Nonvacuous subject :=
  ⟨inputs 0 0 none none, (relation_iff 0 0 none none).mpr rfl,
    (honestInput_iff 0 0 none none).mpr trivial⟩

/-- Exact failure of the source-admitted pair. Missing service values in the
source ABI are handles, not a supplied coin or a restriction on the draw. -/
theorem exact_failure (value expected : Scalar) (nonces challenges : Option Nat) :
    subject.failure (inputs value expected nonces challenges) =
      1 / (Fintype.card Scalar : ENNReal) := by
  classical
  simp only [Subject.failure, Subject.computation, runtimeInputs_eq]
  rw [pair_eq]
  simp only [ZkcSecurity.Examples.Generated.SampledAbort.artifacts,
    ZkcExamples.Construction.Generated.SampledAbortPair.artifacts]
  unfold SampledCompiled.computation Domain.executePair Domain.produce Domain.validate Domain.run
  rw [ZkcExamples.Structured.Generated.Constructed.SampledAbortProducer.participant_eq,
    ZkcExamples.Structured.Generated.Constructed.SampledAbortValidator.participant_eq]
  unfold_component_bodies [ZkcExamples.Structured.Generated.Constructed.SampledAbortProducer.view,
    ZkcExamples.Structured.Generated.Constructed.SampledAbortValidator.view]
  normalize_domain_process [context_eq,
    Domain.Calculations.fieldConstant (F := Scalar) (G := Scalar),
    Domain.Calculations.fieldEqual (F := Scalar) (G := Scalar),
    Domain.Calculations.booleanConstant (F := Scalar) (G := Scalar),
    Domain.Calculations.booleanEqual (F := Scalar) (G := Scalar)] unfolding
    [producerInputs, validatorInputs, blsScalarModel, ZkcSecurity.Domains.PrimeField.model]
  normalize_domain_execution [] unfolding [
    ZkcExamples.Construction.Generated.SampledAbortPair.Producer.participant,
    ZkcExamples.Construction.Generated.SampledAbortPair.Validator.participant]
  apply failure_after_private (Raw := @Domain.Raw subject.domainModel.toCarriers)
    (F := Scalar) (0 : Scalar) (success := subject.Success)
  intro sample cache
  by_cases zero : sample = 0
  · normalize_domain_process [zero] unfolding []
    normalize_domain_execution [] unfolding []
    simp [zero, Subject.Success, Domain.PairExecution.Success]
  · normalize_domain_process [zero] unfolding []
    normalize_domain_execution [] unfolding []
    simp [zero, SampledCompiled.oracle, HonestCompiled.oracle,
      Subject.Success, Domain.PairExecution.Success, Domain.acceptanceAt, acceptance_position,
      simulateQ_map, StateT.run_map]
    rw [← map_bind, prEvent_false]

theorem exact_failure_of_honest (values : subject.Inputs) (honest : subject.HonestInput values) :
    subject.failure values = 1 / (Fintype.card Scalar : ENNReal) := by
  obtain ⟨value, expected, nonces, challenges, rfl⟩ := honestInput_exists values honest
  exact exact_failure value expected nonces challenges

theorem error_positive : 0 < 1 / (Fintype.card Scalar : ENNReal) := by
  simp

theorem compiled_ideal_complete :
    CanonicalCompleteness subject (1 / (Fintype.card Scalar : ENNReal)) := by
  refine ⟨nonvacuous, ?_⟩
  intro values _ honest
  exact (exact_failure_of_honest values honest).le

/-- Equal(0,0) is related and honestly admissible before sampling. The actual
zero-coin path rules out a perfect receipt for precisely this same subject. -/
theorem not_perfect : ¬ CanonicalCompleteness subject 0 := by
  rintro ⟨_, complete⟩
  have bound := complete (inputs 0 0 none none)
    ((relation_iff 0 0 none none).mpr rfl) ((honestInput_iff 0 0 none none).mpr trivial)
  rw [exact_failure] at bound
  exact (not_le_of_gt error_positive) bound

#print axioms failure_after_private
#print axioms run_local_uniform
#print axioms relation_iff
#print axioms nonvacuous
#print axioms exact_failure
#print axioms compiled_ideal_complete
#print axioms not_perfect

end

end ZkcSecurity.Examples.SampledAbort
