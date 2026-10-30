import ZkcSecurity.Claims.PrivateCompleteness
import ZkcSecurity.Bindings.Transcript.PrivateReadbackWP
import ZkcSecurity.Claims.Methods.SampledReadbackCompleteness
import ZkcSecurityExamples.Generated.Components.SchnorrRandomizedCompleteness
import TestsSecurity.HonestSampling

/-! The actual admitted randomized Schnorr producer now consumes the concrete
verifier WP bridge. Existing capability/refusal and independence controls are
imported so private coins remain fresh and the shared cache remains coherent. -/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TestsSecurity.PrivateProducerWP
open Zkc.Source Zkc.Source.Structured Zkc.Construction OracleComp OracleSpec
open ZkcSecurity.Claims.HonestPair ZkcSecurity.FiatShamir
open ZkcSecurity.Examples.Generated
open ZkcSecurity.Domains.PrimeField

local instance : ∀ event : Domain.Event SchnorrRandomized.subject.domainModel.toCarriers,
    SampleableType (Domain.Raw event) := rawSampleable blsModulus

theorem randomizedSchnorr_complete : CanonicalCompleteness SchnorrRandomized.subject 0 := by
  apply perfect_of_private_producer_wp SchnorrRandomized.subject
    Components.SchnorrRandomizedCompleteness.nonvacuous
  intro inputs related honest producer validator prepared answers
  let abi := Components.SchnorrRandomizedABI.abi
  obtain ⟨data, rfl⟩ := abi.honest_exists inputs honest
  rw [abi.runtime_pack] at prepared
  obtain ⟨rfl, rfl⟩ := Option.some.inj prepared
  exact PrivatePairWP.of_readback _ _ _ _ _ _ _ _ answers
    (Components.SchnorrRandomizedCompleteness.readback data related honest)
    (SampledReadback.fixedServices_return SchnorrRandomized.subject)

/-- A stop observed in production cannot satisfy the private-producer WP,
even when the verifier's postcondition would otherwise be trivial. -/
theorem producer_stop_refused (model : DomainModel)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (program : Structured.Program) (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (position : Nat) (answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id)
    (observed : PIR.Execution (Domain.RuntimeState model.toCarriers Unit) (Domain.Event model.toCarriers)
      (Domain.Result model.toCarriers)) (reason : PIR.Stop)
    (reached : observed ∈ support (Domain.produce model program context producer producerInputs
      (SampledCompiled.tableOracle answers) ()
      (SampledCompiled.privateServices context producer.servicePorts validator.servicePorts)))
    (stopped : observed.outcome = .stopped reason) :
    ¬ PrivatePairWP.producerWP model program context producer validator producerInputs validatorInputs position answers := by
  intro checked
  obtain ⟨⟨value, returned⟩, _⟩ := checked observed reached
  rw [stopped] at returned
  cases returned

/-- Fresh repeated private draws do not satisfy a cached-answer-table law. -/
example (initial : Domain.RuntimeState HonestSampling.carriers Unit) :
    Pr{let observed ← (ZkcSecurity.FiatShamir.HonestSampling.run
      (Domain.run .producer SampledCompiled.oracle HonestSampling.twoDraws initial
        (SampledCompiled.services HonestSampling.context [HonestSampling.port] [])))}[
      ∃ first second, observed.1.outcome = .returned (first, second) ∧ first = second] ≠ 1 :=
  HonestSampling.fresh_not_cached initial

namespace CoinStop
open TestsSecurity.HonestSampling

/-- The draw really occurs before the branch; a zero draw stops production. -/
def producer : PIR.Process (Domain.effects carriers) F :=
  .call (.localService port origin) fun (value : F) =>
    if value = 0 then .halt .exhausted else .done value

/-- Keep the stopped execution as an ordinary observation, with the entire
incoming state. It is not removed by conditioning on successful production. -/
theorem execution (initial : Domain.RuntimeState carriers Unit) :
    Domain.run .producer SampledCompiled.oracle producer initial
      (SampledCompiled.services context [port] []) =
      liftM ((fun value : F => PIR.Execution.mk
        (if value = 0 then .stopped .exhausted else .returned value) initial []) <$> ($ᵗ F)) := by
  simp [producer, Domain.run, PIR.Process.runM, Domain.handler,
    SampledCompiled.services, SampledCompiled.privateServices, installed,
    PIR.Execution.followM]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply bind_congr
  intro value
  change F at value
  by_cases zero : value = 0 <;> simp [zero, PIR.Process.runM]

/-- Exact unsuccessful mass of the sampled stopping client. -/
theorem failure (initial : Domain.RuntimeState carriers Unit) :
    ZkcSecurity.FiatShamir.HonestSampling.failure
      (Domain.run .producer SampledCompiled.oracle producer initial
        (SampledCompiled.services context [port] []))
      (fun observed => ∃ value, observed.outcome = .returned value) = 1 / 7 := by
  rw [ZkcSecurity.FiatShamir.HonestSampling.failure_eq_unsuccessful]
  unfold ZkcSecurity.FiatShamir.HonestSampling.run
  rw [execution, ZkcSecurity.FiatShamir.HonestSampling.private_preserves_cache]
  simp only [Functor.map_map]
  have event (value : F) :
      (¬ ∃ result, (if value = 0 then PIR.Outcome.stopped PIR.Stop.exhausted else .returned value) =
        .returned result) ↔ value = 0 := by
    by_cases zero : value = 0 <;> simp [zero]
  simp only [event]
  simpa using SampleableType.prEvent_uniformSample_eq_singleton (0 : F)
end CoinStop

#print axioms randomizedSchnorr_complete
#print axioms producer_stop_refused
#print axioms CoinStop.failure
#print axioms PrivatePairWP.validate_of_wp
#print axioms PrivatePairWP.of_readback
#print axioms PrivatePairWP.pair_success
#print axioms perfect_of_private_producer_wp
end TestsSecurity.PrivateProducerWP
