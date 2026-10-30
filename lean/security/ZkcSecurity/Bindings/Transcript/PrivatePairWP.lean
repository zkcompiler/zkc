module

public import ZkcSecurity.Bindings.Transcript.SampledCompiled
public import ZkcSecurity.Bindings.Transcript.HonestReadbackTransport
public import Zkc.Semantics.WeakestPrecondition

@[expose] public section

/-! Concrete verifier WP after a privately sampled producer. Public tables fix
only ROM answers. Every supported producer result keeps its actual environment,
proof, events and oracle post-state. The selected verifier scope is a returning
deterministic table run: private validator draws require a different consumer.
No probabilistic WP instance or cost calculus is introduced. -/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.PrivatePairWP
open Zkc.Source Zkc.Construction OracleComp OracleSpec Std.WP

/-- The same full verifier handler used by the existing deterministic pair WP. -/
def validatorWP (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (validator : Participant)
    (inputs : Domain.Environment model.toCarriers) (proof : Domain.Proof model.toCarriers)
    (position : Nat) (answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id) : Prop :=
  letI := PIR.WeakestPrecondition.wpMonad (Domain.handler .validator (HonestCompiled.tableOracle answers))
  Std.WP.wp (Domain.participant model program context validator inputs)
    (fun result state _ => state.proof = [] ∧ Domain.acceptanceAt position result.values = some true)
    estack⟨fun _ _ _ => False⟩ ⟨inputs, proof, ()⟩ []

/-- Quantify over real private-coin support, rather than supplying one shared
deterministic answer for repeated private draws. Stops cannot satisfy this WP. -/
def producerWP (model : Structured.DomainModel)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (program : Structured.Program) (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (position : Nat) (answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id) : Prop :=
  ∀ produced ∈ support (Domain.produce model program context producer producerInputs
      (SampledCompiled.tableOracle answers) ()
      (SampledCompiled.privateServices context producer.servicePorts validator.servicePorts)),
    (∃ result, produced.outcome = .returned result) ∧
      validatorWP model program context validator validatorInputs produced.state.proof position answers

/-- A successful concrete WP determines a full returned execution under the
sampled interpreter. Its private state is the producer's actual handoff state. -/
theorem validate_of_wp (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (validator : Participant) (inputs : Domain.Environment model.toCarriers)
    (proof : Domain.Proof model.toCarriers) (position : Nat)
    (answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id)
    (services : Domain.LocalServices ProbComp model.toCarriers Unit)
    (checked : validatorWP model program context validator inputs proof position answers) :
    ∃ result final events,
      Domain.validate model program context validator inputs proof (SampledCompiled.tableOracle answers) () services =
        pure ⟨.returned result, final, events⟩ ∧
      final.proof = [] ∧ Domain.acceptanceAt position result.values = some true := by
  unfold validatorWP at checked
  rw [PIR.WeakestPrecondition.wp_eq_run] at checked
  generalize execution : (Domain.participant model program context validator inputs).run
    (Domain.handler .validator (HonestCompiled.tableOracle answers)) ⟨inputs, proof, ()⟩ = observed at checked
  rcases observed with ⟨outcome, final, events⟩
  cases outcome with
  | stopped reason => exact checked.elim
  | returned result =>
    have transported := ReadbackTransport.run_table_of_returned answers services .validator ()
      (Domain.participant model program context validator inputs) ⟨inputs, proof, ()⟩
      result final events execution
    refine ⟨result, ReadbackTransport.restore () final, events, ?_, checked.1, checked.2⟩
    exact transported

/-- Success probability one for the exact pair, without suppressing producer
stops, verifier stops, unread proof suffixes, or rejected results. -/
theorem pair_success (model : Structured.DomainModel)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (program : Structured.Program) (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (position : Nat) (answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id)
    (checked : producerWP model program context producer validator producerInputs validatorInputs position answers) :
    Pr{let observed ← (Domain.executePair model program context producer validator producerInputs validatorInputs
      (SampledCompiled.tableOracle answers) ()
      (SampledCompiled.privateServices context producer.servicePorts validator.servicePorts))}[
        Domain.PairExecution.Success position observed] = 1 := by
  apply (prEvent_eq_one_iff _ _).mpr
  intro observed reached
  unfold Domain.executePair at reached
  obtain ⟨produced, supported, continued⟩ := mem_support_bind_peel _ _ reached
  obtain ⟨⟨result, returned⟩, verified⟩ := checked produced supported
  obtain ⟨value, final, events, validation, consumed, accepted⟩ :=
    validate_of_wp model program context validator validatorInputs produced.state.proof position answers
      (SampledCompiled.privateServices context producer.servicePorts validator.servicePorts) verified
  cases state : produced.state.oracle
  simp only [returned, state, validation, pure_bind] at continued
  have same := eq_of_mem_support_pure _ continued
  subst observed
  exact ⟨result, _, value, returned, rfl, rfl, consumed, accepted⟩

end ZkcSecurity.FiatShamir.PrivatePairWP
