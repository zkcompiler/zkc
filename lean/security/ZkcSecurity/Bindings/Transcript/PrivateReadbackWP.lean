module

public import ZkcSecurity.Bindings.Transcript.PrivatePairWP
public import ZkcSecurity.Bindings.Transcript.HonestSampledReadback

@[expose] public section

/-! Reuse sampled readback component proofs through the concrete verifier WP.
Only producer draws are installed in this selected method; each draw still
has its own support and its own continuation. -/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.PrivatePairWP
open Zkc.Source Zkc.Construction OracleComp OracleSpec

variable {carriers : Structured.Carriers}

def producerServices (services : Domain.LocalServices ProbComp carriers Unit) :
    Domain.LocalServices ProbComp carriers Unit := fun mode port origin state =>
  match mode with
  | .producer => services .producer port origin state
  | .validator => pure (.stopped .refused, state)

theorem producer_handler (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id)
    (services : Domain.LocalServices ProbComp carriers Unit) :
    Domain.handler .producer (SampledCompiled.tableOracle answers) (producerServices services) =
      Domain.handler .producer (SampledCompiled.tableOracle answers) services := by
  funext operation state
  cases operation <;> rfl

theorem validator_handler (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id)
    (services : Domain.LocalServices ProbComp carriers Unit) :
    Domain.handler .validator (SampledCompiled.tableOracle answers) (producerServices services) =
      (fun operation state => pure (Domain.handler .validator (HonestCompiled.tableOracle answers)
        Domain.refuseLocal operation state)) := by
  funext operation state
  have lifted := Domain.handler_lift (m := Id) (n := ProbComp)
    (HonestCompiled.tableOracle answers) Domain.refuseLocal .validator operation state
  cases operation <;> exact lifted.symm

/-- The component proof is reused with a producer-only service handler. The
producer execution is unchanged; the resulting validator equation is exactly
its concrete WP under the common table handler. -/
theorem of_readback (model : Structured.DomainModel)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (program : Structured.Program) (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (position : Nat) (answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id)
    {Allowed : ServicePort → Origin → Prop}
    (aligned : SampledReadback Allowed
      (fun _ result => Domain.acceptanceAt position result.values = some true)
      (Domain.participant model program context producer producerInputs)
      (Domain.participant model program context validator validatorInputs))
    (total : SampledReadback.Returns Allowed
      (SampledCompiled.privateServices (carriers := model.toCarriers) context
        producer.servicePorts validator.servicePorts) (S := Unit)) :
    producerWP model program context producer validator producerInputs validatorInputs position answers := by
  intro produced supported
  let services : Domain.LocalServices ProbComp model.toCarriers Unit :=
    SampledCompiled.privateServices context producer.servicePorts validator.servicePorts
  have mixedTotal : SampledReadback.Returns Allowed (producerServices services) := total
  have mixedSupported : produced ∈ support (Domain.run .producer (SampledCompiled.tableOracle answers)
      (Domain.participant model program context producer producerInputs)
      ⟨producerInputs, [], ()⟩ (producerServices services)) := by
    simpa only [Domain.produce, Domain.run, producer_handler] using supported
  obtain ⟨a, b, final, events, proof, returned, emitted, validated, accepted⟩ :=
    aligned.run answers (producerServices services) mixedTotal () producerInputs validatorInputs
      [] [] produced mixedSupported
  refine ⟨⟨a, returned⟩, ?_⟩
  simp only [List.nil_append, List.append_nil] at emitted validated
  have sameTable : ReadbackTransport.tableOracle (m := ProbComp) (S := Unit) answers =
      SampledCompiled.tableOracle answers := rfl
  rw [sameTable] at validated
  unfold Domain.run at validated
  rw [validator_handler, PIR.runM_pure] at validated
  have executed := (OracleComp.pure_inj _ _).mp validated
  cases state : produced.state.oracle
  simp only [state] at executed
  unfold validatorWP
  rw [PIR.WeakestPrecondition.wp_eq_run, emitted, executed]
  exact ⟨rfl, accepted⟩

end ZkcSecurity.FiatShamir.PrivatePairWP
