module

public import ZkcSecurity.Bindings.Transcript.HonestSampledReadback
public import ZkcSecurity.Claims.Completeness
public import ZkcSecurity.Bindings.Subjects.ABI

@[expose] public section

/-! One assembly path for deterministic and privately randomized honest proofs.
The request fixes capabilities and the actual producer/verifier. Readback is
only a method for proving that fixed canonical experiment, never its meaning. -/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.SampledReadback
open Zkc.Source Zkc.Source.Structured Zkc.Construction OracleComp OracleSpec
open ZkcSecurity.Claims.HonestPair

variable {model : DomainModel} {original : Snapshot} {imported : Imported original}
  {selected : AuthoredPair.Selection original}

def Allowed (subject : Subject model original imported selected) (port : ServicePort) (origin : Origin) : Prop :=
  SampledCompiled.allowed subject.selection.context selected.artifacts.producer.servicePorts
    selected.artifacts.validator.servicePorts .producer port origin = true

theorem fixedServices_return (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)] :
    Returns (carriers := model.toCarriers) (Allowed subject) (S := Unit)
      (SampledCompiled.privateServices subject.selection.context selected.artifacts.producer.servicePorts
        selected.artifacts.validator.servicePorts) := by
  intro port origin permitted state outcome final reached
  simp only [SampledCompiled.privateServices, Allowed] at permitted reached
  simp only [permitted, ite_true] at reached
  obtain ⟨reply, _, observed⟩ := mem_support_bind_peel _ _ reached
  have same := eq_of_mem_support_pure _ observed
  exact ⟨reply, congrArg Prod.fst same⟩

theorem perfect (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (nonvacuous : Nonvacuous subject)
    (readback : ∀ inputs, subject.Relation inputs → subject.HonestInput inputs →
      ∀ producer validator, subject.runtimeInputs inputs = some (producer, validator) →
      SampledReadback (Allowed subject)
        (fun _ result => Domain.acceptanceAt subject.selection.position result.values = some true)
        (Domain.participant model imported.program subject.selection.context selected.artifacts.producer producer)
        (Domain.participant model imported.program subject.selection.context selected.artifacts.validator validator)) :
    CanonicalCompleteness subject 0 := by
  apply perfect_of_all_tables subject nonvacuous
  intro inputs related honest answers
  obtain ⟨producer, validator, prepared, _⟩ := honest.2.2
  simp only [Subject.computation, prepared, simulateQ_map, prEvent_map,
    SampledCompiled.simulate_computation]
  have success := (readback inputs related honest producer validator prepared).pair_success
    model imported.program subject.selection.context selected.artifacts.producer selected.artifacts.validator
    producer validator subject.selection.position answers
    (SampledCompiled.privateServices subject.selection.context selected.artifacts.producer.servicePorts
      selected.artifacts.validator.servicePorts) (fixedServices_return subject) ()
  have tableLaw : SampledCompiled.tableOracle answers =
      ReadbackTransport.tableOracle (m := ProbComp) (S := Unit) answers := rfl
  rw [tableLaw]
  simpa [Subject.Success] using success

theorem perfect_abi (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (abi : Subject.ABI subject) (nonvacuous : Nonvacuous subject)
    (readback : ∀ data, subject.Relation (abi.pack data) → subject.HonestInput (abi.pack data) →
      SampledReadback (Allowed subject)
        (fun _ result => Domain.acceptanceAt subject.selection.position result.values = some true)
        (Domain.participant model imported.program subject.selection.context selected.artifacts.producer (abi.producer data))
        (Domain.participant model imported.program subject.selection.context selected.artifacts.validator (abi.validator data))) :
    CanonicalCompleteness subject 0 := by
  apply perfect subject nonvacuous
  intro inputs related honest producer validator prepared
  obtain ⟨data, rfl⟩ := abi.honest_exists inputs honest
  rw [abi.runtime_pack] at prepared
  obtain ⟨rfl, rfl⟩ := Option.some.inj prepared
  exact readback data related honest

end ZkcSecurity.FiatShamir.SampledReadback
