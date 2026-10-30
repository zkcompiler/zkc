module

public import ZkcSecurity.Claims.Completeness
public import ZkcSecurity.Bindings.Transcript.PrivatePairWP

@[expose] public section

/-! Selected private-producer WP consumer of canonical honest completeness.
Input preparation, nonvacuity and the complete success/failure experiment are
inherited unchanged from the request-owned subject. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims.HonestPair
open Zkc.Source Zkc.Source.Structured Zkc.Construction OracleComp OracleSpec
open ZkcSecurity.FiatShamir

variable {model : DomainModel} {original : Snapshot} {imported : Imported original}
  {selected : AuthoredPair.Selection original}

theorem perfect_of_private_producer_wp (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (nonvacuous : Nonvacuous subject)
    (checked : ∀ inputs, subject.Relation inputs → subject.HonestInput inputs →
      ∀ producer validator, subject.runtimeInputs inputs = some (producer, validator) →
      ∀ answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id,
        PrivatePairWP.producerWP model imported.program subject.selection.context
          selected.artifacts.producer selected.artifacts.validator producer validator subject.selection.position answers) :
    CanonicalCompleteness subject 0 := by
  apply perfect_of_all_tables subject nonvacuous
  intro inputs related honest answers
  obtain ⟨producer, validator, prepared, _⟩ := honest.2.2
  simp only [Subject.computation, prepared, simulateQ_map, prEvent_map, SampledCompiled.simulate_computation]
  have success := PrivatePairWP.pair_success model imported.program subject.selection.context
    selected.artifacts.producer selected.artifacts.validator producer validator subject.selection.position answers
    (checked inputs related honest producer validator prepared answers)
  simpa [Subject.Success] using success

end ZkcSecurity.Claims.HonestPair
