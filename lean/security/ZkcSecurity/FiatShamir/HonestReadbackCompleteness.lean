module

public import ZkcSecurity.FiatShamir.HonestReadback
public import ZkcSecurity.Claims.Completeness
public import ZkcSecurity.Claims.SubjectABI

@[expose] public section

/-! Read-back evidence closes the existing compiled-ideal completeness game.
The request-owned subject supplies the producer, validator, relation and input
policy. One table serves both phases, and the existing honest experiment starts
its coherent ROM simulation with an empty cache and counts all failure mass.
-/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.Readback
open Zkc.Source Zkc.Source.Structured Zkc.Construction OracleComp OracleSpec
open ZkcSecurity.Claims.HonestPair

variable {model : DomainModel} {original : Snapshot} {imported : Imported original}
  {selected : AuthoredPair.Selection original}

/-- The only protocol-specific premise is successful actual whole-pair
read-back on the fixed source inputs. A concrete root must close this premise;
the generic theorem itself is not a root certificate. -/
theorem perfect (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (nonvacuous : Nonvacuous subject)
    (readback : ∀ inputs, subject.Relation inputs → subject.HonestInput inputs →
      ∀ producer validator, subject.runtimeInputs inputs = some (producer, validator) →
      Readback
        (fun _ result => HonestCompiled.acceptanceAt subject.selection.position result.values = some true)
        (Domain.participant model imported.program subject.selection.context
          selected.artifacts.producer producer)
        (Domain.participant model imported.program subject.selection.context
          selected.artifacts.validator validator)) :
    CanonicalCompleteness subject 0 := by
  apply perfect_of_all_tables subject nonvacuous
  intro inputs related honest answers
  obtain ⟨producer, validator, prepared, _⟩ := honest.2.2
  refine ⟨_, ?_, (readback inputs related honest producer validator prepared).pair_success
    model imported.program subject.selection.context selected.artifacts.producer
      selected.artifacts.validator producer validator subject.selection.position answers⟩
  simp only [Subject.computation, prepared, evalWithAnswerFn_map, HonestCompiled.eval_computation]

/-- Transport a mathematical read-back law through a checked generated source
ABI. Input elimination, exact runtime preparation and both environment
substitutions are shared by every installed root. -/
theorem of_abi (subject : Subject model original imported selected)
    (abi : Subject.ABI subject)
    (run : ∀ data, subject.Relation (abi.pack data) →
      subject.HonestInput (abi.pack data) →
      Readback
        (fun _ result => HonestCompiled.acceptanceAt subject.selection.position result.values = some true)
        (Domain.participant model imported.program subject.selection.context
          selected.artifacts.producer (abi.producer data))
        (Domain.participant model imported.program subject.selection.context
          selected.artifacts.validator (abi.validator data)))
    (inputs : subject.Inputs) (related : subject.Relation inputs)
    (honest : subject.HonestInput inputs)
    (producer validator : Domain.Environment model.toCarriers)
    (prepared : subject.runtimeInputs inputs = some (producer, validator)) :
    Readback
      (fun _ result => HonestCompiled.acceptanceAt subject.selection.position result.values = some true)
      (Domain.participant model imported.program subject.selection.context
        selected.artifacts.producer producer)
      (Domain.participant model imported.program subject.selection.context
        selected.artifacts.validator validator) := by
  obtain ⟨data, rfl⟩ := abi.honest_exists inputs honest
  rw [abi.runtime_pack] at prepared
  obtain ⟨rfl, rfl⟩ := Option.some.inj prepared
  exact run data related honest

/-- Install one checked ABI and its mathematical read-back law in the actual
compiled-ideal experiment. This assembler adds no protocol-specific premise. -/
theorem perfect_abi (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (abi : Subject.ABI subject) (nonvacuous : Nonvacuous subject)
    (run : ∀ data, subject.Relation (abi.pack data) →
      subject.HonestInput (abi.pack data) →
      Readback
        (fun _ result => HonestCompiled.acceptanceAt subject.selection.position result.values = some true)
        (Domain.participant model imported.program subject.selection.context
          selected.artifacts.producer (abi.producer data))
        (Domain.participant model imported.program subject.selection.context
          selected.artifacts.validator (abi.validator data))) :
    CanonicalCompleteness subject 0 :=
  perfect subject nonvacuous (of_abi subject abi run)

end ZkcSecurity.FiatShamir.Readback
