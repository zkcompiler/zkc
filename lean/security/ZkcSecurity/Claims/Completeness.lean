module

public import ZkcSecurity.Claims.HonestModel

@[expose] public section

/-! Compiled-ideal completeness has one fixed success event and counts all
failure mass. The model, pair, source relation and honest input contract are
selected before evidence. This module does not assert native correspondence. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims.HonestPair
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction
open OracleComp OracleSpec ZkcSecurity.FiatShamir

variable {model : DomainModel} {original : Snapshot} {imported : Imported original}
  {selected : Zkc.Construction.AuthoredPair.Selection original}

namespace Subject

def reference (subject : Subject model original imported selected) : SubjectRef :=
  ⟨subject.originalExport, original.entry, .compiledIdeal,
    [⟨"producer", subject.producerExport⟩, ⟨"validator", subject.validatorExport⟩]⟩

def targetReference (subject : Subject model original imported selected) : Wire.TargetRef :=
  .retained subject.target.owner.contract.owner subject.target.clauseIndex.val selected.target.name

/-- Failed preparation is an unsuccessful observation, never discarded mass. -/
def computation (subject : Subject model original imported selected) (inputs : subject.Inputs) :
    OracleComp (TranscriptOracle.DomainSpec model.toCarriers)
      (Option (Domain.PairExecution model.toCarriers Unit)) :=
  match subject.runtimeInputs inputs with
  | none => pure none
  | some (producer, validator) => some <$> HonestCompiled.computation model imported.program
      subject.selection.context selected.artifacts.producer selected.artifacts.validator producer validator

def Success (subject : Subject model original imported selected)
    (observed : Option (Domain.PairExecution model.toCarriers Unit)) : Prop :=
  ∃ execution, observed = some execution ∧ Domain.PairExecution.Success subject.selection.position execution

/-- Observe both complete executions and the one final cache. Failed input
preparation remains a returned unsuccessful observation. -/
noncomputable def experiment (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (inputs : subject.Inputs) : ProbComp
      (Option (Domain.PairExecution model.toCarriers Unit) × (TranscriptOracle.DomainSpec model.toCarriers).QueryCache) := by
  classical
  exact Honest.run (subject.computation inputs)

noncomputable def failure (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (inputs : subject.Inputs) : ENNReal := by
  classical
  exact Honest.failure (subject.computation inputs) subject.Success

theorem failure_eq_complement (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (inputs : subject.Inputs) : subject.failure inputs =
      1 - Pr{let observed ← subject.experiment inputs}[subject.Success observed.1] := rfl

end Subject

/-- A concrete source-admitted input prevents a false-only contract from
turning a vacuous implication into an admitted completeness certificate. -/
def Nonvacuous (subject : Subject model original imported selected) : Prop :=
  ∃ inputs, subject.Relation inputs ∧ subject.HonestInput inputs

/-- The bound is ENNReal, including the zero-error instance. Input admissibility
combines the retained source clauses and the fixed typed request policy. -/
def CanonicalCompleteness (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (error : ENNReal) : Prop :=
  Nonvacuous subject ∧
    ∀ inputs, subject.Relation inputs → subject.HonestInput inputs → subject.failure inputs ≤ error

structure CompletenessRequest (subject : Subject model original imported selected) where
  stage : Stage
  requestedError : ENNReal

def CompletenessRequest.check {subject : Subject model original imported selected}
    (request : CompletenessRequest subject) : Except ResolutionError Unit :=
  if request.stage = .compiledIdeal then .ok () else .error .stageMismatch

/-- Typed evidence proves the already fixed meaning. There is no producer,
input predicate, success predicate or oracle implementation in this record. -/
structure CompletenessEvidence (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (request : CompletenessRequest subject) : Prop where
  stageChecked : request.check = .ok ()
  lawful : LawfulHonestModel model original
  complete : CanonicalCompleteness subject request.requestedError

theorem perfect_of_all_tables (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (nonvacuous : Nonvacuous subject)
    (agreement : ∀ inputs, subject.Relation inputs → subject.HonestInput inputs →
      ∀ answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id,
        subject.Success (evalWithAnswerFn answers (subject.computation inputs))) :
    CanonicalCompleteness subject 0 := by
  classical
  refine ⟨nonvacuous, ?_⟩
  intro inputs related honest
  exact (Honest.failure_zero_of_all_tables _ _ (agreement inputs related honest)).le

theorem not_perfect_of_failed_input (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (inputs : subject.Inputs) (related : subject.Relation inputs) (honest : subject.HonestInput inputs)
    (failed : ∀ answers : QueryImpl (TranscriptOracle.DomainSpec model.toCarriers) Id,
      ¬ subject.Success (evalWithAnswerFn answers (subject.computation inputs))) :
    ¬ CanonicalCompleteness subject 0 := by
  classical
  rintro ⟨_, complete⟩
  have bound := complete inputs related honest
  have failure : subject.failure inputs = 1 := Honest.failure_one_of_all_tables _ _ failed
  rw [failure] at bound
  exact (not_le_of_gt zero_lt_one) bound

end ZkcSecurity.Claims.HonestPair
