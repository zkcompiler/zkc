module

public import ZkcSecurity.Endpoint.DomainCompiled
public import Zkc.Construction.RetainedTarget
public import Zkc.Source.Structured.DomainContract
public import Zkc.Claims.Registry

@[expose] public section

/-! Request-owned dependent verifier subjects. Relation truth reads the actual
nominal values through retained selectors and the request's fixed registry. -/
set_option autoImplicit false
namespace ZkcSecurity.Claims.Domain
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction

structure ChallengeOccurrence where
  suite : String
  field : String
  template : Template
  deriving DecidableEq, Repr

mutual
def challengeOccurrence (instruction : Zkc.Construction.Instruction) : List ChallengeOccurrence :=
  match instruction with
  | ⟨.challenge suite field template, _, _, body⟩ =>
      ⟨suite, field, template⟩ :: challengeOccurrences body
  | ⟨_, _, _, body⟩ => challengeOccurrences body

def challengeOccurrences : List Zkc.Construction.Instruction → List ChallengeOccurrence
  | [] => []
  | first :: rest => challengeOccurrence first ++ challengeOccurrences rest
end

/-- Labels select an actual retained challenge occurrence before evidence.
The construction/source checks separately validate its complete origin. -/
structure ChargeSite {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (compiled : ZkcSecurity.Endpoint.Domain.Compiled art) where
  label : String
  occurrence : ChallengeOccurrence
  retained : occurrence ∈ challengeOccurrences art.participant.instructions
  native : String
  nativeMatched : occurrence.template.querySite? = some native
  selected : ∃ delivery, (native, delivery) ∈ compiled.selection.context.draws

structure Subject (model : DomainModel) (art : ZkcSecurity.Endpoint.Domain.Artifacts) : Type 1 where
  compiled : ZkcSecurity.Endpoint.Domain.Compiled art
  target : RetainedTarget compiled.imported art.participant.policy art.publics
  relations : RegisteredRelations model.Value art.original.relations
  meaning : RelationMeaning compiled.imported target.application.relation model.Value relations.registry
  originalExport : String
  participantExport : String
  sites : List (ChargeSite compiled) := []

namespace Subject
variable {model : DomainModel} {art : ZkcSecurity.Endpoint.Domain.Artifacts}
  (subject : Subject model art)

def reference : SubjectRef :=
  ⟨subject.originalExport, art.original.entry, .compiledIdeal,
    [⟨"constructed-participant", subject.participantExport⟩]⟩

def targetReference : Wire.TargetRef :=
  .retained subject.target.owner.contract.owner subject.target.clauseIndex.val
    (subject.target.owner.clause subject.target.clauseIndex).name

def acceptance : Wire.Acceptance :=
  ⟨true, art.participant.policy.acceptance, subject.compiled.selection.context.validator, []⟩

def check (request : Wire.Request) : Except ResolutionError Unit := do
  if request.subject != subject.reference then throw .subjectMismatch
  if !request.target.matches subject.targetReference then throw .targetMismatch
  if request.accept != subject.acceptance then throw .acceptanceMismatch

abbrev Witness := subject.target.WitnessOn model.Value

def published := subject.target.published (carriers := model.toCarriers)
def publishedInputs := subject.target.publishedInputs (carriers := model.toCarriers)
def boundary := subject.target.boundary (carriers := model.toCarriers)
def assignments := subject.target.assignments (carriers := model.toCarriers)

def Holds (statement : art.Statement model) (witness : subject.Witness) : Prop :=
  subject.target.HoldsOn subject.meaning statement witness

/-- Exact preservation of the previous formula receipt meaning, including the
same ordered publication/witness read and every stopped invocation. -/
theorem holds_formula_iff (binding : FormulaBinding subject.compiled.imported subject.target.application.relation)
    (statement : art.Statement model) (witness : subject.Witness) :
    subject.Holds statement witness ↔
      ∃ arguments, subject.target.application.read {} (subject.boundary statement)
        (subject.assignments statement witness) = some arguments ∧
        binding.invokeRelationOn model arguments =
          .done (subject.target.booleanOutput.symm ▸ Values.cons true .nil) :=
  exists_congr fun arguments => and_congr Iff.rfl
    (subject.meaning.formula_exact binding subject.target.booleanOutput arguments)

def FalseStatement (statement : art.Statement model) : Prop := ¬ ∃ witness, subject.Holds statement witness

def ConstructionChecked : Prop :=
  checkCompiled subject.compiled.imported art.participant = .ok () ∧
  select subject.compiled.imported art.participant = some subject.compiled.selection ∧
  subject.compiled.selection.check subject.compiled.imported art.participant = true ∧
  subject.compiled.selection.publics = art.publics ∧
  SourceOccurrences.check art.original subject.compiled.selection.context art.participant = .ok ()

theorem constructionChecked : subject.ConstructionChecked :=
  ⟨subject.compiled.compiled, subject.compiled.selected, subject.compiled.checked,
    subject.compiled.publics, subject.compiled.occurrences⟩

/-- A stage link is indexed by the actual subject even when two subjects
share the same compiled program and fixed connection proposition. -/
def SourceConnectionChecked : Prop :=
  ConnectionAdmission.Required subject.compiled.imported.program
    subject.compiled.selection.context .validator art.participant

def stageLinks : List Obligation :=
  [⟨"construction.checked", "admitted IR and selected dependent participant",
    subject.ConstructionChecked, .infrastructure⟩,
   ⟨"construction.source_connection", "complete source-to-participant correspondence",
    subject.SourceConnectionChecked, .infrastructure⟩]

def stageLinkProofs (index : Fin subject.stageLinks.length) :
    Option (PLift (subject.stageLinks.get index).goal) := by
  match index with
  | ⟨0, _⟩ => exact some ⟨subject.constructionChecked⟩
  | ⟨1, _⟩ => exact subject.compiled.sourceConnection
  | ⟨n + 2, impossible⟩ => exact False.elim (by simp [stageLinks] at impossible)

end Subject
end ZkcSecurity.Claims.Domain
