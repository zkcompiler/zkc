module

public import ZkcSecurity.Endpoint.DomainCompiled
public import Zkc.Construction.RetainedTarget
public import Zkc.Source.Structured.DomainContract
public import ZkcSecurity.Claims.Model

@[expose] public section

/-! Request-owned dependent verifier subjects. Formula truth reads the actual
nominal values through the retained selectors and the model's helper table. -/
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

abbrev Witness := (type : Ty) →
  BoundarySelector subject.target.owner.protocol.signature type → Option (model.Value type)

def published (_subject : Subject model art) (statement : art.Statement model) (type : Ty) (index : Nat) : Option (model.Value type) := do
  let position ← art.participant.policy.publicInputs.idxOf? index
  let values ← Zkc.Construction.Domain.encodeValues statement
  let value ← values[position]?
  Zkc.Construction.Domain.Value.decode type value

def publishedInputs (statement : art.Statement model) :
    (types : List Ty) → Nat → Values (Component model.Value) types
  | [], _ => .nil
  | type :: rest, index => .cons (subject.published statement type index)
      (publishedInputs statement rest (index + 1))

def boundary (statement : art.Statement model) :
    BoundaryValuation model.Value subject.target.owner.protocol.inputs subject.target.owner.protocol.outputs where
  inputs self := if subject.target.owner.protocol.roles[self]? = some art.participant.policy.validator
    then subject.publishedInputs statement _ 0 else Values.absent model.Value _
  outputs _ := Values.absent model.Value _

def assignments (statement : art.Statement model) (witness : subject.Witness) :
    LogicalAssignments model.Value subject.target.owner ⟨subject.target.owner.protocolIndex.val, []⟩ where
  parameters type selector := match selector.port with
    | .input ref => subject.published statement type ref.index
    | .output _ => none
  witnesses := witness

def Holds (statement : art.Statement model) (witness : subject.Witness) : Prop :=
  ∃ arguments, subject.target.application.read {} (subject.boundary statement)
      (subject.assignments statement witness) = some arguments ∧
    subject.target.formula.invokeRelationOn model arguments =
      .done (subject.target.booleanOutput.symm ▸ Values.cons true .nil)

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

def stageLinks : List Obligation :=
  [⟨"construction.checked", "admitted IR and selected dependent participant",
    subject.ConstructionChecked, .infrastructure⟩]

def stageLinkProofs (index : Fin subject.stageLinks.length) :
    Option (PLift (subject.stageLinks.get index).goal) := by
  match index with
  | ⟨0, _⟩ => exact some ⟨subject.constructionChecked⟩
  | ⟨n + 1, impossible⟩ => exact False.elim (by simp [stageLinks] at impossible)

end Subject
end ZkcSecurity.Claims.Domain
