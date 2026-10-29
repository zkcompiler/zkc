module

public import ZkcSecurity.Claims.Completeness
public import ZkcSecurity.Claims.DomainModel
public import ZkcSecurity.Claims.Parameters

@[expose] public section

/-! Fixed wire adapter for compiled honest pairs. This uses the exact honest
model and source-owned input/target meanings; it introduces no adversary Q. -/
set_option autoImplicit false
namespace ZkcSecurity.Claims.HonestPair
open Zkc.Claims Zkc.Source.Structured Zkc.Construction

variable {model : DomainModel} {original : Snapshot} {imported : Imported original}
  {selected : Zkc.Construction.AuthoredPair.Selection original}

/-- Only a universe lift: canonical pair receipts retain the actual owner subject. -/
abbrev CanonicalSubject (model : DomainModel) (original : Snapshot) (imported : Imported original)
    (selected : Zkc.Construction.AuthoredPair.Selection original) :=
  ULift.{1} (Subject model original imported selected)

/-- Named payload preserves the owner's exact honest schema at the common universe. -/
structure ModelExport : Type 1 where
  elaborate : Wire.Application → Except ResolutionError HonestExecutionModel

abbrev ModelRegistry := Registry ModelExport

def modelEntry : Export ModelExport :=
  ⟨honestModelEntry.identifier, honestModelEntry.schema, some ⟨honestModelSchema⟩⟩

def resolveModel (registry : ModelRegistry) (application : Wire.Application) :
    Except ResolutionError HonestExecutionModel :=
  match registry.lookup application.identifier with
  | .error error => .error error
  | .ok entry => match entry.definition with
    | none => .error (.schema "undefined honest model")
    | some payload => payload.elaborate application

namespace Subject
def acceptance (subject : Subject model original imported selected) : Wire.Acceptance :=
  ⟨true, selected.policy.acceptance, subject.selection.context.validator, []⟩

def check (subject : Subject model original imported selected) (request : Wire.Request) :
    Except ResolutionError Unit := do
  if request.subject != subject.reference then throw .subjectMismatch
  if !request.target.matches subject.targetReference then throw .targetMismatch
  if request.accept != subject.acceptance then throw .acceptanceMismatch

def PairChecked (_subject : Subject model original imported selected) : Prop :=
  Zkc.Construction.AuthoredPair.Admitted imported selected selected.artifacts

def SourceChecked (subject : Subject model original imported selected) : Prop :=
  subject.target.owner.clause subject.target.clauseIndex = selected.target ∧
  Zkc.Construction.AuthoredPair.inputContract original = some selected.inputs ∧
  selected.inputs.clauses = subject.target.owner.contract.clauses.filter (·.kind == .input) ∧
  selected.inputs.preconditions = []

def ValidatorChecked (subject : Subject model original imported selected) : Prop :=
  select imported selected.artifacts.validator = some subject.selection ∧
  subject.selection.check imported selected.artifacts.validator = true

def OccurrencesChecked (subject : Subject model original imported selected) : Prop :=
  SourceOccurrences.check original subject.selection.context selected.artifacts.producer = .ok () ∧
  SourceOccurrences.check original subject.selection.context selected.artifacts.validator = .ok ()

/-- Keep each stage proposition indexed by the complete actual pair subject
before reducing its independently selected connection meaning. -/
def ProducerConnectionChecked (subject : Subject model original imported selected) : Prop :=
  ConnectionAdmission.Required imported.program subject.selection.context
    .producer selected.artifacts.producer

def ValidatorConnectionChecked (subject : Subject model original imported selected) : Prop :=
  ConnectionAdmission.Required imported.program subject.selection.context
    .validator selected.artifacts.validator

def stageLinks (subject : Subject model original imported selected) : List Obligation :=
  [⟨"pair.checked", "exact source, policy, producer and validator", subject.PairChecked, .infrastructure⟩,
   ⟨"pair.source", "retained target and honest input selection", subject.SourceChecked, .infrastructure⟩,
   ⟨"construction.checked", "admitted selected validator", subject.ValidatorChecked, .infrastructure⟩,
   ⟨"pair.occurrences", "exact producer and validator source occurrences", subject.OccurrencesChecked, .infrastructure⟩,
   ⟨"pair.producer_connection", "complete source-to-producer correspondence",
    subject.ProducerConnectionChecked, .infrastructure⟩,
   ⟨"pair.validator_connection", "complete source-to-validator correspondence",
    subject.ValidatorConnectionChecked, .infrastructure⟩]

def stageLinkProofs (subject : Subject model original imported selected)
    (index : Fin subject.stageLinks.length) : Option (PLift (subject.stageLinks.get index).goal) := by
  match index with
  | ⟨0, _⟩ => exact some ⟨subject.admitted⟩
  | ⟨1, _⟩ => exact some ⟨subject.targetExact, subject.inputContractExact,
      subject.inputClausesExact, subject.preconditionsEmpty⟩
  | ⟨2, _⟩ => exact some ⟨subject.selectionExact, subject.selectionChecked⟩
  | ⟨3, _⟩ => exact some ⟨subject.producerOccurrences, subject.validatorOccurrences⟩
  | ⟨4, _⟩ => exact subject.producerConnection
  | ⟨5, _⟩ => exact subject.validatorConnection
  | ⟨n + 6, impossible⟩ => exact False.elim (by simp [stageLinks] at impossible)
end Subject

/-- Apply the same conservative dependency rule as soundness to every source
input formula and the selected target. No input policy is read from a request. -/
def checkHonestRelations (subject : Subject model original imported selected) :
    Except ResolutionError Unit := do
  checkRetainedMeaning subject.meaning
  for index in List.finRange subject.target.owner.contract.clauses.length do
    if isInput : (subject.target.owner.clause index).kind = .input then
      checkRetainedMeaning (subject.inputMeanings index isInput).meaning

def completenessArguments (capabilities : Domain.Capabilities model original)
    (registry : ModelRegistry) (request : Wire.Request)
    (subject : Subject model original imported selected) : Except ResolutionError (Except Incomplete ℚ≥0) := do
  subject.check request
  let _ ← completenessParameters.decode request.parameters
  checkHonestRelations subject
  if !request.capabilities.isEmpty then
    throw (.schema "compiled completeness accepts no capabilities")
  let _ ← resolveModel registry request.model
  match request.quantity with
  | .scalar expression => return Numeric.nonnegativeWith capabilities.cardinality expression
  | _ => throw (.schema "compiled completeness requires a scalar error quantity")

noncomputable def completenessProperty (capabilities : Domain.Capabilities model original)
    (registry : ModelRegistry) : PropertyExport (CanonicalSubject model original imported selected) where
  Arguments _ := Except Incomplete ℚ≥0
  elaborate request subject := completenessArguments capabilities registry request subject.down
  meaning subject arguments := arguments.map fun error =>
    @CanonicalCompleteness model original imported selected subject.down capabilities.samples (error : ENNReal)
  requiredLinks subject _ := subject.down.stageLinks

end ZkcSecurity.Claims.HonestPair
