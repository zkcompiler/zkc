module

public import ZkcSecurity.Bindings.Subjects.HonestPair
public import ZkcSecurity.Bindings.Subjects.Domain
public import ZkcSecurity.Bindings.Transcript.DomainBinding

@[expose] public section

/-! A compiled pair and its adversarial verifier share one structural subject.
This projection reuses admission, source occurrences and the retained target.
It transfers no honest-input assumption or completeness proof to soundness.
Charge labels select checked occurrences before any evidence is supplied. -/
set_option autoImplicit false

namespace ZkcSecurity.Claims
open Zkc.Source Zkc.Source.Structured Zkc.Construction

namespace Domain.ChargeSite

/-- Resolve one source-selected label/native path against the actual verifier.
Ambiguity and missing occurrences refuse; no helper name or protocol dispatch
can supply a missing association proof. -/
def select {art : Endpoint.Domain.Artifacts} (compiled : Endpoint.Domain.Compiled art)
    (label native : String) : Except String (Domain.ChargeSite compiled) := do
  let [occurrence] := (Domain.challengeOccurrences art.participant.instructions).attach.filter
    (fun item => item.val.template.querySite? == some native)
    | throw "charge-occurrence"
  let [draw] := compiled.selection.context.draws.attach.filter (fun item => item.val.1 == native)
    | throw "charge-selection"
  if matched : occurrence.val.template.querySite? = some native then
    if selected : draw.val.1 = native then
      return {
        label, occurrence := occurrence.val, retained := occurrence.property,
        native, nativeMatched := matched,
        selected := ⟨draw.val.2, selected ▸ draw.property⟩ }
    else throw "charge-selection"
  else throw "charge-occurrence"

end Domain.ChargeSite

namespace HonestPair.Subject
variable {model : DomainModel} {original : Snapshot} {imported : Imported original}
  {selected : AuthoredPair.Selection original}

def validatorArtifacts (subject : Subject model original imported selected) : Endpoint.Domain.Artifacts :=
  ⟨original, selected.artifacts.validator, subject.selection.publics⟩

def validatorCompiled (subject : Subject model original imported selected) :
    Endpoint.Domain.Compiled subject.validatorArtifacts where
  imported := imported
  compiled := AuthoredPair.admitted_validator subject.admitted
  selection := subject.selection
  selected := subject.selectionExact
  checked := subject.selectionChecked
  publics := rfl
  occurrences := subject.validatorOccurrences
  sourceConnection := subject.validatorConnection

/-- Only the policy index changes along the admitted equality. The exact
source formula and selectors are retained. -/
def validatorTarget (subject : Subject model original imported selected) :
    RetainedTarget subject.validatorCompiled.imported selected.artifacts.validator.policy
      subject.validatorArtifacts.publics :=
  (AuthoredPair.admitted_validator_policy subject.admitted).symm ▸ subject.target

/-- Soundness's subject has no honest-input policy. Its meaning quantifies all
typed public statements, including those outside the producer's input domain. -/
def validatorSubject (subject : Subject model original imported selected)
    (sites : List (Domain.ChargeSite subject.validatorCompiled) := []) :
    Domain.Subject model subject.validatorArtifacts where
  compiled := subject.validatorCompiled
  target := subject.validatorTarget
  relations := subject.relations
  meaning := subject.target.transportMeaning
    (AuthoredPair.admitted_validator_policy subject.admitted).symm subject.meaning
  originalExport := subject.originalExport
  participantExport := subject.validatorExport
  sites := sites

@[simp] theorem validator_original (subject : Subject model original imported selected) :
    subject.validatorArtifacts.original = original := rfl

@[simp] theorem validator_artifact (subject : Subject model original imported selected) :
    subject.validatorArtifacts.participant = selected.artifacts.validator := rfl

@[simp] theorem validator_selection (subject : Subject model original imported selected) :
    subject.validatorCompiled.selection = subject.selection := rfl

/-- Honest and adversarial policies name exactly the same public coordinates.
The application remains arbitrary; equality with completeness uses originalExport. -/
theorem validatorCodec_eq (subject : Subject model original imported selected)
    (application : String) (statement : Values model.toCarriers.Value subject.selection.publics) :
    (FiatShamir.DomainReduction.policyCodec subject.validatorCompiled application).encode statement =
      Domain.PublicBinding.history application selected.policy.publicInputs statement
        subject.publicBindingArity subject.publicBindingData := by
  change Domain.PublicBinding.history application selected.artifacts.validator.policy.publicInputs
    statement _ _ = _
  simp only [AuthoredPair.admitted_validator_policy subject.admitted]

/-- Source/public alignment is inherited from the retained admitted Entry.
Absent private inputs keep their coordinates; missing public inputs refuse. -/
theorem publicProjection (subject : Subject model original imported selected)
    (inputs : subject.Inputs) (environment : Domain.Environment model.toCarriers)
    (projected : project (encodeInputs inputs) selected.policy.publicInputs = some environment) :
    ∃ statement : Values model.toCarriers.Value subject.selection.publics,
      Domain.encodeValues statement = some environment := by
  have publicTypes : subject.selection.publics = selected.policy.publicInputs.filterMap
      (subject.target.owner.protocol.inputs[·]?) := by
    rw [subject.target.entry]
    exact subject.target.publicTypes
  have arity : (selected.policy.publicInputs.filterMap
      (subject.target.owner.protocol.inputs[·]?)).length = selected.policy.publicInputs.length := by
    rw [← publicTypes]
    exact subject.publicBindingArity.symm
  have same : ∀ {types} (values : Values (Component model.toCarriers.Value) types),
      encodeInputs values = Domain.PublicBinding.optionalInputs values := by
    intro types values
    induction values with
    | nil => rfl
    | cons value rest ih => simp only [encodeInputs, Domain.PublicBinding.optionalInputs, ih]
  rw [same inputs] at projected
  rw [publicTypes]
  exact Domain.PublicBinding.project_statement inputs
    selected.policy.publicInputs environment arity projected

/-- Every actually prepared pair initializes the same source-owned typed game
as its adversarial verifier at the original export selected by the request.
Both ABI environments and the raw typed public projection are retained. -/
theorem runtimeInputs_binding (subject : Subject model original imported selected)
    (inputs : subject.Inputs) (actualProducer actualValidator : Domain.Environment model.toCarriers)
    (prepared : subject.runtimeInputs inputs = some (actualProducer, actualValidator)) :
    ∃ (statement : Values model.toCarriers.Value subject.selection.publics)
      (producer validator : Domain.Environment model.toCarriers),
      project (encodeInputs inputs) selected.policy.publicInputs = some validator ∧
      Domain.encodeValues statement = some validator ∧
      actualProducer = Domain.inputFrame subject.selection.context producer
        ((FiatShamir.DomainReduction.policyCodec subject.validatorCompiled subject.originalExport).encode statement) ∧
      actualValidator = Domain.inputFrame subject.selection.context validator
        ((FiatShamir.DomainReduction.policyCodec subject.validatorCompiled subject.originalExport).encode statement) := by
  simp only [validatorCodec_eq]
  cases interfaceFound : entryInterface original with
  | none => simp [runtimeInputs, interfaceFound] at prepared
  | some entry =>
      rcases entry with ⟨types, interface⟩
      cases producerFound : project (encodeInputs inputs)
          (dataInputs types interface.inputScopes selected.policy.producer) with
      | none => simp [runtimeInputs, interfaceFound, producerFound] at prepared
      | some producer =>
          cases validatorFound : project (encodeInputs inputs) selected.policy.publicInputs with
          | none => simp [runtimeInputs, interfaceFound, validatorFound] at prepared
          | some validator =>
              obtain ⟨statement, encoding⟩ := subject.publicProjection inputs validator validatorFound
              have binding := Domain.PublicBinding.fromEnvironment_encodeValues statement
                subject.originalExport selected.policy.publicInputs subject.publicBindingArity subject.publicBindingData encoding
              cases profile : subject.selection.context.profile with
              | plain =>
                  simp [runtimeInputs, interfaceFound, producerFound, validatorFound, profile] at prepared
                  refine ⟨statement, producer, validator, rfl, encoding, ?_, ?_⟩
                  · simpa only [Domain.inputFrame, profile] using prepared.1.symm
                  · simpa only [Domain.inputFrame, profile] using prepared.2.symm
              | fiatShamir replacement =>
                  simp [runtimeInputs, interfaceFound, producerFound, validatorFound, profile, binding] at prepared
                  exact ⟨statement, producer, validator, rfl, encoding,
                    prepared.1.symm, prepared.2.symm⟩

end HonestPair.Subject
end ZkcSecurity.Claims
