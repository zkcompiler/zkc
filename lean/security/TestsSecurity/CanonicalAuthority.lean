import ZkcSecurity.Claims.Canonical

/-! Closed authority controls. These check association, supported shapes and
request policy; they supply no concrete protocol root theorem. -/
set_option autoImplicit false
namespace TestsSecurity.CanonicalAuthority
open Zkc.Claims Zkc.Source.Structured Zkc.Construction ZkcSecurity.Claims

section Domain
variable {model : DomainModel} (art : ZkcSecurity.Endpoint.Domain.Artifacts)
  (capabilities : Domain.Capabilities model art.original)

example : ((CanonicalAuthority.domains art capabilities).propertyEntry ⟨[]⟩ .completeness).definition = none := rfl
example : ((CanonicalAuthority.domains art capabilities).propertyEntry ⟨[]⟩ .knowledge).definition = none := rfl
example : ((CanonicalAuthority.domains art capabilities).propertyEntry ⟨[]⟩ .specialSoundness).definition = none := rfl
example : (CanonicalAuthority.domains art capabilities).product = "certified_verifier" := rfl

example (subject : Domain.Subject model art) :
    (CanonicalAuthority.domains art capabilities).links subject = subject.stageLinks := rfl

example (subject : Domain.Subject model art) :
    SourceOccurrences.check art.original subject.compiled.selection.context art.participant = .ok () :=
  subject.constructionChecked.2.2.2.2

example (identity : String) (admitted : art.original.catalogue.identitySort identity = some .field) :
    capabilities.cardinality identity =
      .ok (@Fintype.card (model.Field identity) (capabilities.finite identity admitted)) := by
  simp [Domain.Capabilities.cardinality, admitted]

example (identity : String) (unsupported : art.original.catalogue.identitySort identity ≠ some .field) :
    capabilities.cardinality identity = .error ⟨["unsupported or unadmitted finite field: " ++ identity]⟩ := by
  simp [Domain.Capabilities.cardinality, unsupported]

def adaptiveModel : Wire.Application :=
  ⟨exactUniform, [(some "statement", .reference "statements.adaptive"),
    (some "application", .reference "application") ]⟩

example (application : String) :
    Domain.modelSchema capabilities (.parameter "application" application) adaptiveModel =
      .ok (.ok ⟨.adaptive, .symbolic "budgets.queries", "budgets.queries", application,
        .constant 0, some ⟨"application", application, .parameter⟩⟩) := rfl

example : Domain.modelSchema capabilities .empty adaptiveModel =
    .error (.schema "unbound application context: application") := rfl

example (subject : Domain.Subject model art) (selected : Model) :
    Domain.chargeSchedule capabilities subject selected [] =
      .ok (.error ⟨["nonempty charge schedule"]⟩) := rfl

example (subject : Domain.Subject model art) (selected : Model)
    (empty : subject.sites = []) :
    Domain.chargeSchedule capabilities subject selected [("unregistered", .natural 1)] =
      .error (.siteMismatch "unregistered") := by
  simp [Domain.chargeSchedule, Domain.selectChargeSites, empty]

example (subject : Domain.Subject model art) (selected : Model) (error : ZkcSecurity.Claims.Bound) :
    Domain.SoundnessArguments.meaning capabilities
      (⟨{ selected with form := .adaptive }, .scalar error⟩ : Domain.SoundnessArguments subject) =
        Domain.AdaptiveSoundness capabilities subject { selected with form := .adaptive } error.value := rfl

example (subject : Domain.Subject model art) (selected : Model) (schedule : Domain.ChargeSchedule subject) :
    Domain.SoundnessArguments.meaning capabilities
      (⟨{ selected with form := .adaptive }, .charged schedule⟩ : Domain.SoundnessArguments subject) =
        (letI := capabilities.samples;
          Domain.WeightedAdaptiveSoundness capabilities subject { selected with form := .adaptive } schedule ∧
          ∀ queries, selected.queries.allows queries →
            Nonempty (Domain.ChargedExport subject schedule queries (selected.validatorCost.value queries))) := rfl
end Domain

section Pair
variable {model : DomainModel} {original : Snapshot} (imported : Imported original)
  (selected : Zkc.Construction.AuthoredPair.Selection original)
  (capabilities : Domain.Capabilities model original)

example : ((CanonicalAuthority.authoredPair imported selected capabilities).propertyEntry ⟨[]⟩ .soundness).definition = none := rfl
example : ((CanonicalAuthority.authoredPair imported selected capabilities).propertyEntry ⟨[]⟩ .knowledge).definition = none := rfl
example : ((CanonicalAuthority.authoredPair imported selected capabilities).propertyEntry ⟨[]⟩ .specialSoundness).definition = none := rfl
example : (CanonicalAuthority.authoredPair imported selected capabilities).product = "compiled_ideal_completeness" := rfl

example (subject : HonestPair.CanonicalSubject model original imported selected) :
    (CanonicalAuthority.authoredPair imported selected capabilities).links subject = subject.down.stageLinks := rfl

example (subject : HonestPair.CanonicalSubject model original imported selected) (error : ℚ≥0) :
    (HonestPair.completenessProperty capabilities ⟨[]⟩).meaning subject (.ok error) =
      .ok (@HonestPair.CanonicalCompleteness model original imported selected
        subject.down capabilities.samples (error : ENNReal)) := rfl
end Pair

def unrelatedModel : Export HonestPair.ModelExport :=
  ⟨⟨"example.unrelated", 0⟩, "example/0", none⟩

example : HonestPair.resolveModel ⟨[unrelatedModel, HonestPair.modelEntry]⟩
    ⟨HonestPair.honestModelIdentifier, []⟩ = .ok .privateUniform := rfl

example : HonestPair.resolveModel ⟨[HonestPair.modelEntry, HonestPair.modelEntry]⟩
    ⟨HonestPair.honestModelIdentifier, []⟩ = .error (.conflict HonestPair.honestModelIdentifier) := rfl

example : HonestPair.resolveModel ⟨[HonestPair.modelEntry]⟩
    ⟨HonestPair.honestModelIdentifier, [(some "queries", .natural 1)]⟩ =
      .error (.schema "honest private-uniform model accepts no arguments") := rfl

def undefinedModel : Export HonestPair.ModelExport := { HonestPair.modelEntry with definition := none }

example {model : DomainModel} {original : Snapshot} (imported : Imported original)
    (selected : Zkc.Construction.AuthoredPair.Selection original)
    (capabilities : Domain.Capabilities model original)
    (subject : HonestPair.CanonicalSubject model original imported selected) :
    ¬ CanonicalModelAdmission (CanonicalAuthority.authoredPair imported selected capabilities)
      ⟨[undefinedModel]⟩ () subject ⟨HonestPair.honestModelIdentifier, []⟩ := by
  intro admission
  have same := admission.selected
  change Except.ok undefinedModel = Except.ok HonestPair.modelEntry at same
  have definitions := congrArg Export.definition (Except.ok.inj same)
  cases definitions

example {S : Type 1} {authority : ZkcSecurity.Claims.CanonicalAuthority S}
    {registry : Registry authority.ModelExport} {context : authority.Context}
    {subject : S} {application : Wire.Application}
    (admitted : CanonicalModelAdmission authority registry context subject application) :
    authority.resolveModel registry subject application = authority.modelMeaning context subject application :=
  admitted.canonical_resolution

def policy : HonestPair.InputPolicy [.index] := ⟨[.boundedIndex .here 12]⟩

example : policy.checkParameters policy.parameters = .ok () := policy.parameters_checked
example : policy.checkParameters none =
    .error (.schema "honest input policy does not match the typed request") := rfl
example : policy.checkParameters
    (some (.application "honest.input_policy" (some 0) [(some "rules", .list
      [.application "honest.bounded_index" (some 0)
        [(some "input", .natural 0), (some "maximum", .natural 13)]])])) =
      .error (.schema "honest input policy does not match the typed request") := rfl

example : reservedIdentifier ⟨"completeness", 9⟩ = true := rfl
example : reservedIdentifier ⟨"soundness", 9⟩ = true := rfl

end TestsSecurity.CanonicalAuthority
