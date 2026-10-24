import ZkcSecurity.Claims.Completeness

/-! Typed substitution and stage controls. These do not instantiate a new root
producer proof and cannot bypass the discovery candidate freeze. -/
set_option autoImplicit false
namespace TestsSecurity.HonestClaims
open Zkc.Claims Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair

variable {model : DomainModel} {original : Snapshot} {imported : Imported original}
  {selected : AuthoredPair.Selection original}

example (subject : Subject model original imported selected) :
    subject.reference.unitDigest = subject.originalExport := by rfl

example (subject : Subject model original imported selected) :
    subject.reference.artifacts =
      [⟨"producer", subject.producerExport⟩, ⟨"validator", subject.validatorExport⟩] := by rfl

-- Complete artifact equality is necessary, even if the substitute prints the
-- same source, candidate or protocol identifier.
example (actual : AuthoredPair.Artifacts)
    (different : actual ≠ selected.artifacts) : ¬ AuthoredPair.Admitted imported selected actual := by
  intro admitted
  exact different (AuthoredPair.admitted_artifacts admitted)

-- A changed producer cannot be supplied as evidence for the selected pair.
example (actual : AuthoredPair.Artifacts)
    (different : actual.producer ≠ selected.artifacts.producer) :
    ¬ AuthoredPair.Admitted imported selected actual := by
  intro admitted
  exact different (congrArg AuthoredPair.Artifacts.producer (AuthoredPair.admitted_artifacts admitted))

-- The honest input contract is read from this source. Replacing it with any
-- other contract prevents construction of the typed subject.
example (subject : Subject model original imported selected)
    (changed : AuthoredPair.InputContract) (different : changed ≠ selected.inputs) :
    AuthoredPair.inputContract original ≠ some changed := by
  intro substituted
  exact different (Option.some.inj (substituted.symm.trans subject.inputContractExact))

example (subject : Subject model original imported selected) (error : ENNReal) :
    (CompletenessRequest.mk (subject := subject) .interactive error).check = .error .stageMismatch := by
  rfl

example (subject : Subject model original imported selected) (error : ENNReal) :
    (CompletenessRequest.mk (subject := subject) .executableBytes error).check = .error .stageMismatch := by
  rfl

example (subject : Subject model original imported selected) (error : ENNReal) :
    (CompletenessRequest.mk (subject := subject) .compiledIdeal error).check = .ok () := by
  rfl

example (subject : Subject model original imported selected)
    (falseOnly : ∀ inputs, ¬ subject.HonestInput inputs) : ¬ Nonvacuous subject := by
  rintro ⟨inputs, _, honest⟩
  exact falseOnly inputs honest

example (subject : Subject model original imported selected)
    [∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
    (error : ENNReal) (falseOnly : ∀ inputs, ¬ subject.HonestInput inputs) :
    ¬ CanonicalCompleteness subject error := by
  rintro ⟨⟨inputs, _, honest⟩, _⟩
  exact falseOnly inputs honest

example : honestModelSchema ⟨honestModelIdentifier, [(some "private_coins", .natural 1)]⟩ =
    .error (.schema "honest private-uniform model accepts no arguments") := by rfl

example : resolveHonestModel ⟨[honestModelEntry]⟩ ⟨honestModelIdentifier, []⟩ =
    .ok .privateUniform := by rfl

-- Version zero is pinned by the export/dependency identity. A surface version
-- bump is not a substitute for that pin while the registry is still pre-v1.
example : honestModelIdentifier = ⟨"models.honest_fiat_shamir", 0⟩ := by rfl

example : resolveHonestModel ⟨[honestModelEntry]⟩
    ⟨⟨"models.honest_fiat_shamir", 0⟩, []⟩ = .ok .privateUniform := by rfl

example : resolveHonestModel ⟨[honestModelEntry]⟩
    ⟨⟨"models.honest_fiat_shamir", 1⟩, []⟩ =
    .error (.unknownIdentifier ⟨"models.honest_fiat_shamir", 1⟩) := by rfl

-- A same-name export with an undefined implementation fails complete-entry
-- association, independently of whether its key is recognized.
def undefinedModel : Export (Wire.Application → Except ResolutionError HonestExecutionModel) :=
  { honestModelEntry with definition := none }

example : ¬ HonestModelAdmission ⟨[undefinedModel]⟩ ⟨honestModelIdentifier, []⟩ := by
  intro admission
  have selected := admission.selected
  change Except.ok undefinedModel = Except.ok honestModelEntry at selected
  have definitions := congrArg Export.definition (Except.ok.inj selected)
  cases definitions

#print axioms ZkcSecurity.Claims.HonestPair.perfect_of_all_tables
#print axioms ZkcSecurity.Claims.HonestPair.not_perfect_of_failed_input
end TestsSecurity.HonestClaims
