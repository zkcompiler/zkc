module

public import ZkcSecurityExamples.TableMembership.Endpoint
public import ZkcSecurityTools.ClaimConstruction

@[expose] public section

/-! Fixed canonical compiled-ideal requests for the actual CheckMembership
pair. Registration selects the existing meanings before either theorem is used.
The soundness subject is the same pair's validator, without honest-input bounds. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace ZkcSecurity.Examples.TableMembership
open Zkc.Claims ZkcSecurity.Claims
open ZkcSecurity.Examples.TableMembership.Subject

namespace Completeness

def authority := CanonicalAuthority.authoredPair imported selected capabilities
def subject := ULift.up.{1} Subject.subject
def models : Registry authority.ModelExport := ⟨[authority.modelEntry ()]⟩
def properties := authority.properties models

def completeData : Wire.Request := {
  subject := subject.down.reference
  property := ⟨"completeness", 0⟩
  model := HonestPair.honestModelApplication
  target := subject.down.targetReference
  accept := subject.down.acceptance
  quantity := .scalar (.natural 0) }

def library : ZkcSecurity.Tools.ClaimConstruction.Library where
  subject := ``subject
  authority := some ``authority
  properties := ``properties
  models := ``models
  normalization := [``subject, ``authority, ``properties, ``models, ``capabilities]
  theoremMethods := [(⟨"fs.honest_completeness", 0⟩, ``Method.compiled_ideal_complete)]

claim_request completeData using library method
  (some (⟨⟨"fs.honest_completeness", 0⟩, []⟩ : Wire.Application))

end Completeness

namespace Soundness

abbrev subject := validatorSubject
def authority := CanonicalAuthority.domains validatorArtifacts capabilities
def modelContext (application : String) : ModelContext := ModelContext.parameter "application" application
def models (application : String) : Registry authority.ModelExport :=
  ⟨[authority.modelEntry (modelContext application)]⟩
def properties (application : String) := authority.properties (models application)

def soundData : Wire.Request := {
  subject := subject.reference
  property := ⟨"soundness", 0⟩
  model := ⟨exactUniform, [
    (some "level", .reference "levels.ideal"),
    (some "statement", .reference "statements.adaptive"),
    (some "oracle", .application "oracles.random" (some 0) [(none, .reference "construction.provider")]),
    (some "queries", .reference "Q"),
    (some "budget_symbol", .reference "Q"),
    (some "validator_cost", .natural 0),
    (some "application", .reference "application")]⟩
  target := subject.targetReference
  accept := subject.acceptance
  quantity := .scalar (.natural 0) }

def chargedData : Wire.Request := { soundData with quantity := .charged [] }

/-- The fixed request model remains universally quantified in its application.
Specializing before rational-to-ENNReal normalization keeps the zero-cost
dependent export visible to theorem application. Resolution checks this data
against the independently elaborated wire request. -/
def selectedModel (application : String) : Model :=
  ⟨.adaptive, .symbolic "Q", "Q", application, .constant 0,
    some ⟨"application", application, .parameter⟩⟩

theorem charged_meaning (application : String) :
    Domain.SoundnessArguments.meaning capabilities
      (⟨selectedModel application, .charged Method.schedule⟩ : Domain.SoundnessArguments subject) :=
  Endpoint.charged_meaning (selectedModel application) rfl (fun _ => by
    simp only [selectedModel, Bound.value, ennreal_nnrat_zero, Endpoint.validatorCost, Method.validatorCost])

def library : ZkcSecurity.Tools.ClaimConstruction.Library where
  subject := ``subject
  authority := some ``authority
  context := some ``modelContext
  properties := ``properties
  models := ``models
  normalization := [``authority, ``modelContext, ``properties, ``models, ``soundData]
  theoremNormalization := [``Endpoint.schedule, ``Endpoint.validatorCost, ``Endpoint.scalarBound,
    ``Method.schedule, ``Method.validatorCost, ``Method.scalarBound, ``Domain.ChargeSchedule.empty,
    ``selectedModel]
  theoremMethods := [(⟨"fs.keyed_soundness", 0⟩, ``Endpoint.scalar_meaning),
    (⟨"fs.keyed_charged", 0⟩, ``charged_meaning)]

claim_request soundData using library method
  (some (⟨⟨"fs.keyed_soundness", 0⟩, []⟩ : Wire.Application))
claim_request chargedData using library method
  (some (⟨⟨"fs.keyed_charged", 0⟩, []⟩ : Wire.Application))

end Soundness
end ZkcSecurity.Examples.TableMembership
