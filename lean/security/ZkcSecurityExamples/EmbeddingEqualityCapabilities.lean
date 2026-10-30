module

public import ZkcSecurityExamples.EmbeddingEqualityDomains
public import ZkcSecurity.Claims.DomainModel

@[expose] public section

/-! Capabilities of the actual exported catalogue. The regenerated field rows agree
with the installed model catalogue. Lookup equality transports the existing
laws without replacing the snapshot or its interpretation. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Examples.EmbeddingEqualityCapabilities
open Zkc.Source.Structured
open ZkcSecurity.Domains.KoalaBearModel
open ZkcExamples.Construction.EmbeddingEqualityData

theorem find_source (identity : String) :
    snapshot.catalogue.find identity = catalogue.find identity := rfl

theorem expect_source (identity : String) (sort : DomainSort) :
    snapshot.catalogue.expect identity sort = catalogue.expect identity sort := by
  unfold Catalogue.expect
  rw [find_source]

theorem require_source (identity : String) (sort : DomainSort) (capability : String) :
    snapshot.catalogue.require identity sort capability = catalogue.require identity sort capability := by
  unfold Catalogue.require
  rw [expect_source]

theorem embedding_source (extension base : String) :
    snapshot.catalogue.requireEmbedding extension base = catalogue.requireEmbedding extension base := by
  unfold Catalogue.requireEmbedding
  simp only [expect_source]

theorem action_source (group field : String) :
    snapshot.catalogue.requireScale group field = catalogue.requireScale group field := by
  unfold Catalogue.requireScale
  rw [expect_source]

theorem algebra : DomainLaws snapshot.catalogue model where
  field identity admitted := laws.field identity ((require_source _ _ _).symm.trans admitted)
  inverse := laws.inverse
  embedding extension base admitted := laws.embedding extension base
    ((embedding_source _ _).symm.trans admitted)
  action group field admitted := laws.action group field ((action_source _ _).symm.trans admitted)

theorem characteristic : CharacteristicLaws snapshot.catalogue model.toFieldModel := by
  intro identity row admitted
  exact characteristic_laws identity row ((expect_source _ _).symm.trans admitted)

def capabilities : Claims.Domain.Capabilities model snapshot where
  algebra := algebra
  characteristic := characteristic
  finite identity _ := EmbeddingEqualityDomains.finite identity
  samples := EmbeddingEqualityDomains.rawSampleable

theorem canonical_base_cardinality : capabilities.cardinality baseIdentity =
    .ok ZkcSecurity.Domains.KoalaBear.q := by
  simp only [Claims.Domain.Capabilities.cardinality]
  simp only [show snapshot.catalogue.identitySort baseIdentity = some .field from rfl,
    ↓reduceDIte]
  exact congrArg Except.ok ZkcSecurity.Domains.KoalaBear.card_base

theorem canonical_octic_cardinality : capabilities.cardinality octicIdentity =
    .ok (ZkcSecurity.Domains.KoalaBear.q ^ 8) := by
  simp only [Claims.Domain.Capabilities.cardinality]
  simp only [show snapshot.catalogue.identitySort octicIdentity = some .field from rfl,
    ↓reduceDIte]
  exact congrArg Except.ok ZkcSecurity.Domains.KoalaBear.card_octic

theorem canonical_octic_bound : Claims.Bound.elaborateWith capabilities.cardinality "Q"
    (.application "cardinality" none [(none, .reference octicIdentity)]) =
      .ok (.constant (ZkcSecurity.Domains.KoalaBear.q ^ 8)) := by
  simp [Claims.Bound.elaborateWith, Claims.Numeric.nonnegativeWith_cardinality
    capabilities.cardinality octicIdentity _ canonical_octic_cardinality]

end ZkcSecurity.Examples.EmbeddingEqualityCapabilities
