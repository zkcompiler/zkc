import Zkc.Claims.Interactive
import ZkcExamples.Structured.SchnorrBinding

/-! Interactive requests retain their actual admitted clause and Boolean
acceptance. Registered but unavailable models produce an explicit incomplete
result, while unknown versions and wrong selectors fail resolution. -/

set_option autoImplicit false
namespace Tests.ClaimsInteractive
open Zkc.Claims
open ZkcExamples.Structured

private def subject : InteractiveSubject where
  reference := ⟨SchnorrInteractiveData.snapshot.source,
    SchnorrInteractiveData.snapshot.entry, .interactive, []⟩
  interactive := rfl
  noArtifacts := rfl
  snapshot := SchnorrInteractiveData.snapshot
  imported := SchnorrInteractive.imported
  owner := SchnorrBinding.owner
  entry := SchnorrBinding.owner_is_entry
  clauseIndex := SchnorrBinding.clauseIndex
  target := SchnorrBinding.exact_clause.1
  acceptancePort := ⟨0, by decide +kernel⟩
  acceptanceRole := ⟨1, by decide +kernel⟩
  boolean := rfl
  decision := rfl

private def request : Wire.Request where
  subject := subject.reference
  property := ⟨"special_soundness", 0⟩
  model := ⟨⟨"models.interactive", 0⟩, []⟩
  target := subject.targetReference
  accept := subject.acceptance
  quantity := .scalar (.natural 0)

private def models : Registry Unit :=
  ⟨[⟨⟨"models.interactive", 0⟩, "zkc.model.interactive/0", none⟩]⟩

example : InteractiveSubject.resolveRequest models subject request =
    .ok (.error ⟨["special_soundness@0"]⟩) := rfl
example : InteractiveSubject.resolveRequest models subject
    { request with property := ⟨"completeness", 0⟩ } =
    .ok (.error ⟨["completeness@0"]⟩) := rfl
example : InteractiveSubject.resolveRequest models subject
    { request with property := ⟨"special_soundness", 1⟩ } =
    .error (.unknownIdentifier ⟨"special_soundness", 1⟩) := rfl
example : InteractiveSubject.resolveRequest models subject
    { request with accept := ⟨true, 1, 1, []⟩ } =
    .error .acceptanceMismatch := rfl
example : InteractiveSubject.resolveRequest models subject
    { request with model := ⟨⟨"models.interactive", 1⟩, []⟩ } =
    .error (.unknownIdentifier ⟨"models.interactive", 1⟩) := rfl

end Tests.ClaimsInteractive
