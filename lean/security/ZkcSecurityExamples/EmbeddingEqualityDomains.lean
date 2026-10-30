module

public import ZkcExamples.Construction.EmbeddingEqualityData
public import Zkc.Construction.DomainTranscript
public import ZkcSecurity.Bindings.Models.KoalaBearModel
public import ZkcSecurity.Claims.Model

@[expose] public section

/-! Domain-selected numeric and sampling data for the equality endpoint.
Cardinality is computed from the actual carrier; characteristic remains q in
both fields. Unsupported identities still refuse in the numeric elaborator. -/
set_option autoImplicit false

namespace ZkcSecurity.Examples.EmbeddingEqualityDomains
open Zkc.Source Zkc.Source.Structured Zkc.Claims
open ZkcSecurity.Domains.KoalaBearModel
open ZkcSecurity.Domains.KoalaBear (q Base Octic)
open ZkcExamples.Construction.EmbeddingEqualityData

abbrev finite (identity : String) : Fintype (model.Field identity) := by
  change Fintype (carrier (resolve identity))
  cases resolve identity <;> dsimp [carrier] <;> infer_instance

noncomputable abbrev sampleable (identity : String) : SampleableType (model.Field identity) := by
  letI := finite identity
  letI := model.fieldRing identity
  exact SampleableType.ofFintype _

noncomputable abbrev rawSampleable : (event : Zkc.Construction.Domain.Event model.toCarriers) →
    SampleableType (Zkc.Construction.Domain.Raw event)
  | .challenge origin => by
      cases origin with
      | mk entry event request =>
        cases request with
        | none => exact inferInstanceAs (SampleableType Unit)
        | some request =>
          cases request with
          | mk method parameters sort =>
            cases sort
            case field identity => exact sampleable identity
            all_goals exact inferInstanceAs (SampleableType Unit)
  | .message .. | .publicBinding .. => inferInstanceAs (SampleableType Unit)

def cardinality := Claims.Numeric.cardinalityOn model.toCarriers finite snapshot

theorem base_numeric : cardinality baseIdentity = .ok q := by
  exact (Claims.Numeric.cardinalityOn_field _ _ _ _ (by decide)).trans
    (congrArg Except.ok ZkcSecurity.Domains.KoalaBear.card_base)

theorem octic_numeric : cardinality octicIdentity = .ok (q ^ 8) := by
  exact (Claims.Numeric.cardinalityOn_field _ _ _ _ (by decide)).trans
    (congrArg Except.ok ZkcSecurity.Domains.KoalaBear.card_octic)

theorem normalize_octic : Claims.Numeric.normalizeWith cardinality
    (.application "cardinality" none [(none, .reference octicIdentity)]) =
      .ok (.natural (q ^ 8)) := by
  simp [Claims.Numeric.normalizeWith, octic_numeric]

theorem bound_octic : Claims.Bound.elaborateWith cardinality "Q"
    (.application "cardinality" none [(none, .reference octicIdentity)]) =
      .ok (.constant (q ^ 8)) := by
  simp [Claims.Bound.elaborateWith, Claims.Numeric.nonnegativeWith_cardinality
    cardinality octicIdentity (q ^ 8) octic_numeric]

theorem characteristic_base : CharP (model.Field baseIdentity) q := base_characteristic
theorem characteristic_octic : CharP (model.Field octicIdentity) q := octic_characteristic

theorem cardinality_not_characteristic : (q ^ 8 : Nat) ≠ q := by norm_num

theorem zero_embedding_refused : ¬ EmbeddingLaw (fun _ : Base => (0 : Octic)) :=
  EmbeddingLaw.not_zero

end ZkcSecurity.Examples.EmbeddingEqualityDomains
