import Zkc.Source.Structured.DomainLaws
import Zkc.Source.Structured.DomainEvaluation

/-! Admission and operation-coherence controls. These do not assert that the
uniform interpretation realizes an extension's native representation. -/

set_option autoImplicit false
namespace Tests.DomainLaws
open Zkc.Source.Structured

def catalogue : Catalogue where
  nominals := [
    ⟨"base", .field, [], ["CommRing", "Field"], some 3⟩,
    ⟨"extension", .field, [("BaseField", "base")],
      ["CommRing", "Field", "ExtensionField"], some 3⟩,
    ⟨"other", .field, [], ["CommRing", "Field"], some 5⟩,
    ⟨"wrong", .field, [("BaseField", "base")],
      ["CommRing", "Field", "ExtensionField"], some 5⟩,
    ⟨"ring", .field, [], ["CommRing"], none⟩]
  services := []

example : catalogue.check = .ok () := by decide
example : catalogue.requireEmbedding "extension" "base" = .ok () := by decide
example : catalogue.requireEmbedding "base" "extension" =
    .error "structured-domain-capability" := by decide
example : catalogue.requireEmbedding "extension" "other" =
    .error "structured-domain-member" := by decide
example : catalogue.requireEmbedding "wrong" "base" =
    .error "structured-domain-modulus" := by decide
example : catalogue.requireEmbedding "missing" "base" =
    .error "structured-domain-unknown" := by decide
example : catalogue.require "ring" .field "CommRing" = .ok () := by decide
example : catalogue.require "ring" .field "Field" =
    .error "structured-domain-capability" := by decide

example {B E : Type} [CommRing B] [CommRing E] [Nontrivial E] :
    ¬ EmbeddingLaw (fun _ : B => (0 : E)) := EmbeddingLaw.not_zero

/-- The direct mixed-domain verifier's algebra, for arbitrary message/challenge.
The endpoint must additionally bind this predicate to its actual Process. -/
theorem equality_of_two_checks {B E : Type} [Field B] [CommRing E] [Nontrivial E]
    {embed : B → E} (law : EmbeddingLaw embed) (a b : B) (u c : E)
    (left : u + c = embed a + c) (right : u + c = embed b + c) : a = b := by
  apply law.injective
  exact (add_right_cancel left).symm.trans (add_right_cancel right)

/-- The field instance used in a proof has exactly the evaluator's arithmetic. -/
example (model : DomainModel) (laws : DomainLaws catalogue model) (d : String)
    (admitted : catalogue.require d .field "Field" = .ok ())
    (x y : model.Field d) :
    let _ := laws.fieldInstance d admitted
    Evaluation.operationOn model SiteObservations.closed [] (.fieldMultiply d)
      (.cons x (.cons y .nil)) .nil = .done (.cons (x * y) .nil) := by
  rfl

end Tests.DomainLaws
