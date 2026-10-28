import ZkcTools.StructuredSource.ReferenceInstallation
import Zkc.Source.Structured.MultilinearReferenceInstallation
import ZkcExamples.Structured.MultilinearSourceBindings
import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs

/-! The same body certificates and mathematical installation serve both actual
admitted source libraries. The only instance work is this source selection. -/
set_option autoImplicit false
namespace Tests.MultilinearReferences
open Zkc.Source Zkc.Source.Structured
open ReferenceLibrary.Multilinear
open ZkcExamples.Structured.Generated.Bindings

inductive RetainedSource | small | twoSums

noncomputable def source : RetainedSource → Program
  | .small => SmallSumcheckInputs.imported.program
  | .twoSums => TwoSumsInputs.imported.program

abbrev bindings := ZkcExamples.Structured.MultilinearSourceBindings.sumcheck

/-- One selection proof; every complete typed body is checked independently. -/
theorem bodies (selected : RetainedSource) :
    Bodies (source selected).payload.definitions "bls12-381.fr" bindings := by
  cases selected <;> select_reference_bodies

variable (model : DomainModel) (selected : RetainedSource)

theorem actual_metadata (xs : List (model.Field "bls12-381.fr")) (n w : Nat) :
    invoke (closed model (definitions := (source selected).payload.definitions))
      ⟨bindings.dimension, .math, triple "bls12-381.fr", [.index]⟩
      (tableValues model "bls12-381.fr" xs n w) = .done (.cons n .nil) ∧
    invoke (closed model (definitions := (source selected).payload.definitions))
      ⟨bindings.width, .math, triple "bls12-381.fr", [.index]⟩
      (tableValues model "bls12-381.fr" xs n w) = .done (.cons w .nil) :=
  ⟨dimension_eq model (source selected).payload.linked (bodies selected) xs n w,
    width_eq model (source selected).payload.linked (bodies selected) xs n w⟩

theorem actual_restriction (xs : List (model.Field "bls12-381.fr")) (n w : Nat)
    (r : model.Field "bls12-381.fr") (bound : xs.length < indexLimit)
    (small : n < 64) (width : 0 < w) (shape : xs.length = 2 ^ n * w) :
    invoke (closed model (definitions := (source selected).payload.definitions))
      (firstHelper "bls12-381.fr" bindings) (.cons xs (.cons n (.cons w (.cons r .nil)))) =
      primitiveOutcome (firstOutcome model "bls12-381.fr" (.cons xs (.cons n (.cons w (.cons r .nil))))) :=
  first_eq model (source selected).payload.linked (bodies selected) xs n w r bound small width shape

theorem actual_prefix (xs point : List (model.Field "bls12-381.fr")) (n w : Nat)
    (bound : xs.length < indexLimit) (small : n < 64) (width : 0 < w)
    (shape : xs.length = 2 ^ n * w) :
    invoke (closed model (definitions := (source selected).payload.definitions))
      ⟨bindings.fold, .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index],
        triple "bls12-381.fr"⟩ (.cons point (.cons xs (.cons n (.cons w .nil)))) =
      primitiveOutcome (prefixOutcome model "bls12-381.fr" xs point n w) :=
  fold_eq model (source selected).payload.linked (bodies selected) xs point n w bound small width shape

theorem actual_sums (xs : List (model.Field "bls12-381.fr")) (n w : Nat) :
    invoke (closed model (definitions := (source selected).payload.definitions))
      ⟨bindings.sums, .local, triple "bls12-381.fr", [.field "bls12-381.fr", .field "bls12-381.fr"]⟩
      (tableValues model "bls12-381.fr" xs n w) =
      primitiveOutcome ((sums model "bls12-381.fr" bindings).reference
        (tableValues model "bls12-381.fr" xs n w)) :=
  sums_eq model (source selected).payload.linked (bodies selected) xs n w

#print axioms actual_restriction
#print axioms actual_metadata
#print axioms actual_prefix
#print axioms actual_sums
#print axioms bodies
#print axioms ReferenceLibrary.Multilinear.fold
#print axioms ReferenceLibrary.Multilinear.first
end Tests.MultilinearReferences
