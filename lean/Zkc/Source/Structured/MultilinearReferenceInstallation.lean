module

public import Zkc.Source.Structured.MultilinearReference
public import Zkc.Source.TypedABI

@[expose] public section

/-! One body-selection record installs a complete dependency chain into any
linked source library. There are no instance-specific lookup or ABI equations.
All mathematical premises are discharged here or remain explicit caller inputs. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Zkc.Source.Structured.ReferenceLibrary.Multilinear
open Zkc.Source MultilinearBodies Zkc.Polynomial.Multilinear

attribute [local implicit_reducible] Op.arguments Op.results Op.regions DomainSpec.elements

structure Bodies (definitions : List CheckedDefinition) (domain : String) (bindings : Bindings) : Prop where
  less : BodyIn definitions (lessHelper bindings) (lessBody domain bindings)
  halves : BodyIn definitions (halvesHelper domain bindings) (halvesBody domain bindings)
  interpolate : BodyIn definitions
    ⟨bindings.interpolate, .math, [.field domain, .field domain, .field domain], [.field domain]⟩
    (interpolateBody domain bindings)
  interpolation : BodyIn definitions
    ⟨bindings.interpolation, .local, [.field domain, .field domain, .field domain], [.field domain]⟩
    (interpolateRealizationBody domain bindings)
  callback : BodyIn definitions (collectSpec domain bindings).bodyHelper (mapCallbackBody domain bindings)
  collect : BodyIn definitions (mapHelper domain bindings) (mapBody domain bindings)
  first : BodyIn definitions (firstHelper domain bindings) (firstBody domain bindings)
  step : BodyIn definitions ⟨bindings.step, .local, firstInputs domain, triple domain⟩
    (stepBody domain bindings)
  foldStep : BodyIn definitions (foldSpec domain bindings).stepHelper (foldStepBody domain bindings)
  fold : BodyIn definitions ⟨bindings.fold, .local,
    [.vector domain, .vector domain, .index, .index], triple domain⟩ (foldBody domain bindings)
  sums : BodyIn definitions ⟨bindings.sums, .local, triple domain, [.field domain, .field domain]⟩
    (sumsBody domain bindings)
  foldWrapper : BodyIn definitions
    ⟨bindings.foldWrapper, .local, [.vector domain, .index, .index, .vector domain], triple domain⟩
    (foldWrapperBody domain bindings)
  restrictionPrefix : BodyIn definitions
    ⟨bindings.restrictPrefix, .local, [.vector domain, .index, .index, .vector domain], triple domain⟩
    (prefixBody domain bindings)
  values : BodyIn definitions ⟨bindings.values, .math, triple domain, [.vector domain]⟩
    (.ret (.cons .here .nil))
  dimension : BodyIn definitions ⟨bindings.dimension, .math, triple domain, [.index]⟩
    (.ret (.cons (.there .here) .nil))
  width : BodyIn definitions ⟨bindings.width, .math, triple domain, [.index]⟩
    (.ret (.cons (.there (.there .here)) .nil))
  valuesRealization : BodyIn definitions
    ⟨bindings.valuesRealization, .local, triple domain, [.vector domain]⟩
    (.letOp (.invoke ⟨bindings.values, .math, triple domain, [.vector domain]⟩)
      (Operands.identity _) .nil (.ret (.cons .here .nil)))

variable {definitions : List CheckedDefinition} {domain : String} {bindings : Bindings}
  (model : DomainModel) (linked : DeclarationsLinked [] definitions)
  (bodies : Bodies definitions domain bindings)

abbrev closed := definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) []

include linked bodies

theorem dimension_eq (xs : List (model.Field domain)) (n w : Nat) :
    invoke (closed model (definitions := definitions))
      ⟨bindings.dimension, .math, triple domain, [.index]⟩ (tableValues model domain xs n w) =
      .done (.cons n .nil) :=
  ReferenceLaw.invoke (model := model)
    (helper := ⟨bindings.dimension, .math, triple domain, [.index]⟩)
    (projection model (.cons (.there .here) .nil)) definitions linked bodies.dimension _ trivial

theorem width_eq (xs : List (model.Field domain)) (n w : Nat) :
    invoke (closed model (definitions := definitions))
      ⟨bindings.width, .math, triple domain, [.index]⟩ (tableValues model domain xs n w) =
      .done (.cons w .nil) :=
  ReferenceLaw.invoke (model := model)
    (helper := ⟨bindings.width, .math, triple domain, [.index]⟩)
    (projection model (.cons (.there (.there .here)) .nil)) definitions linked bodies.width _ trivial

theorem less_eq (a b : Nat) :
    invoke (closed model (definitions := definitions)) (lessHelper bindings) (.cons a (.cons b .nil)) =
      primitiveOutcome ((less model domain bindings).reference (.cons a (.cons b .nil))) :=
  ReferenceLaw.invoke (model := model) (helper := lessHelper bindings) (less model domain bindings) definitions linked bodies.less _ trivial

theorem halves_eq (xs : List (model.Field domain)) (n w : Nat) :
    invoke (closed model (definitions := definitions)) (halvesHelper domain bindings)
      (tableValues model domain xs n w) = primitiveOutcome (halvesOutcome model domain xs n) :=
  ReferenceLaw.invoke (model := model) (helper := halvesHelper domain bindings) (halves model domain bindings) definitions linked bodies.halves _ (less_eq model linked bodies 0 n)

theorem interpolate_eq (lo hi r : model.Field domain) :
    invoke (closed model (definitions := definitions))
      ⟨bindings.interpolate, .math, [.field domain, .field domain, .field domain], [.field domain]⟩
      (.cons lo (.cons hi (.cons r .nil))) = .done (.cons (lo + (hi - lo) * r) .nil) :=
  ReferenceLaw.invoke (model := model) (helper := ⟨bindings.interpolate, .math, [.field domain, .field domain, .field domain], [.field domain]⟩) (ReferenceLibrary.interpolate model domain) definitions linked bodies.interpolate _ trivial

theorem interpolation_eq (lo hi r : model.Field domain) :
    invoke (closed model (definitions := definitions))
      ⟨bindings.interpolation, .local, [.field domain, .field domain, .field domain], [.field domain]⟩
      (.cons lo (.cons hi (.cons r .nil))) = .done (.cons (lo + (hi - lo) * r) .nil) :=
  ReferenceLaw.invoke (model := model) (helper := ⟨bindings.interpolation, .local, [.field domain, .field domain, .field domain], [.field domain]⟩) (interpolation model domain bindings) definitions linked bodies.interpolation _
    (interpolate_eq model linked bodies lo hi r)

theorem callback_eq (lo hi r : model.Field domain) (low high : List (model.Field domain)) :
    invoke (closed model (definitions := definitions)) (collectSpec domain bindings).bodyHelper
      (.cons lo (.cons hi (.cons low (.cons high (.cons r .nil))))) =
      .done (.cons (lo + (hi - lo) * r) .nil) :=
  ReferenceLaw.invoke (model := model) (helper := (collectSpec domain bindings).bodyHelper) (callback model domain bindings) definitions linked bodies.callback _
    (interpolation_eq model linked bodies lo hi r)

theorem collect_eq (low high : List (model.Field domain)) (r : model.Field domain)
    (small : low.length < indexLimit) (same : low.length = high.length) :
    invoke (closed model (definitions := definitions)) (mapHelper domain bindings)
      (.cons low (.cons high (.cons r .nil))) =
      .done (.cons (List.zipWith (fun lo hi => lo + (hi - lo) * r) low high) .nil) :=
  ReferenceLaw.invoke (model := model) (helper := mapHelper domain bindings) (collect model domain bindings) definitions linked bodies.collect _
    ⟨small, same, fun lo hi => callback_eq model linked bodies lo hi r low high⟩

theorem first_eq (xs : List (model.Field domain)) (n w : Nat) (r : model.Field domain)
    (lengthBound : xs.length < indexLimit) (small : n < 64) (width : 0 < w)
    (shape : xs.length = 2 ^ n * w) :
    invoke (closed model (definitions := definitions)) (firstHelper domain bindings)
      (.cons xs (.cons n (.cons w (.cons r .nil)))) =
      primitiveOutcome (firstOutcome model domain (.cons xs (.cons n (.cons w (.cons r .nil))))) :=
  ReferenceLaw.invoke (model := model) (helper := firstHelper domain bindings) (first model domain bindings) definitions linked bodies.first _
    ⟨lengthBound, Nat.lt_trans small (by decide +kernel),
      fun positive => split_shape model domain xs n w positive width shape,
      halves_eq model linked bodies xs n w,
      fun low high r bound same => collect_eq model linked bodies low high r bound same⟩

set_option backward.isDefEq.respectTransparency false in
theorem step_eq (xs : List (model.Field domain)) (n w : Nat) (r : model.Field domain)
    (lengthBound : xs.length < indexLimit) (small : n < 64) (width : 0 < w)
    (shape : xs.length = 2 ^ n * w) :
    invoke (closed model (definitions := definitions))
      ⟨bindings.step, .local, firstInputs domain, triple domain⟩
      (.cons xs (.cons n (.cons w (.cons r .nil)))) =
      primitiveOutcome (firstOutcome model domain (.cons xs (.cons n (.cons w (.cons r .nil))))) := by
  have actual := ReferenceLaw.invoke (model := model) (helper := ⟨bindings.step, .local, firstInputs domain, triple domain⟩) (step model domain bindings) definitions linked bodies.step
    (.cons xs (.cons n (.cons w (.cons r .nil))))
    (first_eq model linked bodies xs n w r lengthBound small width shape)
  have reference : (step model domain bindings).reference
      (.cons xs (.cons n (.cons w (.cons r .nil)))) =
      firstOutcome model domain (.cons xs (.cons n (.cons w (.cons r .nil)))) := by
    rfl
  exact actual.trans (congrArg primitiveOutcome reference)

set_option backward.isDefEq.respectTransparency false in
theorem foldStep_eq (xs : List (model.Field domain)) (n w : Nat) (r : model.Field domain)
    (point : List (model.Field domain))
    (lengthBound : xs.length < indexLimit) (small : n < 64) (width : 0 < w)
    (shape : xs.length = 2 ^ n * w) :
    invoke (closed model (definitions := definitions)) (foldSpec domain bindings).stepHelper
      (.cons xs (.cons n (.cons w (.cons r (.cons point .nil))))) =
      primitiveOutcome (firstOutcome model domain (.cons xs (.cons n (.cons w (.cons r .nil))))) := by
  have actual := ReferenceLaw.invoke (model := model) (helper := (foldSpec domain bindings).stepHelper) (foldStep model domain bindings) definitions linked bodies.foldStep
    (.cons xs (.cons n (.cons w (.cons r (.cons point .nil)))))
    (step_eq model linked bodies xs n w r lengthBound small width shape)
  have reference : (foldStep model domain bindings).reference
      (.cons xs (.cons n (.cons w (.cons r (.cons point .nil))))) =
      firstOutcome model domain (.cons xs (.cons n (.cons w (.cons r .nil)))) := by
    rfl
  exact actual.trans (congrArg primitiveOutcome reference)

theorem fold_eq (xs point : List (model.Field domain)) (n w : Nat)
    (lengthBound : xs.length < indexLimit) (small : n < 64) (width : 0 < w)
    (shape : xs.length = 2 ^ n * w) :
    invoke (closed model (definitions := definitions))
      ⟨bindings.fold, .local, [.vector domain, .vector domain, .index, .index], triple domain⟩
      (.cons point (.cons xs (.cons n (.cons w .nil)))) =
      primitiveOutcome (prefixOutcome model domain xs point n w) :=
  ReferenceLaw.invoke (model := model) (helper := ⟨bindings.fold, .local, [.vector domain, .vector domain, .index, .index], triple domain⟩) (fold model domain bindings) definitions linked bodies.fold _
    ⟨lengthBound, small, width, shape,
      fun ys dim cols r len dimBound colsBound size =>
        foldStep_eq model linked bodies ys dim cols r point len dimBound colsBound size⟩

theorem sums_eq (xs : List (model.Field domain)) (n w : Nat) :
    invoke (closed model (definitions := definitions))
      ⟨bindings.sums, .local, triple domain, [.field domain, .field domain]⟩
      (tableValues model domain xs n w) =
      primitiveOutcome ((sums model domain bindings).reference (tableValues model domain xs n w)) :=
  ReferenceLaw.invoke (model := model) (helper := ⟨bindings.sums, .local, triple domain, [.field domain, .field domain]⟩) (sums model domain bindings) definitions linked bodies.sums _ (halves_eq model linked bodies xs n w)

theorem foldWrapper_eq (xs point : List (model.Field domain)) (n w : Nat)
    (lengthBound : xs.length < indexLimit) (small : n < 64) (width : 0 < w)
    (shape : xs.length = 2 ^ n * w) :
    invoke (closed model (definitions := definitions))
      ⟨bindings.foldWrapper, .local, [.vector domain, .index, .index, .vector domain], triple domain⟩
      (.cons xs (.cons n (.cons w (.cons point .nil)))) =
      primitiveOutcome (prefixOutcome model domain xs point n w) :=
  ReferenceLaw.invoke (model := model)
    (helper := ⟨bindings.foldWrapper, .local,
      [.vector domain, .index, .index, .vector domain], triple domain⟩)
    (foldWrapper model domain bindings) definitions linked bodies.foldWrapper _
    (fold_eq model linked bodies xs point n w lengthBound small width shape)

theorem prefix_eq (xs point : List (model.Field domain)) (n w : Nat)
    (lengthBound : xs.length < indexLimit) (small : n < 64) (width : 0 < w)
    (shape : xs.length = 2 ^ n * w) :
    invoke (closed model (definitions := definitions))
      ⟨bindings.restrictPrefix, .local, [.vector domain, .index, .index, .vector domain], triple domain⟩
      (.cons xs (.cons n (.cons w (.cons point .nil)))) =
      primitiveOutcome (prefixOutcome model domain xs point n w) :=
  ReferenceLaw.invoke (model := model)
    (helper := ⟨bindings.restrictPrefix, .local,
      [.vector domain, .index, .index, .vector domain], triple domain⟩)
    (restrictionPrefix model domain bindings) definitions linked bodies.restrictionPrefix _
    (foldWrapper_eq model linked bodies xs point n w lengthBound small width shape)

theorem values_eq (xs : List (model.Field domain)) (n w : Nat) :
    invoke (closed model (definitions := definitions))
      ⟨bindings.values, .math, triple domain, [.vector domain]⟩
      (tableValues model domain xs n w) = .done (.cons xs .nil) :=
  ReferenceLaw.invoke (model := model)
    (helper := ⟨bindings.values, .math, triple domain, [.vector domain]⟩)
    (values model domain) definitions linked bodies.values _ trivial

theorem valuesRealization_eq (xs : List (model.Field domain)) (n w : Nat) :
    invoke (closed model (definitions := definitions))
      ⟨bindings.valuesRealization, .local, triple domain, [.vector domain]⟩
      (tableValues model domain xs n w) = .done (.cons xs .nil) :=
  ReferenceLaw.invoke (model := model)
    (helper := ⟨bindings.valuesRealization, .local, triple domain, [.vector domain]⟩)
    (valuesRealization model domain bindings) definitions linked bodies.valuesRealization _
    (values_eq model linked bodies xs n w)

end Zkc.Source.Structured.ReferenceLibrary.Multilinear
