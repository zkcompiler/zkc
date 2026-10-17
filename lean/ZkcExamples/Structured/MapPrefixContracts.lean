module

public import ZkcExamples.Structured.MapFirstContracts
public import ZkcExamples.Structured.MapProjectionContracts
public import ZkcExamples.Structured.MapPrefixLaws

@[expose] public section
namespace ZkcExamples.Structured.MapPrefixContracts
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws MapPrefixLaws MapPrefixBodies
open Zkc.Polynomial.Multilinear (restrictPrefixValues)

/-- The additional exact associations needed only by Prefix clients. -/
structure Bodies (definitions : List CheckedDefinition) : Prop where
  step : BodyIn definitions stepHelper stepBody
  foldStep : BodyIn definitions foldStepHelper foldStepBody
  fold : BodyIn definitions foldHelper foldBody
  foldWrapper : BodyIn definitions foldWrapperHelper foldWrapperBody
  prefixBody : BodyIn definitions prefixHelper MapPrefixBodies.prefixBody
  values : BodyIn definitions valuesHelper valuesBody
  valuesRealization : BodyIn definitions valuesRealizationHelper valuesRealizationBody

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Each premise already has a source-body proof in the completed map package.
Instantiation in a different source table must recheck its entire raw body and ABI. -/
structure Laws (table : Meanings F G) : Prop where
  halves : HalvesLaw table
  shape : ∀ (xs : List F) (dimension columns : Nat),
    xs.length < indexLimit → dimension < indexLimit → columns < indexLimit →
    invoke table shapeHelper (inputs xs dimension columns) =
      .done (boolResult (decide (HasShape xs dimension columns)))
  tableLaw : ∀ (xs : List F) (dimension columns : Nat),
    xs.length < indexLimit → dimension < indexLimit → columns < indexLimit →
    invoke table tableHelper (inputs xs dimension columns) =
      if HasShape xs dimension columns then .done (inputs xs dimension columns) else .halt .reject
  fixPrefix : ∀ (xs : List F) (dimension columns : Nat) (point : List F),
    HasShape xs dimension columns → xs.length < indexLimit → point.length < indexLimit →
    invoke table prefixHelper (prefixInputs xs dimension columns point) =
      if point.length ≤ dimension then
        .done (inputs (restrictPrefixValues xs point) (dimension - point.length) columns)
      else .halt .reject
  values : ∀ (xs : List F) (dimension columns : Nat),
    invoke table valuesRealizationHelper (inputs xs dimension columns) = .done (.cons xs .nil)


variable {definitions : List CheckedDefinition}
    (linked : DeclarationsLinked [] definitions) (bodies : Bodies definitions)
include linked bodies

set_option backward.isDefEq.respectTransparency false in
theorem step_equation (xs : List F) (dimension columns : Nat) (r : F) :
    invoke (closedMeanings (F := F) (G := G) definitions) stepHelper (firstInputs xs dimension columns r) =
      invoke (closedMeanings (F := F) (G := G) definitions) firstHelper (firstInputs xs dimension columns r) :=
  (bodies.step.invoke linked (firstInputs xs dimension columns r)).trans
    (step_body _ xs dimension columns r)

set_option backward.isDefEq.respectTransparency false in
theorem foldStep_equation : FoldStepLaw (closedMeanings (F := F) (G := G) definitions) := by
  intro xs dimension columns r point
  exact (bodies.foldStep.invoke linked
    (.cons xs (.cons dimension (.cons columns (.cons r (.cons point .nil)))))).trans
      ((foldStep_body _ xs dimension columns r point).trans
        (step_equation linked bodies xs dimension columns r))

set_option backward.isDefEq.respectTransparency false in
/-- All source wrappers reduce to the actual finite body in this same table. -/
theorem prefix_finite_body (xs : List F) (dimension columns : Nat) (point : List F) :
    invoke (closedMeanings (F := F) (G := G) definitions) prefixHelper (prefixInputs xs dimension columns point) =
      foldBody.denote (meaning F G (closedMeanings (F := F) (G := G) definitions))
        (Values.cons point (.cons xs (.cons dimension (.cons columns .nil)))).get := by
  rw [bodies.prefixBody.invoke linked, prefix_body, bodies.foldWrapper.invoke linked,
    foldWrapper_body, bodies.fold.invoke linked]

set_option backward.isDefEq.respectTransparency false in
theorem prefix_equation (first : FirstLaw (closedMeanings (F := F) (G := G) definitions))
    (xs : List F) (dimension columns : Nat) (point : List F)
    (shape : HasShape xs dimension columns) (vectorBound : xs.length < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) definitions) prefixHelper (prefixInputs xs dimension columns point) =
      if point.length < indexLimit then
        if point.length ≤ dimension then
          .done (inputs (restrictPrefixValues xs point) (dimension - point.length) columns)
        else .halt .reject
      else .halt .exhausted := by
  rw [prefix_finite_body linked bodies]
  exact finite_prefix_generic_body _ first (foldStep_equation linked bodies)
    xs dimension columns point shape vectorBound

set_option backward.isDefEq.respectTransparency false in
/-- Domain admission stops before a callback, even without a valid table shape. -/
theorem prefix_exhausted (xs : List F) (dimension columns : Nat) (point : List F)
    (invalid : ¬ point.length < indexLimit) :
    invoke (closedMeanings (F := F) (G := G) definitions) prefixHelper (prefixInputs xs dimension columns point) =
      .halt .exhausted := by
  rw [prefix_finite_body linked bodies, fold_body]
  change Evaluation.denoteFold (closedMeanings (F := F) (G := G) definitions) foldSpec
    ((Values.cons point Values.nil).append ((inputs xs dimension columns).append Values.nil)) = _
  rw [Evaluation.denoteFold_pack, Finite.execute, domain_admit, ite_eq_right invalid]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem values_equation (xs : List F) (dimension columns : Nat) :
    invoke (closedMeanings (F := F) (G := G) definitions) valuesHelper (inputs xs dimension columns) =
      .done (.cons xs .nil) :=
  MapProjectionContracts.values_equation linked bodies.values xs dimension columns

set_option backward.isDefEq.respectTransparency false in
theorem valuesRealization_equation (xs : List F) (dimension columns : Nat) :
    invoke (closedMeanings (F := F) (G := G) definitions) valuesRealizationHelper (inputs xs dimension columns) =
      .done (.cons xs .nil) :=
  MapProjectionContracts.valuesRealization_equation linked bodies.values bodies.valuesRealization
    xs dimension columns

/-- First and Prefix associations refer to this list; no other table is equated to it. -/
theorem laws_of_bodies (firstBodies : MapFirstContracts.Bodies definitions) :
    Laws (closedMeanings (F := F) (G := G) definitions) := by
  have first := MapFirstContracts.laws_of_bodies (F := F) (G := G) linked firstBodies
  refine ⟨first.halves, first.shape, first.tableLaw, ?_, valuesRealization_equation linked bodies⟩
  intro xs dimension columns point shape vectorBound pointBound
  rw [prefix_equation linked bodies first.first xs dimension columns point shape vectorBound,
    ite_eq_left pointBound]

end ZkcExamples.Structured.MapPrefixContracts
