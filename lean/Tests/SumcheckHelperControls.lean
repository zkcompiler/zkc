module

public import Tests.SumcheckSourceControls
public import ZkcExamples.Structured.MapContractInstances

@[expose] public section
namespace Tests.SumcheckHelperControls
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open PrimitiveLibrary MapPrefixBodies MapFirstLaws MapPrefixLaws SumcheckHelperBodies SumcheckHelperLaws
open Tests.SumcheckHelperMutants
open Zkc.Polynomial.Multilinear

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false in
theorem sums_body_all (xs : List F) (dimension columns : Nat) :
    sumsBody.denote (meaning F G (MapPrefixViews.program.payload.meanings F G)) (inputs xs dimension columns).get =
      if dimension < indexLimit then
        if 0 < dimension then
          if 0 < xs.length ∧ xs.length % 2 = 0 then
            .done (messageResult (xs.take (xs.length / 2)).sum (xs.drop (xs.length / 2)).sum)
          else .halt .refused
        else .halt .reject
      else .halt .refused  :=
  sums_generic_body_all _ MapPrefixContractsInstance.first_laws.less
    (fun xs n w => MapPrefixContractsInstance.first_bodies.halves.invoke
      MapPrefixViews.program.payload.linked (inputs xs n w)) xs dimension columns

set_option backward.isDefEq.respectTransparency false in
theorem sums_ordered : sumsBody.denote
    (meaning ℤ ℤ (MapPrefixViews.program.payload.meanings ℤ ℤ)) (inputs [1,2,3,4] 2 1).get =
      .done (messageResult 3 7) := by
  rw [sums_body_all]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem sums_zero_dimension : sumsBody.denote
    (meaning ℤ ℤ (MapPrefixViews.program.payload.meanings ℤ ℤ)) (inputs [9] 0 1).get = .halt .reject := by
  rw [sums_body_all]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem sums_odd_vector : sumsBody.denote
    (meaning ℤ ℤ (MapPrefixViews.program.payload.meanings ℤ ℤ)) (inputs [1,2,3] 1 1).get = .halt .refused := by
  rw [sums_body_all]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem sums_unused_width : sumsBody.denote
    (meaning ℤ ℤ (MapPrefixViews.program.payload.meanings ℤ ℤ)) (inputs [1,2] 1 0).get =
      .done (messageResult 1 2) := by
  rw [sums_body_all]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem sums_unrepresentable_dimension : sumsBody.denote
    (meaning ℤ ℤ (MapPrefixViews.program.payload.meanings ℤ ℤ)) (inputs [1,2] indexLimit 1).get =
      .halt .refused := by
  rw [sums_body_all, ite_eq_right (Nat.lt_irrefl _)]

set_option backward.isDefEq.respectTransparency false in
/-- A malformed shape returns false even with no check_table closure installed. -/
theorem malformed_no_callback : checkBody.denote
    (meaning ℤ ℤ (MapPrefixViews.program.payload.meanings ℤ ℤ))
    (checkInputs [1,2,3] [2] 0).get = .done (boolResult false) :=
  check_malformed_generic_body _ MapPrefixContractsInstance.first_laws.shape _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option backward.isDefEq.respectTransparency false in
theorem finite_empty : foldBody.denote
    (meaning ℤ ℤ (MapPrefixViews.program.payload.meanings ℤ ℤ))
    (Values.cons ([] : List ℤ) (.cons [9] (.cons 0 (.cons 1 .nil)))).get =
      .done (inputs [9] 0 1) := by
  rw [finite_prefix_generic_body _ MapPrefixContractsInstance.first_laws.first
    (MapPrefixContracts.foldStep_equation MapPrefixViews.program.payload.linked MapPrefixContractsInstance.prefix_bodies) _ _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem finite_partial_width_two : foldBody.denote
    (meaning ℤ ℤ (MapPrefixViews.program.payload.meanings ℤ ℤ))
    (Values.cons ([2] : List ℤ) (.cons [1,2,3,4,5,6,7,8] (.cons 2 (.cons 2 .nil)))).get =
      .done (inputs [9,10,11,12] 1 2) := by
  rw [finite_prefix_generic_body _ MapPrefixContractsInstance.first_laws.first
    (MapPrefixContracts.foldStep_equation MapPrefixViews.program.payload.linked MapPrefixContractsInstance.prefix_bodies) _ _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem finite_too_long : foldBody.denote
    (meaning ℤ ℤ (MapPrefixViews.program.payload.meanings ℤ ℤ))
    (Values.cons ([2,3] : List ℤ) (.cons [1,2] (.cons 1 (.cons 1 .nil)))).get =
      .halt .reject := by
  rw [finite_prefix_generic_body _ MapPrefixContractsInstance.first_laws.first
    (MapPrefixContracts.foldStep_equation MapPrefixViews.program.payload.linked MapPrefixContractsInstance.prefix_bodies) _ _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- The reached true branch demands the absent callback in the actual map table. -/
theorem valid_shape_missing_callback : checkBody.denote
    (meaning ℤ ℤ (MapPrefixViews.program.payload.meanings ℤ ℤ))
    (checkInputs [1,2,3,4] [2,3] 8).get = .halt .refused := by
  rw [check_expansion, ite_eq_left (by decide +kernel),
    MapPrefixContractsInstance.first_laws.shape _ _ _
      (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Normal exact-signature lookup executes the swapped return order. -/
theorem swapped_sums_lookup :
    invoke (Evaluation.extendMeanings SiteObservations.closed
      (MapPrefixViews.program.payload.meanings ℤ ℤ) sumsSwappedDefinition)
      sumsHelper (inputs [1,2,3,4] 2 1) = .done (messageResult 7 3) := by
  refine (Evaluation.invoke_extended (F := ℤ) (G := ℤ) SiteObservations.closed _
    sumsSwappedDefinition (inputs [1,2,3,4] 2 1)).trans ?_
  change sumsSwappedBody.denote _ _ = _
  rw [sums_swapped_expansion, MapPrefixContractsInstance.first_laws.halves _ _ _
    (by decide +kernel)]
  rfl

/-- Same full interpolation signature, with the low/high arithmetic exchanged. -/
def interpolateSwappedBody : Region dialect [scalar, scalar, scalar] [scalar] :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def interpolateSwappedDefinition := checkedBody interpolateHelper interpolateSwappedBody

def dependencyTable : Meanings ℤ ℤ := Evaluation.extendMeanings SiteObservations.closed
  (MapPrefixViews.program.payload.meanings ℤ ℤ) interpolateSwappedDefinition

set_option backward.isDefEq.respectTransparency false in
theorem changed_dependency_lookup (low high r : ℤ) :
    invoke dependencyTable interpolateHelper (.cons low (.cons high (.cons r .nil))) =
      .done (.cons (high + (low - high) * r) .nil) := by
  refine (Evaluation.invoke_extended (F := ℤ) (G := ℤ) SiteObservations.closed _
    interpolateSwappedDefinition (.cons low (.cons high (.cons r .nil)))).trans ?_
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The unchanged actual map body now captures the changed same-name dependency. -/
theorem changed_dependency_changes_map :
    invoke (Evaluation.extendMeanings SiteObservations.closed dependencyTable MapPrefixViews.mapDefinition)
      mapHelper (.cons [1] (.cons [3] (.cons (2 : ℤ) .nil))) = .done (.cons [-1] .nil) := by
  refine (Evaluation.invoke_extended (F := ℤ) (G := ℤ) SiteObservations.closed dependencyTable
    MapPrefixViews.mapDefinition (.cons [1] (.cons [3] (.cons 2 .nil)))).trans ?_
  change mapBody.denote (meaning ℤ ℤ dependencyTable) _ = _
  rw [MapSourceExpansions.first_map]
  have mapped := Evaluation.denoteMap_twoRows_broadcast dependencyTable
    MapFirstBodies.mapSpec.helperName MapFirstBodies.mapSpec.field [1] [3] 2
    (by decide +kernel) rfl (fun lo hi => hi + (lo - hi) * 2)
    (fun lo hi => changed_dependency_lookup lo hi 2)
  rw [mapped]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem original_dependency_map :
    invoke (MapPrefixViews.program.payload.meanings ℤ ℤ)
      mapHelper (.cons [1] (.cons [3] (.cons (2 : ℤ) .nil))) = .done (.cons [5] .nil) := by
  refine (MapFirstContracts.map_law (F := ℤ) (G := ℤ) MapPrefixViews.program.payload.linked
    MapPrefixContractsInstance.first_bodies [1] [3] 2 rfl (by decide +kernel)).trans ?_
  rfl

end Tests.SumcheckHelperControls
