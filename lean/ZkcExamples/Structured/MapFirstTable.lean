module

public import ZkcExamples.Structured.MapFirstViews
public import ZkcExamples.Structured.MapFirstLaws
public import Zkc.Source.Structured.MapLaws

@[expose] public section

/-! All invocation laws below use this actual retained source's complete Payload.
Shared body views never substitute another program's helper table. -/
namespace ZkcExamples.Structured.MapFirstTable
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws
open MapFirstBodies MapFirstViews
set_option smartUnfolding false
set_option linter.unusedSimpArgs false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]


set_option backward.isDefEq.respectTransparency false in
/-- Actual membership plus raw-body equality discharges the comparison premise. -/
theorem less_law : LessLaw (program.payload.meanings F G) := by
  intro a b aBound bBound
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload lessDefinition less_member
    PrimitiveShapeViews.lessBody (by rfl) (.cons a (.cons b .nil))).trans
      (less_body _ a b aBound bBound)

set_option backward.isDefEq.respectTransparency false in
/-- The full table supplies the loop equation, including every checked step. -/
theorem rows_law : RowsLaw (program.payload.meanings F G) := by
  intro dimension bound
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload rowsDefinition rows_member
    PrimitiveShapeViews.rowsBody (by rfl) (indexResult dimension)).trans
      (rows_body _ less_law dimension bound)

set_option backward.isDefEq.respectTransparency false in
/-- The actual retained has_shape helper has this universal conditional equation. -/
theorem shape_equation (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    invoke (program.payload.meanings F G) shapeHelper (inputs xs dimension columns) =
      .done (boolResult (decide (HasShape xs dimension columns))) :=
  (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload shapeDefinition shape_member
    PrimitiveShapeViews.shapeBody (by rfl) (inputs xs dimension columns)).trans
      (shape_body _ less_law rows_law xs dimension columns lengthBound dimensionBound columnsBound)

set_option backward.isDefEq.respectTransparency false in
/-- The checked constructor preserves all three original outputs in order. -/
theorem table_equation (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    invoke (program.payload.meanings F G) tableHelper (inputs xs dimension columns) =
      if HasShape xs dimension columns then .done (inputs xs dimension columns) else .halt .reject := by
  have actual := Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload tableDefinition table_member
    PrimitiveTableViews.tableBody (by rfl) (inputs xs dimension columns)
  have equation := table_body (program.payload.meanings F G) xs dimension columns
    (decide (HasShape xs dimension columns))
    (shape_equation (G := G) xs dimension columns lengthBound dimensionBound columnsBound)
  simp only [decide_eq_true_eq] at equation
  exact actual.trans equation

set_option backward.isDefEq.respectTransparency false in
/-- The source helper itself checks dimension and split shape, not columns. -/
theorem halves_equation (xs : List F) (dimension columns : Nat)
    (dimensionBound : dimension < indexLimit) :
    invoke (program.payload.meanings F G) halvesHelper (inputs xs dimension columns) =
      if 0 < dimension then
        if 0 < xs.length ∧ xs.length % 2 = 0 then
          .done (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil))
        else .halt .refused
      else .halt .reject :=
  (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload halvesDefinition halves_member
    halvesBody halves_exact (inputs xs dimension columns)).trans
      (halves_body _ less_law xs dimension columns dimensionBound)

set_option backward.isDefEq.respectTransparency false in
theorem values_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) valuesHelper (inputs xs dimension columns) =
      .done (.cons xs .nil) := by
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload valuesDefinition values_member
    valuesBody values_exact (inputs xs dimension columns)).trans
      (MapSourceExpansions.first_values _ xs dimension columns)

set_option backward.isDefEq.respectTransparency false in
theorem valuesRealization_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) valuesRealizationHelper (inputs xs dimension columns) =
      .done (.cons xs .nil) := by
  refine (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload valuesRealizationDefinition valuesRealization_member
    valuesRealizationBody valuesRealization_exact (inputs xs dimension columns)).trans ?_
  dsimp only [inputs, vector]
  rw [MapSourceExpansions.first_valuesRealization]
  change (invoke (program.payload.meanings F G) valuesHelper (inputs xs dimension columns)).bind _ = _
  rw [values_equation]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem variables_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) variablesHelper (inputs xs dimension columns) =
      .done (.cons dimension .nil) := by
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload variablesDefinition variables_member
    variablesBody variables_exact (inputs xs dimension columns)).trans
      (MapSourceExpansions.first_variables _ xs dimension columns)

set_option backward.isDefEq.respectTransparency false in
theorem variablesRealization_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) variablesRealizationHelper (inputs xs dimension columns) =
      .done (.cons dimension .nil) := by
  refine (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload variablesRealizationDefinition variablesRealization_member
    variablesRealizationBody variablesRealization_exact (inputs xs dimension columns)).trans ?_
  dsimp only [inputs, vector]
  rw [MapSourceExpansions.first_variablesRealization]
  change (invoke (program.payload.meanings F G) variablesHelper (inputs xs dimension columns)).bind _ = _
  rw [variables_equation]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem width_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) widthHelper (inputs xs dimension columns) =
      .done (.cons columns .nil) := by
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload widthDefinition width_member
    widthBody width_exact (inputs xs dimension columns)).trans
      (MapSourceExpansions.first_width _ xs dimension columns)

set_option backward.isDefEq.respectTransparency false in
theorem widthRealization_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) widthRealizationHelper (inputs xs dimension columns) =
      .done (.cons columns .nil) := by
  refine (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload widthRealizationDefinition widthRealization_member
    widthRealizationBody widthRealization_exact (inputs xs dimension columns)).trans ?_
  dsimp only [inputs, vector]
  rw [MapSourceExpansions.first_widthRealization]
  change (invoke (program.payload.meanings F G) widthHelper (inputs xs dimension columns)).bind _ = _
  rw [width_equation]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Arithmetic is established from the retained Math body, not its symbol name. -/
theorem interpolate_equation (low high r : F) :
    invoke (program.payload.meanings F G) interpolateHelper
      (.cons low (.cons high (.cons r .nil))) =
      .done (.cons (low + (high - low) * r) .nil) := by
  refine (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload interpolateDefinition interpolate_member
    interpolateBody interpolate_exact (.cons low (.cons high (.cons r .nil)))).trans ?_
  rw [MapSourceExpansions.first_interpolate]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Complete actual table discharges the generic map helper premise. -/
theorem map_law : MapLaw (program.payload.meanings F G) := by
  intro low high r sameLength small
  refine (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload mapDefinition map_member
    mapBody map_exact (.cons low (.cons high (.cons r .nil)))).trans ?_
  rw [MapSourceExpansions.first_map]
  have mapped := Evaluation.denoteMap_twoRows_broadcast (program.payload.meanings F G)
    MapFirstBodies.mapSpec.helperName MapFirstBodies.mapSpec.field low high r small sameLength.symm
    (fun lo hi => lo + (hi - lo) * r) (fun lo hi => interpolate_equation lo hi r)
  exact (congrArg (fun process : Closed (Values (assignment F G) [vector]) =>
    process.bind fun result =>
      (.done (.cons (result.get .here) .nil) : Closed (Values (assignment F G) [vector])))
    mapped).trans (by rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Checked body lookup is repeated for this complete Payload. -/
theorem first_equation (xs : List F) (dimension columns : Nat) (r : F)
    (shape : HasShape xs dimension columns) (lengthBound : xs.length < indexLimit) :
    invoke (program.payload.meanings F G) firstHelper (firstInputs xs dimension columns r) =
      if 0 < dimension then
        .done (inputs (Zkc.Polynomial.Multilinear.restrictValues xs r) (dimension - 1) columns)
      else .halt .reject :=
  (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload firstDefinition first_member
    firstBody first_exact (firstInputs xs dimension columns r)).trans
      (MapFirstLaws.first_body _ halves_equation map_law xs dimension columns r shape lengthBound)

end ZkcExamples.Structured.MapFirstTable
