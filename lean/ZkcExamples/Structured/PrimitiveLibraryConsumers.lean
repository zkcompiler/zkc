module

public import Zkc.Protocols.Multilinear.Source.PrimitiveLibrary

@[expose] public section

/-! Full-table consumers of the actual original-stage exports. Every helper
premise is supplied by checked membership and exact body equality. -/
namespace ZkcExamples.Structured.PrimitiveLibraryConsumers
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary

-- Local transparency options below elaborate dependent source-view aliases;
-- every resulting equation is still checked by the kernel.
set_option smartUnfolding false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

namespace Shape
open PrimitiveShapeViews

/-- Actual membership plus raw-body equality discharges the comparison premise. -/
theorem less_law : LessLaw (program.payload.meanings F G) := by
  intro a b aBound bBound
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload lessDefinition less_member
    PrimitiveShapeViews.lessBody (by rfl) (.cons a (.cons b .nil))).trans
      (less_body _ a b aBound bBound)

/-- The full table supplies the loop equation, including every checked step. -/
theorem rows_law : RowsLaw (program.payload.meanings F G) := by
  intro dimension bound
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload rowsDefinition rows_member
    PrimitiveShapeViews.rowsBody (by rfl) (indexResult dimension)).trans
      (rows_body _ less_law dimension bound)

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
/-- The complete original wrapper returns precisely the library predicate. -/
theorem process_equation (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    program.denote F G (inputs xs dimension columns) =
      .done (boolResult (decide (HasShape xs dimension columns))) := by
  refine (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    program.payload entryBody entry_exact (inputs xs dimension columns)).trans ?_
  dsimp only [inputs]
  rw [PrimitiveExpansions.shape_entry]
  change (invoke (program.payload.meanings F G) shapeHelper (inputs xs dimension columns)).bind _ = _
  rw [shape_equation xs dimension columns lengthBound dimensionBound columnsBound]
  rfl

end Shape

namespace Table
open PrimitiveTableViews

/-- Actual membership plus raw-body equality discharges the comparison premise. -/
theorem less_law : LessLaw (program.payload.meanings F G) := by
  intro a b aBound bBound
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload lessDefinition less_member
    PrimitiveShapeViews.lessBody (by rfl) (.cons a (.cons b .nil))).trans
      (less_body _ a b aBound bBound)

/-- The full table supplies the loop equation, including every checked step. -/
theorem rows_law : RowsLaw (program.payload.meanings F G) := by
  intro dimension bound
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload rowsDefinition rows_member
    PrimitiveShapeViews.rowsBody (by rfl) (indexResult dimension)).trans
      (rows_body _ less_law dimension bound)

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
theorem process_equation (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    program.denote F G (inputs xs dimension columns) =
      if HasShape xs dimension columns then .done (inputs xs dimension columns) else .halt .reject := by
  refine (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    program.payload entryBody entry_exact (inputs xs dimension columns)).trans ?_
  dsimp only [inputs]
  rw [PrimitiveExpansions.table_entry]
  change (invoke (program.payload.meanings F G) tableHelper (inputs xs dimension columns)).bind _ = _
  rw [table_equation xs dimension columns lengthBound dimensionBound columnsBound]
  split <;> rfl

end Table

namespace Halves
open PrimitiveHalvesViews

/-- Actual membership plus raw-body equality discharges the comparison premise. -/
theorem less_law : LessLaw (program.payload.meanings F G) := by
  intro a b aBound bBound
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload lessDefinition less_member
    PrimitiveShapeViews.lessBody (by rfl) (.cons a (.cons b .nil))).trans
      (less_body _ a b aBound bBound)

/-- The full table supplies the loop equation, including every checked step. -/
theorem rows_law : RowsLaw (program.payload.meanings F G) := by
  intro dimension bound
  exact (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload rowsDefinition rows_member
    PrimitiveShapeViews.rowsBody (by rfl) (indexResult dimension)).trans
      (rows_body _ less_law dimension bound)

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
/-- Complete original table-then-halves behavior. A failed constructor prevents
all later checks and both split outputs. -/
theorem process_equation (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    program.denote F G (inputs xs dimension columns) =
      if HasShape xs dimension columns then
        if 0 < dimension then
          if 0 < xs.length ∧ xs.length % 2 = 0 then
            .done (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil))
          else .halt .refused
        else .halt .reject
      else .halt .reject := by
  refine (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    program.payload entryBody entry_exact (inputs xs dimension columns)).trans ?_
  dsimp only [inputs]
  rw [PrimitiveExpansions.halves_entry]
  change (invoke (program.payload.meanings F G) tableHelper (inputs xs dimension columns)).bind _ = _
  rw [table_equation xs dimension columns lengthBound dimensionBound columnsBound]
  split
  · change (invoke (program.payload.meanings F G) halvesHelper (inputs xs dimension columns)).bind _ = _
    rw [halves_equation xs dimension columns dimensionBound]
    split
    · split <;> rfl
    · rfl
  · rfl

end Halves

end ZkcExamples.Structured.PrimitiveLibraryConsumers
