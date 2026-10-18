module

public import ZkcExamples.Structured.PrimitiveLibraryConsumers

@[expose] public section

/-! Short-circuit laws on the complete admitted Shape wrapper. Unlike the
representable-input equation, these expose which later bounds are unnecessary
when an earlier source guard decides the result. -/
namespace ZkcExamples.Structured.PrimitiveSourceStops
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary PrimitiveShapeViews
set_option smartUnfolding false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false in
/-- A zero column count avoids both dimension comparison and vector length. -/
theorem zero_columns (xs : List F) (dimension : Nat) :
    program.denote F G (inputs xs dimension 0) = .done (boolResult false) := by
  have helper : invoke (program.payload.meanings F G) shapeHelper (inputs xs dimension 0) =
      .done (boolResult false) :=
    (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
      program.payload shapeDefinition shape_member
      shapeBody shape_exact (inputs xs dimension 0)).trans
        (shape_zero_columns _ PrimitiveLibraryConsumers.Shape.less_law xs dimension)
  refine (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    program.payload entryBody entry_exact (inputs xs dimension 0)).trans ?_
  dsimp only [inputs]
  rw [PrimitiveExpansions.shape_entry]
  change (invoke (program.payload.meanings F G) shapeHelper (inputs xs dimension 0)).bind _ = _
  rw [helper]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A representable large dimension returns false without a vector length bound. -/
theorem large_dimension (xs : List F) (dimension columns : Nat) (positive : 0 < columns)
    (columnsBound : columns < indexLimit) (dimensionBound : dimension < indexLimit)
    (large : ¬ dimension < 64) :
    program.denote F G (inputs xs dimension columns) = .done (boolResult false) := by
  have helper : invoke (program.payload.meanings F G) shapeHelper (inputs xs dimension columns) =
      .done (boolResult false) :=
    (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
      program.payload shapeDefinition shape_member
      shapeBody shape_exact (inputs xs dimension columns)).trans
        (shape_large_dimension _ PrimitiveLibraryConsumers.Shape.less_law xs dimension columns
          positive columnsBound dimensionBound large)
  refine (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    program.payload entryBody entry_exact (inputs xs dimension columns)).trans ?_
  dsimp only [inputs]
  rw [PrimitiveExpansions.shape_entry]
  change (invoke (program.payload.meanings F G) shapeHelper (inputs xs dimension columns)).bind _ = _
  rw [helper]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Once both guards pass, unrepresentable length exhausts the original process. -/
theorem length_exhausted (xs : List F) (dimension columns : Nat) (positive : 0 < columns)
    (columnsBound : columns < indexLimit) (dimensionSmall : dimension < 64)
    (lengthInvalid : ¬ xs.length < indexLimit) :
    program.denote F G (inputs xs dimension columns) = .halt .exhausted := by
  have helper : invoke (program.payload.meanings F G) shapeHelper (inputs xs dimension columns) =
      .halt .exhausted :=
    (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
      program.payload shapeDefinition shape_member
      shapeBody shape_exact (inputs xs dimension columns)).trans
        (shape_length_exhausted _ PrimitiveLibraryConsumers.Shape.less_law xs dimension columns
          positive columnsBound dimensionSmall lengthInvalid)
  refine (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    program.payload entryBody entry_exact (inputs xs dimension columns)).trans ?_
  dsimp only [inputs]
  rw [PrimitiveExpansions.shape_entry]
  change (invoke (program.payload.meanings F G) shapeHelper (inputs xs dimension columns)).bind _ = _
  rw [helper]
  rfl

end ZkcExamples.Structured.PrimitiveSourceStops
