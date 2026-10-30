module

public import ZkcExamples.Structured.MapFirstAssociations
public import Zkc.Protocols.Multilinear.Source.MapProjectionContracts

@[expose] public section

/-! All invocation laws below use this actual retained source's complete Payload.
Shared body views never substitute another program's helper table. -/
namespace ZkcExamples.Structured.MapFirstTable
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws
open MapFirstBodies MapFirstViews
set_option smartUnfolding false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Actual membership plus raw-body equality discharges the comparison premise. -/
theorem less_law : LessLaw (program.payload.meanings F G) :=
  MapFirstContracts.less_law program.payload.linked MapFirstAssociations.first_bodies

/-- The full table supplies the loop equation, including every checked step. -/
theorem rows_law : RowsLaw (program.payload.meanings F G) :=
  MapFirstContracts.rows_law program.payload.linked MapFirstAssociations.first_bodies

/-- The actual retained has_shape helper has this universal conditional equation. -/
theorem shape_equation (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    invoke (program.payload.meanings F G) shapeHelper (inputs xs dimension columns) =
      .done (boolResult (decide (HasShape xs dimension columns))) :=
  MapFirstContracts.shape_equation program.payload.linked MapFirstAssociations.first_bodies
    xs dimension columns lengthBound dimensionBound columnsBound

/-- The checked constructor preserves all three original outputs in order. -/
theorem table_equation (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    invoke (program.payload.meanings F G) tableHelper (inputs xs dimension columns) =
      if HasShape xs dimension columns then .done (inputs xs dimension columns) else .halt .reject :=
  MapFirstContracts.table_equation program.payload.linked MapFirstAssociations.first_bodies
    xs dimension columns lengthBound dimensionBound columnsBound

/-- The source helper itself checks dimension and split shape, not columns. -/
theorem halves_equation (xs : List F) (dimension columns : Nat)
    (dimensionBound : dimension < indexLimit) :
    invoke (program.payload.meanings F G) halvesHelper (inputs xs dimension columns) =
      if 0 < dimension then
        if 0 < xs.length ∧ xs.length % 2 = 0 then
          .done (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil))
        else .halt .refused
      else .halt .reject :=
  MapFirstContracts.halves_equation program.payload.linked MapFirstAssociations.first_bodies
    xs dimension columns dimensionBound

theorem values_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) valuesHelper (inputs xs dimension columns) =
      .done (.cons xs .nil) :=
  MapProjectionContracts.values_equation program.payload.linked
    MapFirstAssociations.values_association xs dimension columns

theorem valuesRealization_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) valuesRealizationHelper (inputs xs dimension columns) =
      .done (.cons xs .nil) :=
  MapProjectionContracts.valuesRealization_equation program.payload.linked
    MapFirstAssociations.values_association MapFirstAssociations.valuesRealization_association xs dimension columns

theorem variables_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) variablesHelper (inputs xs dimension columns) =
      .done (.cons dimension .nil) :=
  MapProjectionContracts.variables_equation program.payload.linked
    MapFirstAssociations.variables_association xs dimension columns

theorem variablesRealization_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) variablesRealizationHelper (inputs xs dimension columns) =
      .done (.cons dimension .nil) :=
  MapProjectionContracts.variablesRealization_equation program.payload.linked
    MapFirstAssociations.variables_association MapFirstAssociations.variablesRealization_association xs dimension columns

theorem width_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) widthHelper (inputs xs dimension columns) =
      .done (.cons columns .nil) :=
  MapProjectionContracts.width_equation program.payload.linked
    MapFirstAssociations.width_association xs dimension columns

theorem widthRealization_equation (xs : List F) (dimension columns : Nat) :
    invoke (program.payload.meanings F G) widthRealizationHelper (inputs xs dimension columns) =
      .done (.cons columns .nil) :=
  MapProjectionContracts.widthRealization_equation program.payload.linked
    MapFirstAssociations.width_association MapFirstAssociations.widthRealization_association xs dimension columns

/-- Arithmetic is established from the retained Math body, not its symbol name. -/
theorem interpolate_equation (low high r : F) :
    invoke (program.payload.meanings F G) interpolateHelper
      (.cons low (.cons high (.cons r .nil))) =
      .done (.cons (low + (high - low) * r) .nil) :=
  MapFirstContracts.interpolate_equation program.payload.linked MapFirstAssociations.first_bodies
    low high r

/-- Complete actual table discharges the generic map helper premise. -/
theorem map_law : MapLaw (program.payload.meanings F G) :=
  MapFirstContracts.map_law program.payload.linked MapFirstAssociations.first_bodies

/-- Instantiate the shared body proof in this complete Payload. -/
theorem first_equation (xs : List F) (dimension columns : Nat) (r : F)
    (shape : HasShape xs dimension columns) (lengthBound : xs.length < indexLimit) :
    invoke (program.payload.meanings F G) firstHelper (firstInputs xs dimension columns r) =
      if 0 < dimension then
        .done (inputs (Zkc.Polynomial.Multilinear.restrictValues xs r) (dimension - 1) columns)
      else .halt .reject :=
  MapFirstContracts.first_equation program.payload.linked MapFirstAssociations.first_bodies
    xs dimension columns r shape lengthBound

end ZkcExamples.Structured.MapFirstTable
