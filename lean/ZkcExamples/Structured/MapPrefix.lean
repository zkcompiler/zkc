module

public import ZkcExamples.Structured.MapPrefixFold

@[expose] public section

/-! Complete checked Prefix contract: ordered finite composition, empty identity,
reached zero-dimension rejection and point-length admission. -/
namespace ZkcExamples.Structured.MapPrefix
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws MapPrefixLaws
open MapPrefixBodies MapPrefixViews MapPrefixTable MapPrefixFold
open Zkc.Polynomial.Multilinear (restrictPrefixValues)
set_option smartUnfolding false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem wrapper_equation (xs : List F) (dimension columns : Nat) (point : List F)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    invoke (program.payload.meanings F G) wrapperHelper (prefixInputs xs dimension columns point) =
      if HasShape xs dimension columns then
        if point.length < indexLimit then
          if point.length ≤ dimension then .done (inputs (restrictPrefixValues xs point) (dimension - point.length) columns)
          else .halt .reject
        else .halt .exhausted
      else .halt .reject := by
  refine (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload wrapperDefinition wrapper_member
    wrapperBody wrapper_exact (prefixInputs xs dimension columns point)).trans ?_
  exact MapPrefixLaws.wrapper_body _ table_equation valuesRealization_equation
    variablesRealization_equation widthRealization_equation prefix_equation prefix_exhausted
    xs dimension columns point lengthBound dimensionBound columnsBound

/-- Universal equation of the complete retained singleton protocol's checked projection. -/
theorem process_equation (xs : List F) (dimension columns : Nat) (point : List F)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    program.denote F G (prefixInputs xs dimension columns point) =
      if HasShape xs dimension columns then
        if point.length < indexLimit then
          if point.length ≤ dimension then .done (inputs (restrictPrefixValues xs point) (dimension - point.length) columns)
          else .halt .reject
        else .halt .exhausted
      else .halt .reject := by
  refine (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    program.payload entryBody entry_exact (prefixInputs xs dimension columns point)).trans ?_
  exact (MapPrefixLaws.entry_body _ xs dimension columns point).trans
    (wrapper_equation xs dimension columns point lengthBound dimensionBound columnsBound)

/-- Empty points preserve the complete ordered table triple, including dimension zero. -/
theorem process_empty (xs : List F) (dimension columns : Nat)
    (shape : HasShape xs dimension columns) (lengthBound : xs.length < indexLimit)
    (columnsBound : columns < indexLimit) :
    program.denote F G (prefixInputs xs dimension columns []) =
      .done (inputs xs dimension columns) := by
  rw [process_equation xs dimension columns [] lengthBound
    (Nat.lt_trans shape.2.1 (by decide +kernel)) columnsBound, ite_eq_left shape]
  rfl

/-- A representable overlong point reaches the zero-dimension First guard. -/
theorem process_too_long (xs : List F) (dimension columns : Nat) (point : List F)
    (shape : HasShape xs dimension columns) (lengthBound : xs.length < indexLimit)
    (columnsBound : columns < indexLimit) (pointBound : point.length < indexLimit)
    (tooLong : dimension < point.length) :
    program.denote F G (prefixInputs xs dimension columns point) = .halt .reject := by
  rw [process_equation xs dimension columns point lengthBound
    (Nat.lt_trans shape.2.1 (by decide +kernel)) columnsBound, ite_eq_left shape,
    ite_eq_left pointBound, ite_eq_right (by omega)]

/-- Each coordinate removes one leading row bit while retaining every column. -/
theorem process_shape (xs : List F) (dimension columns : Nat) (point : List F)
    (shape : HasShape xs dimension columns) (lengthBound : xs.length < indexLimit)
    (columnsBound : columns < indexLimit) (fits : point.length ≤ dimension) :
    program.denote F G (prefixInputs xs dimension columns point) =
        .done (inputs (restrictPrefixValues xs point) (dimension - point.length) columns) ∧
      HasShape (restrictPrefixValues xs point) (dimension - point.length) columns := by
  have dimensionBound : dimension < indexLimit := Nat.lt_trans shape.2.1 (by decide +kernel)
  have pointBound : point.length < indexLimit := Nat.lt_of_le_of_lt fits dimensionBound
  constructor
  · rw [process_equation xs dimension columns point lengthBound dimensionBound columnsBound,
      ite_eq_left shape, ite_eq_left pointBound, ite_eq_left fits]
  · apply hasShape_of_length _ _ _ shape.1 (by have := shape.2.1; omega)
    apply Zkc.Polynomial.Multilinear.restrictPrefixValues_length_mul
    simpa only [Nat.sub_add_cancel fits] using shape.length

/-- Actual source composition follows the supplied coordinate order. -/
theorem process_ordered_append (xs : List F) (dimension columns : Nat)
    (first second : List F) (shape : HasShape xs dimension columns)
    (lengthBound : xs.length < indexLimit) (columnsBound : columns < indexLimit)
    (fits : (first ++ second).length ≤ dimension) :
    program.denote F G (prefixInputs xs dimension columns (first ++ second)) =
      .done (inputs (restrictPrefixValues (restrictPrefixValues xs first) second)
        (dimension - first.length - second.length) columns) := by
  have actual := (process_shape (G := G) xs dimension columns (first ++ second)
    shape lengthBound columnsBound fits).1
  simpa only [Zkc.Polynomial.Multilinear.restrictPrefixValues_append,
    List.length_append, Nat.sub_sub] using actual

/-- The residual scalar table fixes exactly the leading MSB-first prefix. -/
theorem process_msb (xs point : List F) (n : Nat)
    (table : Zkc.Polynomial.Multilinear.Table F (n + point.length))
    (decoded : Zkc.Polynomial.Multilinear.ofList? (n + point.length) xs = some table)
    (small : n + point.length < 64) (lengthBound : xs.length < indexLimit) :
    program.denote F G (prefixInputs xs (n + point.length) 1 point) =
        .done (inputs (restrictPrefixValues xs point) n 1) ∧
      Zkc.Polynomial.Multilinear.ofList? n (restrictPrefixValues xs point) =
        some (Zkc.Polynomial.Multilinear.fixPrefix point.length table
          (Zkc.Polynomial.coordinates point.length point)) := by
  have shape : HasShape xs (n + point.length) 1 := hasShape_of_length _ _ _ (by decide) small
    (by simpa only [Nat.mul_one] using Zkc.Polynomial.Multilinear.ofList?_length xs table decoded)
  constructor
  · simpa only [Nat.add_sub_cancel] using
      (process_shape (G := G) xs (n + point.length) 1 point shape lengthBound
        (by decide +kernel) (by omega)).1
  · exact Zkc.Polynomial.Multilinear.ofList?_restrictPrefixValues xs point table decoded

end ZkcExamples.Structured.MapPrefix
