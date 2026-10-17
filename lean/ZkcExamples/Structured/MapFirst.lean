module

public import ZkcExamples.Structured.MapFirstTable

@[expose] public section

/-! Complete checked First source contract. The table guard is evaluated before
positive dimension, contiguous split, the scalar map and ordered projections. -/
namespace ZkcExamples.Structured.MapFirst
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary MapFirstLaws
open MapFirstBodies MapFirstViews MapFirstTable
open Zkc.Polynomial.Multilinear (restrictValues)
set_option smartUnfolding false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false in
theorem wrapper_equation (xs : List F) (dimension columns : Nat) (r : F)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    invoke (program.payload.meanings F G) wrapperHelper (firstInputs xs dimension columns r) =
      if HasShape xs dimension columns then
        if 0 < dimension then .done (inputs (restrictValues xs r) (dimension - 1) columns)
        else .halt .reject
      else .halt .reject := by
  refine (Evaluation.payload_invoke_body_view (F := F) (G := G) SiteObservations.closed
    program.payload wrapperDefinition wrapper_member
    wrapperBody wrapper_exact (firstInputs xs dimension columns r)).trans ?_
  exact MapFirstLaws.wrapper_body _ table_equation valuesRealization_equation
    variablesRealization_equation widthRealization_equation first_equation
    xs dimension columns r lengthBound dimensionBound columnsBound

set_option backward.isDefEq.respectTransparency false in
/-- Universal equation of the complete retained singleton protocol's checked projection. -/
theorem process_equation (xs : List F) (dimension columns : Nat) (r : F)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    program.denote F G (firstInputs xs dimension columns r) =
      if HasShape xs dimension columns then
        if 0 < dimension then .done (inputs (restrictValues xs r) (dimension - 1) columns)
        else .halt .reject
      else .halt .reject := by
  refine (Evaluation.payload_denote_body_view (F := F) (G := G) SiteObservations.closed
    program.payload entryBody entry_exact (firstInputs xs dimension columns r)).trans ?_
  exact (MapFirstLaws.entry_body _ xs dimension columns r).trans
    (wrapper_equation xs dimension columns r lengthBound dimensionBound columnsBound)

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The authored modulus/quotient test is precisely the table size contract. -/
theorem shape_iff (xs : List F) (dimension columns : Nat) :
    HasShape xs dimension columns ↔
      0 < columns ∧ dimension < 64 ∧ xs.length = 2 ^ dimension * columns := by
  constructor
  · intro shape
    exact ⟨shape.1, shape.2.1, shape.length⟩
  · rintro ⟨positive, small, size⟩
    exact hasShape_of_length xs dimension columns positive small size

set_option backward.isDefEq.respectTransparency false in
/-- The full source equation with every authored table validation exposed. -/
theorem process_checked_equation (xs : List F) (dimension columns : Nat) (r : F)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    program.denote F G (firstInputs xs dimension columns r) =
      if 0 < columns ∧ dimension < 64 ∧ xs.length = 2 ^ dimension * columns then
        if 0 < dimension then .done (inputs (List.zipWith (fun lo hi => lo + (hi - lo) * r)
          (xs.take (xs.length / 2)) (xs.drop (xs.length / 2))) (dimension - 1) columns)
        else .halt .reject
      else .halt .reject := by
  simpa only [shape_iff, restrictValues] using
    process_equation (G := G) xs dimension columns r lengthBound dimensionBound columnsBound

set_option backward.isDefEq.respectTransparency false in
/-- Valid source execution preserves the exact flattened shape and output ABI. -/
theorem process_shape (xs : List F) (dimension columns : Nat) (r : F)
    (shape : HasShape xs dimension columns) (positive : 0 < dimension)
    (lengthBound : xs.length < indexLimit) (columnsBound : columns < indexLimit) :
    program.denote F G (firstInputs xs dimension columns r) =
        .done (inputs (restrictValues xs r) (dimension - 1) columns) ∧
      HasShape (restrictValues xs r) (dimension - 1) columns := by
  constructor
  · rw [process_equation xs dimension columns r lengthBound
      (Nat.lt_trans shape.2.1 (by decide +kernel)) columnsBound, ite_eq_left shape, ite_eq_left positive]
  · exact restrict_shape xs dimension columns r shape positive

set_option backward.isDefEq.respectTransparency false in
/-- The returned scalar table fixes the leading MSB-first Boolean coordinate. -/
theorem process_msb (xs : List F) (n : Nat) (r : F)
    (table : Zkc.Polynomial.Multilinear.Table F (n + 1))
    (decoded : Zkc.Polynomial.Multilinear.ofList? (n + 1) xs = some table)
    (small : n + 1 < 64) (lengthBound : xs.length < indexLimit) :
    program.denote F G (firstInputs xs (n + 1) 1 r) =
        .done (inputs (restrictValues xs r) n 1) ∧
      Zkc.Polynomial.Multilinear.ofList? n (restrictValues xs r) =
        some (Zkc.Polynomial.Multilinear.fixFirst table r) := by
  have shape : HasShape xs (n + 1) 1 := hasShape_of_length _ _ _ (by decide) small
    (by simpa only [Nat.mul_one] using Zkc.Polynomial.Multilinear.ofList?_length xs table decoded)
  constructor
  · simpa only [Nat.add_sub_cancel] using
      (process_shape (G := G) xs (n + 1) 1 r shape (by omega) lengthBound (by decide +kernel)).1
  · exact Zkc.Polynomial.Multilinear.ofList?_restrictValues xs table r decoded

end ZkcExamples.Structured.MapFirst
