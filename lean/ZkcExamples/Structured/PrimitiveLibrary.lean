module

public import ZkcExamples.Structured.PrimitiveRows
public import ZkcExamples.Structured.PrimitiveExpansions
public import ZkcExamples.Structured.PrimitiveTableViews
public import ZkcExamples.Structured.PrimitiveHalvesViews

@[expose] public section

/-! Conditional shape, table and ordered-halves equations for exact library bodies. -/
namespace ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Source Zkc.Source.Structured
open PrimitiveShapeViews (shapeBody shapeHelper)
-- Local transparency options below elaborate dependent source-view aliases;
-- every resulting equation is still checked by the kernel.
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

set_option backward.isDefEq.respectTransparency false in
/-- Under explicit representation bounds, the complete checked helper returns
exactly the authored guard/modulus/quotient predicate. -/
theorem shape_body (table : Meanings F G) (less : LessLaw table) (rows : RowsLaw table)
    (xs : List F) (dimension columns : Nat)
    (lengthBound : xs.length < indexLimit) (dimensionBound : dimension < indexLimit)
    (columnsBound : columns < indexLimit) :
    shapeBody.denote (meaning F G table) (inputs xs dimension columns).get =
      .done (boolResult (decide (HasShape xs dimension columns))) := by
  rw [Evaluation.denote_meaning_eq_meaningOn]
  have result := ReferenceLibrary.Multilinear.Admission.shape_body (ringModel F G)
    "bls12-381.fr" MultilinearSourceBindings.common table xs dimension columns
    lengthBound dimensionBound columnsBound
    (less 0 columns (by decide +kernel) columnsBound)
    (less dimension 64 dimensionBound (by decide +kernel))
    (fun small => rows dimension small)
  simpa only [ReferenceLibrary.Multilinear.Admission.boolResult,
    ReferenceLibrary.Multilinear.Admission.HasShape, HasShape, boolResult,
    ReferenceLibrary.Multilinear.tableValues, inputs, PrimitiveShapeViews.shapeBody,
    MultilinearBodies.shapeBody, MultilinearSourceBindings.common] using result



/-- A zero column guard returns false without observing the vector or dimension. -/
theorem shape_zero_columns (table : Meanings F G) (less : LessLaw table)
    (xs : List F) (dimension : Nat) :
    shapeBody.denote (meaning F G table) (inputs xs dimension 0).get =
      .done (boolResult false) := by
  dsimp only [inputs, vector]
  rw [PrimitiveExpansions.shape_body]
  have first := less 0 0 (by decide +kernel) (by decide +kernel)
  simp [meaning, Evaluation.meaning,
    Values.get,
    SiteObservations.closed,
    SiteObservations.silent, PIR.Process.bind, Primitive.evaluate, primitiveOutcome,
    first, boolResult, show 0 < indexLimit by decide +kernel]

/-- The high-dimension guard also precedes every length, division and loop. -/
theorem shape_large_dimension (table : Meanings F G) (less : LessLaw table)
    (xs : List F) (dimension columns : Nat) (positive : 0 < columns)
    (columnsBound : columns < indexLimit) (dimensionBound : dimension < indexLimit)
    (large : ¬ dimension < 64) :
    shapeBody.denote (meaning F G table) (inputs xs dimension columns).get =
      .done (boolResult false) := by
  dsimp only [inputs, vector]
  rw [PrimitiveExpansions.shape_body]
  have first := less 0 columns (by decide +kernel) columnsBound
  have second := less dimension 64 dimensionBound (by decide +kernel)
  simp [meaning, Evaluation.meaning,
    Values.get,
    SiteObservations.closed,
    SiteObservations.silent, PIR.Process.bind, Primitive.evaluate, primitiveOutcome,
    first, second, boolResult, positive, large, show 0 < indexLimit by decide +kernel, show 64 < indexLimit by decide +kernel]

/-- An unrepresentable vector length exhausts only after both initial guards. -/
theorem shape_length_exhausted (table : Meanings F G) (less : LessLaw table)
    (xs : List F) (dimension columns : Nat) (positive : 0 < columns)
    (columnsBound : columns < indexLimit) (dimensionSmall : dimension < 64)
    (lengthInvalid : ¬ xs.length < indexLimit) :
    shapeBody.denote (meaning F G table) (inputs xs dimension columns).get = .halt .exhausted := by
  dsimp only [inputs, vector]
  rw [PrimitiveExpansions.shape_body]
  have first := less 0 columns (by decide +kernel) columnsBound
  have second := less dimension 64 (Nat.lt_trans dimensionSmall (by decide +kernel)) (by decide +kernel)
  simp [meaning, Evaluation.meaning,
    Values.get,
    SiteObservations.closed,
    SiteObservations.silent, PIR.Process.bind, Primitive.evaluate, primitiveOutcome,
    first, second, boolResult, positive, dimensionSmall, lengthInvalid, show 0 < indexLimit by decide +kernel, show 64 < indexLimit by decide +kernel]

/-- The table constructor returns the original ordered tuple or rejects. -/
theorem table_body (table : Meanings F G) (xs : List F) (dimension columns : Nat) (valid : Bool)
    (shape : invoke table shapeHelper (inputs xs dimension columns) = .done (boolResult valid)) :
    PrimitiveTableViews.tableBody.denote (meaning F G table) (inputs xs dimension columns).get =
      if valid then .done (inputs xs dimension columns) else .halt .reject := by
  dsimp only [inputs, vector]
  rw [PrimitiveExpansions.table_body]
  simp only [inputs] at shape
  cases valid <;>
    simp [meaning,
      Evaluation.meaning, Values.get, SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
      shape, boolResult]

/-- Halves checks positive dimension before executing the two-result split.
Columns are retained source inputs, but this helper itself never validates them. -/
theorem halves_body (table : Meanings F G) (less : LessLaw table)
    (xs : List F) (dimension columns : Nat) (dimensionBound : dimension < indexLimit) :
    PrimitiveHalvesViews.halvesBody.denote (meaning F G table) (inputs xs dimension columns).get =
      if 0 < dimension then
        if 0 < xs.length ∧ xs.length % 2 = 0 then
          .done (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil))
        else .halt .refused
      else .halt .reject := by
  dsimp only [inputs, vector]
  rw [PrimitiveExpansions.halves_body]
  have comparison := less 0 dimension (by decide +kernel) dimensionBound
  by_cases positive : 0 < dimension
  · by_cases divisible : 0 < xs.length ∧ xs.length % 2 = 0 <;>
      simp [meaning,
        Evaluation.meaning, Values.get, SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
        Primitive.evaluate, primitiveOutcome, comparison, boolResult, positive, divisible,
        show 0 < indexLimit by decide +kernel]
    all_goals rfl
  · simp [meaning,
      Evaluation.meaning, Values.get, SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
      Primitive.evaluate, primitiveOutcome, comparison, boolResult, positive,
      show 0 < indexLimit by decide +kernel]


/-- Source halves refuses an unrepresentable dimension before the positive guard. -/
theorem halves_dimension_refused (table : Meanings F G) (less : LessAllLaw table)
    (xs : List F) (dimension columns : Nat) (invalid : ¬ dimension < indexLimit) :
    PrimitiveHalvesViews.halvesBody.denote (meaning F G table) (inputs xs dimension columns).get = .halt .refused := by
  dsimp only [inputs, vector]
  rw [PrimitiveExpansions.halves_body]
  have comparison := less 0 dimension
  simp only [show 0 < indexLimit by decide +kernel, true_and, invalid, ite_false] at comparison
  simp only [Primitive.evaluate, show 0 < indexLimit by decide +kernel, ite_true,
    primitiveOutcome, PIR.Process.bind, Values.get, comparison]

/-- No raw table triple is excluded; width is unused and vector split has its own guard. -/
theorem halves_generic_body_all (table : Meanings F G) (less : LessAllLaw table)
    (xs : List F) (dimension columns : Nat) :
    PrimitiveHalvesViews.halvesBody.denote (meaning F G table) (inputs xs dimension columns).get =
      if dimension < indexLimit then
        if 0 < dimension then
          if 0 < xs.length ∧ xs.length % 2 = 0 then
            .done (.cons (xs.take (xs.length / 2)) (.cons (xs.drop (xs.length / 2)) .nil))
          else .halt .refused
        else .halt .reject
      else .halt .refused := by
  by_cases h : dimension < indexLimit
  · rw [ite_eq_left h]
    exact halves_body table (lessAll_bounded table less) xs dimension columns h
  · rw [ite_eq_right h]
    exact halves_dimension_refused table less xs dimension columns h


end ZkcExamples.Structured.PrimitiveLibrary
