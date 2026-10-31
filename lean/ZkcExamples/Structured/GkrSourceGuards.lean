module

public import ZkcExamples.Structured.GkrSourceViews
public import Zkc.Protocols.Gkr.Source.VerifierHelperInstallation
public import Zkc.Protocols.Multilinear.Source.PrimitiveLibrary
public import Zkc.Source.Structured.BodyBindings
public import Zkc.Source.TypedABI

@[expose] public section

/-! Total laws for the helpers in the actual GKR admission prefix. Every law
is associated with a complete retained body, including its refusal branches. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace ZkcExamples.Structured.GkrSourceGuards
open Zkc.Source Zkc.Source.Structured
open PrimitiveShapeViews PrimitiveLibrary

structured_associations GkrSourceViews
  [helper2 := PrimitiveShapeViews.less,
    helper3 := PrimitiveShapeViews.rows,
    helper4 := PrimitiveShapeViews.shape,
    sourceHelper4 := GkrSourceBodies.sourceHelper4,
    helper18 := GkrSourceBodies.helper18]

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev helpers : Meanings F G := closedMeanings GkrSourceViews.unit.definitions

set_option linter.unusedSimpArgs false in
theorem index_add_all (a b : Nat) :
    invoke (helpers (F := F) (G := G)) GkrSourceBodies.sourceHelper4Helper
      (.cons a (.cons b .nil)) =
      if a < indexLimit ∧ b < indexLimit ∧ a + b < indexLimit then
        .done (.cons (a + b) .nil) else .halt .refused := by
  rw [sourceHelper4_association.invoke GkrSourceViews.unit.linked]
  by_cases aBound : a < indexLimit <;> by_cases bBound : b < indexLimit <;>
    by_cases sumBound : a + b < indexLimit <;>
      simp [GkrSourceBodies.sourceHelper4Body, Region.denote, meaning,
        Evaluation.meaning, Evaluation.operation, Operands.eval, Regions.denote,
        Values.get, Environment.prepend, Environment.push, SiteObservations.closed,
        SiteObservations.silent, PIR.Process.bind, Primitive.evaluate, primitiveOutcome,
        checkedIndices, aBound, bBound, sumBound]

theorem comparison_all : LessAllLaw (helpers (F := F) (G := G)) := by
  intro a b
  exact (helper2_association.invoke GkrSourceViews.unit.linked _).trans
    (less_generic_body_all _ a b)

theorem comparison_bounded : LessLaw (helpers (F := F) (G := G)) :=
  lessAll_bounded _ comparison_all

theorem rows_bounded : RowsLaw (helpers (F := F) (G := G)) := by
  intro dimension small
  exact (helper3_association.invoke GkrSourceViews.unit.linked _).trans
    (rows_body _ comparison_bounded dimension small)

theorem power_bounded (exponent : Nat) (small : exponent < 64) :
    invoke (helpers (F := F) (G := G)) GkrSourceBodies.helper18Helper (.cons exponent .nil) =
      .done (.cons (2 ^ exponent) .nil) :=
  (helper18_association.invoke GkrSourceViews.unit.linked _).trans
    (Zkc.Protocols.Gkr.Source.VerifierHelperInstallation.powerOfTwo_body _ exponent small)

/-- An unrepresentable dimension refuses before the vector is inspected. -/
theorem shape_dimension_refused (table : Meanings F G) (less : LessAllLaw table)
    (xs : List F) (dimension : Nat) (outside : ¬ dimension < indexLimit) :
    shapeBody.denote (meaning F G table) (inputs xs dimension 1).get = .halt .refused := by
  dsimp only [inputs, vector]
  rw [PrimitiveExpansions.shape_body]
  have first := less 0 1
  have second := less dimension 64
  simp only [show 0 < indexLimit by decide, show 1 < indexLimit by decide,
    show 64 < indexLimit by decide, and_true, outside, ite_false, ite_true] at first second
  simp [meaning, Evaluation.meaning, SiteObservations.closed,
    SiteObservations.silent, PIR.Process.bind, Primitive.evaluate, primitiveOutcome,
    first, second, boolResult, show 0 < indexLimit by decide, show 64 < indexLimit by decide]

/-- This equation covers arbitrary lists and arbitrary mathematical naturals;
none of its branches assumes successful source admission. -/
theorem shape_all (xs : List F) (dimension : Nat) :
    invoke (helpers (F := F) (G := G)) shapeHelper (inputs xs dimension 1) =
      if dimension < indexLimit then
        if dimension < 64 then
          if xs.length < indexLimit then
            .done (boolResult (decide (xs.length = 2 ^ dimension)))
          else .halt .exhausted
        else .done (boolResult false)
      else .halt .refused := by
  rw [helper4_association.invoke GkrSourceViews.unit.linked]
  by_cases representable : dimension < indexLimit
  · rw [ite_eq_left representable]
    by_cases small : dimension < 64
    · rw [ite_eq_left small]
      by_cases bounded : xs.length < indexLimit
      · rw [ite_eq_left bounded, shape_body _ comparison_bounded rows_bounded xs dimension 1
          bounded representable (by decide)]
        congr 2
        simp only [HasShape, Nat.mod_one, Nat.div_one,
          show 0 < 1 by decide, small, true_and]
      · rw [ite_eq_right bounded]
        exact shape_length_exhausted _ comparison_bounded xs dimension 1 (by decide)
          (by decide) small bounded
    · rw [ite_eq_right small]
      exact shape_large_dimension _ comparison_bounded xs dimension 1 (by decide)
        (by decide) representable small
  · rw [ite_eq_right representable]
    exact shape_dimension_refused _ comparison_all xs dimension representable

end ZkcExamples.Structured.GkrSourceGuards
