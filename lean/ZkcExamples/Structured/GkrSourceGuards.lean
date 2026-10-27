module

public import ZkcExamples.Structured.GkrSourceViews
public import ZkcExamples.Structured.PrimitiveLibrary
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

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem loop_states {I : PIR.Signature} (state captures : List Ty)
    (body : RegionFunction (assignment F G) I (.index :: (state ++ captures), state ++ captures))
    (count : Nat) (initial : Values (assignment F G) state)
    (captured : Values (assignment F G) captures) (states : Nat → Values (assignment F G) state)
    (start : states 0 = initial)
    (law : ∀ index, index < count →
      Evaluation.invokeCallback body (.cons index ((states index).append captured)) =
        .done ((states (index + 1)).append captured)) :
    Evaluation.denoteLoop state captures body 0 count initial captured = .done (states count) := by
  subst start
  simp only [Evaluation.denoteLoop, Finite.execute, Finite.Domain.admit, Finite.admitThen, Nat.sub_zero]
  have folded := Finite.fold_range_state
    (fun current index => (Evaluation.invokeCallback body (.cons index (current.append captured))).bind
      fun results => (.done (results.split state).1 : PIR.Process I _)) states 0 count (by
        intro index _ upper
        rw [law index (by omega)]
        simp only [PIR.Process.bind, Values.split_append])
  simpa using folded

set_option backward.isDefEq.respectTransparency false in
theorem power_bounded (exponent : Nat) (small : exponent < 64) :
    invoke (helpers (F := F) (G := G)) GkrSourceBodies.helper18Helper (.cons exponent .nil) =
      .done (.cons (2 ^ exponent) .nil) := by
  rw [helper18_association.invoke GkrSourceViews.unit.linked]
  simp only [GkrSourceBodies.helper18Body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Regions.denote, Values.get_cons, Environment.prepend,
    Environment.push, SiteObservations.closed, SiteObservations.silent, PIR.Process.bind,
    Primitive.evaluate, primitiveOutcome, show 1 < indexLimit by decide,
    show 0 < indexLimit by decide, ite_true, Values.split]
  rw [loop_states (F := F) (G := G) [.index] [] _ exponent _ .nil
    (fun index => .cons (2 ^ index) .nil) ?start ?law]
  · rfl
  case start => rfl
  case law =>
    intro index lower
    have current : 2 ^ index < indexLimit := power_bound index (by omega)
    have product : 2 ^ index * 2 < indexLimit := by
      simpa only [Nat.pow_succ] using power_bound (index + 1) (by omega : index + 1 < 64)
    simp only [Evaluation.invokeCallback, Values.get_cons, Environment.prepend, Environment.push,
      PIR.Process.bind, checkedIndices, current, product, show 2 < indexLimit by decide,
      and_self, ite_true, Values.append, Nat.pow_succ]

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
