module

public import ZkcSecurity.Realizations.Gkr.HonestLineHelpers

@[expose] public section

/-! The actual row-reset finite fold, including every checked increment. -/

namespace ZkcSecurity.Realizations.Gkr.HonestLine
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceViews GkrSourceLaws
open ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Polynomial.Multilinear CoefficientRows

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev shiftFold : FoldSpec :=
  (fold? GkrSourceBodies.scopedHelper86Body).get (by decide +kernel)

theorem shift_step_expansion (table : Meanings F G) (xs : List F)
    (previous value : F) (offset count : Nat) :
    GkrSourceBodies.helper62Body.denote (meaning F G table)
      (Values.cons xs (.cons previous (.cons offset (.cons value (.cons count .nil))))).get =
      (primitiveOutcome (Primitive.evaluate (F := F) (G := G) .indexMod
        (.cons offset (.cons count .nil)))).bind fun remainder =>
      (primitiveOutcome (Primitive.evaluate (F := F) (G := G) .indexEqual
        (.cons (remainder.get .here) (.cons 0 .nil)))).bind fun boundary =>
      ((if boundary.get .here then
        (invoke table GkrSourceBodies.scopedHelper74Helper .nil).bind fun zero =>
          .done (.cons (zero.get .here) .nil)
       else .done (.cons previous .nil)) :
         PIR.Process _ (Values (assignment F G) [.field "bls12-381.fr"])).bind fun emitted =>
      (primitiveOutcome (Primitive.evaluate (F := F) (G := G) .indexAdd
        (.cons offset (.cons 1 .nil)))).bind fun next =>
      .done (.cons (xs ++ [emitted.get .here]) (.cons value (.cons (next.get .here) .nil))) := by
  derive_process using (exact branch_law _ _ _ _ _ _)

theorem shift_step_body (table : Meanings F G)
    (zero : invoke table GkrSourceBodies.scopedHelper74Helper .nil = .done (.cons 0 .nil))
    (xs : List F) (previous value : F) (offset count : Nat)
    (bound : offset + 1 < indexLimit) (countBound : count < indexLimit)
    (positive : 0 < count) :
    GkrSourceBodies.helper62Body.denote (meaning F G table)
      (Values.cons xs (.cons previous (.cons offset (.cons value (.cons count .nil))))).get =
      .done (.cons (xs ++ [if offset % count = 0 then 0 else previous])
        (.cons value (.cons (offset + 1) .nil))) := by
  have offsetBound : offset < indexLimit := by omega
  have remainderBound : offset % count < indexLimit :=
    lt_trans (Nat.mod_lt _ positive) countBound
  have nonzero : count ≠ 0 := Nat.ne_of_gt positive
  rw [shift_step_expansion]
  by_cases boundary : offset % count = 0 <;>
    simp only [Values.get, PIR.Process.bind, Primitive.evaluate, primitiveOutcome, checkedIndices,
      show 1 < indexLimit by decide +kernel, show 0 < indexLimit by decide +kernel,
      zero, nonzero, offsetBound, countBound, remainderBound,
      bound, boundary, ↓reduceIte, and_self, Bool.decide_true, decide_false, Bool.false_eq_true]

theorem shift_step (xs : List F) (previous value : F) (offset count : Nat) (source : List F)
    (bound : offset + 1 < indexLimit) (countBound : count < indexLimit)
    (positive : 0 < count) :
    invoke (helpers (G := G)) shiftFold.stepHelper
      (.cons xs (.cons previous (.cons offset (.cons value (.cons source (.cons count .nil)))))) =
      .done (.cons (xs ++ [if offset % count = 0 then 0 else previous])
        (.cons value (.cons (offset + 1) .nil))) := by
  change invoke (helpers (G := G)) GkrSourceBodies.helper63Helper _ = _
  rw [helper63_association.invoke unit.linked]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper62Helper
    (.cons xs (.cons previous (.cons offset (.cons value (.cons count .nil)))))).bind _ = _
  rw [helper62_association.invoke unit.linked,
    shift_step_body (helpers (F := F) (G := G)) HonestHelpers.zero_equation
      xs previous value offset count bound countBound positive]
  rfl

theorem shift_finite (values source xs : List F) (previous : F) (offset count : Nat)
    (bound : offset + values.length < indexLimit) (countBound : count < indexLimit)
    (positive : 0 < count) :
    Finite.fold (Evaluation.foldTransition (helpers (F := F) (G := G)) shiftFold
      (.cons source .nil) (.cons count .nil)) (values.map fun value => .cons value .nil)
      (.cons xs (.cons previous (.cons offset .nil))) =
      .done (.cons (xs ++ shiftAux count offset previous values)
        (.cons (values.getLastD previous) (.cons (offset + values.length) .nil))) := by
  induction values generalizing xs previous offset with
  | nil => simp [Finite.fold, shiftAux, List.getLastD]
  | cons value rest ih =>
    simp only [List.map_cons]
    rw [Finite.fold, Evaluation.foldTransition_unfiltered _ _ rfl]
    change (invoke (helpers (G := G)) shiftFold.stepHelper
      (.cons xs (.cons previous (.cons offset (.cons value (.cons source (.cons count .nil))))))).bind _ = _
    rw [shift_step xs previous value offset count source
      (by simp only [List.length_cons] at bound; omega) countBound positive]
    change Finite.fold _ (rest.map fun value => (Values.cons value .nil : Values (assignment F G) [.field "bls12-381.fr"]))
      (Values.cons (xs ++ [if offset % count = 0 then 0 else previous])
        (.cons value (.cons (offset + 1) .nil)) : Values (assignment F G) shiftFold.state) = _
    rw [ih _ value (offset + 1) (by simp only [List.length_cons] at bound; omega)]
    simp only [shiftAux, List.append_assoc, List.singleton_append, List.length_cons]
    have last : (value :: rest).getLastD previous = rest.getLastD value := by
      cases rest <;> rfl
    rw [last, show offset + 1 + rest.length = offset + (rest.length + 1) by omega]

theorem shift_fold (values xs : List F) (previous : F) (offset count : Nat)
    (bound : offset + values.length < indexLimit) (countBound : count < indexLimit)
    (positive : 0 < count) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper86Helper
      (.cons values (.cons xs (.cons previous (.cons offset (.cons count .nil))))) =
      .done (.cons (xs ++ shiftAux count offset previous values)
        (.cons (values.getLastD previous) (.cons (offset + values.length) .nil))) := by
  rw [scopedHelper86_association.invoke unit.linked]
  change (Evaluation.denoteFold _ shiftFold
    ((Values.cons values .nil).append
      ((Values.cons xs (.cons previous (.cons offset .nil))).append (.cons count .nil)))).bind _ = _
  rw [Evaluation.denoteFold_pack,
    show shiftFold.domain.admit (Values.cons values (.nil : Values (assignment F G) [])) =
      .returned (values.map fun value => .cons value .nil) from Evaluation.elements_admit _ _ _ _ _
        (by simpa only [Values.get] using (show values.length < indexLimit by omega)), Finite.admitThen,
    shift_finite values values xs previous offset count bound countBound positive]
  rfl

theorem shift_body (table : Meanings F G) (values : List F) (count : Nat) :
    GkrSourceBodies.helper66Body.denote (meaning F G table)
      (Values.cons values (.cons count .nil)).get =
      (invoke table GkrSourceBodies.scopedHelper74Helper .nil).bind fun zero =>
      (invoke table GkrSourceBodies.helper65Helper
        (.cons [] (.cons (zero.get .here) (.cons 0 (.cons count (.cons values .nil)))))).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  derive_process

theorem shift_wrapper_body (table : Meanings F G) (values xs : List F) (previous : F)
    (offset count : Nat) :
    GkrSourceBodies.helper65Body.denote (meaning F G table)
      (Values.cons xs (.cons previous (.cons offset (.cons count (.cons values .nil))))).get =
      (invoke table GkrSourceBodies.scopedHelper86Helper
        (.cons values (.cons xs (.cons previous (.cons offset (.cons count .nil)))))).bind
        fun result => .done (.cons (result.get .here)
          (.cons (result.get (.there .here)) (.cons (result.get (.there (.there .here))) .nil))) := by
  derive_process

/-- Exact success law for the actual `shift_rows`, not an assumed callback. -/
theorem shift_rows (values : List F) (count : Nat)
    (bound : values.length < indexLimit) (countBound : count < indexLimit)
    (positive : 0 < count) :
    invoke (helpers (G := G)) GkrSourceBodies.helper66Helper (.cons values (.cons count .nil)) =
      .done (.cons (shiftAux count 0 0 values) .nil) := by
  rw [helper66_association.invoke unit.linked, shift_body, HonestHelpers.zero_equation]
  simp only [PIR.Process.bind, Values.get]
  rw [helper65_association.invoke unit.linked, shift_wrapper_body,
    shift_fold values [] 0 0 count (by simpa using bound) countBound positive]
  rfl

end ZkcSecurity.Realizations.Gkr.HonestLine
