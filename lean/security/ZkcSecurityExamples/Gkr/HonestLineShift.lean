module

public import ZkcSecurityExamples.Gkr.HonestLineHelpers
public import ZkcSecurityExamples.Gkr.HonestLineCompanion

@[expose] public section

/-! The actual row-reset finite fold, including every checked increment. -/

namespace ZkcSecurity.Realizations.Gkr.HonestLine
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceViews GkrSourceLaws
open ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Polynomial.Multilinear CoefficientRows

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
attribute [local implicit_reducible] Collection.type Collection.element Op.arguments Op.results Op.regions

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

noncomputable abbrev shiftFold : FoldSpec := Goals.shiftSpec

theorem shift_step_body (table : Meanings F G)
    (zero : invoke table GkrSourceBodies.scopedHelper74Helper .nil = .done (.cons 0 .nil))
    (xs : List F) (previous value : F) (offset count : Nat)
    (bound : offset + 1 < indexLimit) (countBound : count < indexLimit)
    (positive : 0 < count) :
    GkrSourceBodies.helper62Body.denote (meaning F G table)
      (Goals.ShiftStep.Inputs.pack (Value := assignment F G) { initial := xs, previous, offset, value, count }).get =
      .done (Goals.ShiftStep.encode (ringModel F G)
        { values := xs ++ [if offset % count = 0 then 0 else previous],
          previous := value, offset := offset + 1 }) := by
  have offsetBound : offset < indexLimit := by omega
  have remainderBound : offset % count < indexLimit :=
    lt_trans (Nat.mod_lt _ positive) countBound
  have nonzero : count ≠ 0 := Nat.ne_of_gt positive
  named_equation Goals.ShiftStep over F G
  by_cases boundary : offset % count = 0 <;>
    simp only [Evaluation.invokeCallbackOn, Values.get, PIR.Process.bind, Primitive.evaluateOn, primitiveOutcome, checkedIndices,
      show 1 < indexLimit by decide +kernel, show 0 < indexLimit by decide +kernel,
      zero, nonzero, offsetBound, countBound, remainderBound,
      Environment.prepend, Environment.push, Values.get_cons, bound, boundary, ↓reduceIte, and_self, Bool.decide_true, decide_false, Bool.false_eq_true]

theorem shift_step (xs : List F) (previous value : F) (offset count : Nat) (source : List F)
    (bound : offset + 1 < indexLimit) (countBound : count < indexLimit)
    (positive : 0 < count) :
    invoke (helpers (G := G)) shiftFold.stepHelper
      (Goals.ShiftCallback.Inputs.pack (Value := assignment F G) { initial := xs, previous, offset, value, source, count }) =
      .done (Goals.ShiftStep.encode (ringModel F G)
        { values := xs ++ [if offset % count = 0 then 0 else previous],
          previous := value, offset := offset + 1 }) := by
  change invoke (helpers (G := G)) GkrSourceBodies.helper63Helper _ = _
  rw [helper63_association.invoke unit.linked]
  named_equation Goals.ShiftCallback over F G
  rw [helper62_association.invoke unit.linked,
    shift_step_body (helpers (F := F) (G := G)) HonestHelpers.zero_equation
      xs previous value offset count bound countBound positive]
  rfl

theorem shift_fold (values xs : List F) (previous : F) (offset count : Nat)
    (bound : offset + values.length < indexLimit) (countBound : count < indexLimit)
    (positive : 0 < count) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper86Helper
      (Goals.ShiftFold.Inputs.pack (Value := assignment F G) { source := values, initial := xs, previous, offset, count }) =
      .done (Goals.ShiftFold.encode (ringModel F G)
        { values := xs ++ shiftAux count offset previous values,
          previous := values.getLastD previous, offset := offset + values.length }) := by
  rw [scopedHelper86_association.invoke unit.linked]
  named_equation Goals.ShiftFold over F G
  let encode := fun state : Companion.ShiftState F => Goals.ShiftState.pack
    (Value := assignment F G) { values := state.values, previous := state.previous, offset := state.offset }
  have admitted : shiftFold.domain.admit (Goals.ShiftDomain.pack (Value := assignment F G) ⟨values⟩) =
      .returned (values.map fun value => Goals.ShiftItem.pack ⟨value⟩) := by
    simp [shiftFold, Goals.shiftSpec, Goals.ShiftFold.body, GkrSourceLaws.fold?, GkrSourceBodies.scopedHelper86Body,
      DomainSpec.admit, DomainBody.admit, DomainNode.admit, Collection.values,
      Goals.ShiftDomain.pack, Goals.ShiftItem.pack, Values.get,
      show values.length < indexLimit by omega, Finite.continueWith]
  have folded := Evaluation.denoteFoldOn_cursor_encode (carriers := uniformCarriers F G)
    (helpers (F := F) (G := G)) shiftFold (Goals.ShiftDomain.pack ⟨values⟩)
    (Goals.ShiftCaptures.pack ⟨count⟩) values (fun value => Goals.ShiftItem.pack ⟨value⟩)
    encode ⟨xs, previous, offset⟩ admitted
    (Companion.shiftTransition count) Companion.ShiftState.offset indexLimit
    (by intros; rfl) (by
      intro state value small
      rw [← Evaluation.foldTransition_eq_foldTransitionOn (F := F) (G := G),
        Evaluation.foldTransition_unfiltered _ _ rfl]
      exact shift_step state.values state.previous value state.offset count values
        small countBound positive)
    bound
  erw [folded]
  rw [Companion.shift_fold]
  rfl

/-- Exact success law for the actual `shift_rows`, not an assumed callback. -/
theorem shift_rows (values : List F) (count : Nat)
    (bound : values.length < indexLimit) (countBound : count < indexLimit)
    (positive : 0 < count) :
    invoke (helpers (G := G)) GkrSourceBodies.helper66Helper (Goals.Shift.Inputs.pack (Value := assignment F G) { source := values, count }) =
      .done (Goals.Shift.encode (ringModel F G) ⟨shiftAux count 0 0 values⟩) := by
  rw [helper66_association.invoke unit.linked]
  named_equation Goals.Shift over F G
  rw [HonestHelpers.zero_equation]
  simp only [Primitive.evaluateOn, primitiveOutcome,
    show 0 < indexLimit by decide +kernel, ↓reduceIte,
    PIR.Process.bind, Environment.prepend, Environment.push, Values.get_cons, Values.get]
  rw [helper65_association.invoke unit.linked]
  named_equation Goals.ShiftWrapper over F G
  rw [
    shift_fold values [] 0 0 count (by simpa using bound) countBound positive]
  rfl

end ZkcSecurity.Realizations.Gkr.HonestLine
