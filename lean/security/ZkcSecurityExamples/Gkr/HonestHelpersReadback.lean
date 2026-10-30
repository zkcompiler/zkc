module

public import ZkcSecurityExamples.Gkr.HonestHelpers

@[expose] public section

/-! Actual readback helpers scan a finite admitted vector. An out-of-range
read returns zero; index overflow and domain exhaustion remain failures. -/

namespace ZkcSecurity.Realizations.Gkr.HonestHelpers
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceViews GkrSourceLaws
open ZkcExamples.Structured.PrimitiveLibrary

set_option maxRecDepth 20000 in
structured_associations GkrSourceViews
  [helper46 := GkrSourceBodies.helper46, scopedHelper74 := GkrSourceBodies.scopedHelper74,
    helper53 := GkrSourceBodies.helper53, helper54 := GkrSourceBodies.helper54,
    scopedHelper82 := GkrSourceBodies.scopedHelper82, helper56 := GkrSourceBodies.helper56,
    helper57 := GkrSourceBodies.helper57, helper70 := GkrSourceBodies.helper70]

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem zero_body (table : Meanings F G) :
    GkrSourceBodies.helper46Body.denote (meaning F G table) Values.nil.get =
      .done (.cons 0 .nil) := by
  simp [GkrSourceBodies.helper46Body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Regions.denote, Environment.prepend,
    Environment.push, Values.get, PIR.Process.bind, SiteObservations.closed,
    SiteObservations.silent]

theorem zero_equation :
    invoke (helpers (F := F) (G := G)) GkrSourceBodies.scopedHelper74Helper .nil =
      .done (.cons 0 .nil) := by
  rw [scopedHelper74_association.invoke unit.linked]
  change (invoke (helpers (F := F) (G := G)) GkrSourceBodies.helper46Helper .nil).bind _ = _
  rw [helper46_association.invoke unit.linked, zero_body]
  rfl

abbrev readFold : FoldSpec :=
  (fold? GkrSourceBodies.scopedHelper82Body).get (by decide +kernel)

theorem read_step_body (table : Meanings F G) (current value : F) (index position : Nat)
    (indexBound : index + 1 < indexLimit) (positionBound : position < indexLimit) :
    GkrSourceBodies.helper53Body.denote (meaning F G table)
      (Values.cons current (.cons index (.cons value (.cons position .nil)))).get =
        .done (.cons (if index = position then value else current) (.cons (index + 1) .nil)) := by
  have indexSmall : index < indexLimit := by omega
  by_cases eq : index = position <;>
    simp_all [GkrSourceBodies.helper53Body, Region.denote, meaning, Evaluation.meaning,
      Evaluation.operation, Operands.eval, Regions.denote, Values.get_cons, Values.get,
      Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
      PIR.Process.bind, Primitive.evaluate, primitiveOutcome, checkedIndices,
      indexSmall, positionBound, indexBound, show 1 < indexLimit by decide +kernel, eq,
      Evaluation.invokeCallback]
  all_goals rfl

theorem read_step (current value : F) (index position : Nat) (source : List F)
    (indexBound : index + 1 < indexLimit) (positionBound : position < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper54Helper
      (.cons current (.cons index (.cons value (.cons source (.cons position .nil))))) =
        .done (.cons (if index = position then value else current) (.cons (index + 1) .nil)) := by
  rw [helper54_association.invoke unit.linked]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper53Helper
    (.cons current (.cons index (.cons value (.cons position .nil))))).bind _ = _
  rw [helper53_association.invoke unit.linked, read_step_body _ current value index position indexBound positionBound]
  rfl

def readTransition (position : Nat) (state : F × Nat) (value : F) : F × Nat :=
  (if state.2 = position then value else state.1, state.2 + 1)

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem readTransition_fold (xs : List F) (position offset : Nat) (current : F) :
    xs.foldl (readTransition position) (current, offset) =
      (if offset ≤ position then xs[position - offset]?.getD current else current, offset + xs.length) := by
  induction xs generalizing current offset with
  | nil => simp
  | cons value rest ih =>
    simp only [List.foldl_cons, readTransition, ih, List.length_cons]
    by_cases eq : offset = position
    · subst position
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · by_cases before : offset < position
      · have le : offset ≤ position := by omega
        have next : offset + 1 ≤ position := by omega
        have delta : position - offset = (position - (offset + 1)) + 1 := by omega
        simp only [eq, le, next, delta, ↓reduceIte, List.getElem?_cons_succ, Prod.mk.injEq, true_and]
        omega
      · have le : ¬ offset ≤ position := by omega
        have next : ¬ offset + 1 ≤ position := by omega
        simp only [eq, le, next, ↓reduceIte, Prod.mk.injEq, true_and]
        omega

private def readReference (position : Nat)
    (state : Values (assignment F G) readFold.state) (value : F) :
    Values (assignment F G) readFold.state :=
  .cons (if state.get (.there .here) = position then value else state.get .here)
    (.cons (state.get (.there .here) + 1) .nil)

private theorem read_finite (xs source : List F) (position offset : Nat) (current : F)
    (positionBound : position < indexLimit) (bound : offset + xs.length < indexLimit) :
    Finite.fold
      (Evaluation.foldTransition (helpers (F := F) (G := G)) readFold
        (.cons source .nil) (.cons position .nil)) (xs.map fun value => .cons value .nil)
        (.cons current (.cons offset .nil)) =
      .done (xs.foldl (readReference position) (.cons current (.cons offset .nil))) := by
  induction xs generalizing current offset with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.map_cons]
    rw [Finite.fold, Evaluation.foldTransition_unfiltered _ _ rfl]
    change (invoke (helpers (G := G)) GkrSourceBodies.helper54Helper
      (.cons current (.cons offset (.cons value (.cons source (.cons position .nil)))))).bind _ = _
    rw [read_step current value offset position source (by simpa using (show offset + 1 < indexLimit by simp only [List.length_cons] at bound; omega)) positionBound]
    change Finite.fold _ (rest.map fun value => (Values.cons value .nil : Values (assignment F G) [.field "bls12-381.fr"])) (Values.cons (if offset = position then value else current)
      (.cons (offset + 1) .nil) : Values (assignment F G) readFold.state) = _
    exact ih (offset + 1) _ (by simp only [List.length_cons] at bound; omega)

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem readReference_fold (xs : List F) (position offset : Nat) (current : F) :
    xs.foldl (readReference (G := G) position) (.cons current (.cons offset .nil)) =
      .cons (xs.foldl (readTransition position) (current, offset)).1
        (.cons (xs.foldl (readTransition position) (current, offset)).2 .nil) := by
  induction xs generalizing current offset with
  | nil => rfl
  | cons value rest ih =>
    exact ih (offset + 1) (if offset = position then value else current)

theorem read_fold (xs : List F) (position offset : Nat) (current : F)
    (positionBound : position < indexLimit) (bound : offset + xs.length < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.scopedHelper82Helper
      (.cons xs (.cons current (.cons offset (.cons position .nil)))) =
      .done (.cons (if offset ≤ position then xs[position - offset]?.getD current else current)
        (.cons (offset + xs.length) .nil)) := by
  have xsBound : xs.length < indexLimit := by omega
  rw [scopedHelper82_association.invoke unit.linked]
  change (Evaluation.denoteFold _ readFold
    ((Values.cons xs .nil).append ((Values.cons current (.cons offset .nil)).append (.cons position .nil)))).bind _ = _
  rw [Evaluation.denoteFold_pack,
    show readFold.domain.admit (Values.cons xs (.nil : Values (assignment F G) [])) =
      .returned (xs.map fun value => .cons value .nil) from Evaluation.elements_admit _ _ _ _ _ xsBound, Finite.admitThen,
    read_finite xs xs position offset current positionBound bound,
    readReference_fold, readTransition_fold]
  rfl

theorem element_body (table : Meanings F G) (xs : List F) (position : Nat) :
    GkrSourceBodies.helper57Body.denote (meaning F G table)
      (Values.cons xs (.cons position .nil)).get =
      (invoke table GkrSourceBodies.scopedHelper74Helper .nil).bind fun zero =>
      (invoke table GkrSourceBodies.helper56Helper
        (.cons (zero.get .here) (.cons 0 (.cons position (.cons xs .nil))))).bind fun result =>
      .done (.cons (result.get .here) .nil) := by
  derive_process

/-- Exact source readback, including out-of-range reads and an explicit bound
on the selected index, even when no element is selected. -/
theorem element_equation (xs : List F) (position : Nat)
    (xsBound : xs.length < indexLimit) (positionBound : position < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper57Helper (.cons xs (.cons position .nil)) =
      .done (.cons (xs[position]?.getD 0) .nil) := by
  rw [helper57_association.invoke unit.linked, element_body]
  rw [zero_equation]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper56Helper
    (.cons 0 (.cons 0 (.cons position (.cons xs .nil))))).bind _ = _
  rw [helper56_association.invoke unit.linked]
  change ((invoke (helpers (G := G)) GkrSourceBodies.scopedHelper82Helper
    (.cons xs (.cons 0 (.cons 0 (.cons position .nil))))).bind _).bind _ = _
  rw [read_fold xs position 0 0 positionBound (by simpa using xsBound)]
  simp [Nat.zero_le, Nat.sub_zero, PIR.Process.bind, Values.get_cons, Region.denote,
    Values.get, Operands.eval, Environment.prepend, Environment.push]

theorem element_after_equation (xs : List F) (position : Nat)
    (xsBound : xs.length < indexLimit) (positionBound : position + 1 < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper70Helper (.cons xs (.cons position .nil)) =
      .done (.cons (xs[position + 1]?.getD 0) .nil) := by
  rw [helper70_association.invoke unit.linked]
  have currentBound : position < indexLimit := by omega
  simp only [GkrSourceBodies.helper70Body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Regions.denote, Values.get_cons,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Process.bind, Primitive.evaluate, primitiveOutcome, checkedIndices,
    currentBound, positionBound, show 1 < indexLimit by decide +kernel, ite_true, and_self]
  rw [element_equation xs (position + 1) xsBound positionBound]
  rfl

/-- The successor primitive refuses overflow before scanning any vector. -/
theorem element_after_overflow (xs : List F) (position : Nat)
    (overflow : ¬ position + 1 < indexLimit) :
    invoke (helpers (G := G)) GkrSourceBodies.helper70Helper (.cons xs (.cons position .nil)) =
      .halt .refused := by
  rw [helper70_association.invoke unit.linked]
  simp only [GkrSourceBodies.helper70Body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Regions.denote, Values.get_cons,
    Environment.prepend, Environment.push, SiteObservations.closed, SiteObservations.silent,
    PIR.Process.bind, Primitive.evaluate, primitiveOutcome, checkedIndices,
    show 1 < indexLimit by decide +kernel, ite_true]
  simp [overflow, PIR.Process.bind]

end ZkcSecurity.Realizations.Gkr.HonestHelpers
