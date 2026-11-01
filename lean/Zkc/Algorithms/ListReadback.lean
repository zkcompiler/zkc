module

public import Zkc.Source.Finite
public import Mathlib.Data.List.Basic
public meta import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Deterministic list readback with a default accumulator and a checked cursor.
The cursor advances for every element, including elements after the selected
one. Empty scans perform no index checks. Admission belongs to the caller. -/
set_option autoImplicit false
namespace Zkc.Algorithms.ListReadback
open Zkc.Source

def transition {A : Type} (position : Nat) (state : A × Nat) (value : A) : A × Nat :=
  (if state.2 = position then value else state.1, state.2 + 1)

theorem fold {A : Type} (xs : List A) (position offset : Nat) (current : A) :
    xs.foldl (transition position) (current, offset) =
      (if offset ≤ position then xs[position - offset]?.getD current else current,
        offset + xs.length) := by
  induction xs generalizing current offset with
  | nil => simp
  | cons value rest ih =>
    simp only [List.foldl_cons, transition, ih, List.length_cons]
    by_cases eq : offset = position
    · subst position
      have next : ¬ offset + 1 ≤ offset := by omega
      simp [next, Nat.add_comm, Nat.add_left_comm]
    · by_cases before : offset < position
      · have le : offset ≤ position := by omega
        have next : offset + 1 ≤ position := by omega
        have delta : position - offset = (position - (offset + 1)) + 1 := by omega
        simp only [eq, le, next, delta, ↓reduceIte, List.getElem?_cons_succ,
          Prod.mk.injEq, true_and]
        omega
      · have le : ¬ offset ≤ position := by omega
        have next : ¬ offset + 1 ≤ position := by omega
        simp only [eq, le, next, ↓reduceIte, Prod.mk.injEq, true_and]
        omega

/-- Both operands of index equality and the incremented cursor must fit. -/
def step {A : Type} (limit position : Nat) (state : A × Nat) (value : A) :
    PIR.Outcome (A × Nat) :=
  if state.2 < limit ∧ position < limit ∧ state.2 + 1 < limit then
    .returned (transition position state value)
  else .stopped .refused

def scan {A : Type} (limit position : Nat) (xs : List A) (current : A) (offset : Nat) :
    PIR.Outcome (A × Nat) :=
  Finite.foldChecked (step limit position) xs (current, offset)

theorem scan_bounded {A : Type} (limit position : Nat) (xs : List A)
    (current : A) (offset : Nat) (selected : position < limit)
    (capacity : offset + xs.length < limit) :
    scan limit position xs current offset = .returned
      (if offset ≤ position then xs[position - offset]?.getD current else current,
        offset + xs.length) := by
  suffices total : scan limit position xs current offset =
      .returned (xs.foldl (transition position) (current, offset)) by rw [total, fold]
  induction xs generalizing current offset with
  | nil => rfl
  | cons value rest ih =>
    have small : offset < limit := by simp only [List.length_cons] at capacity; omega
    have next : offset + 1 < limit := by simp only [List.length_cons] at capacity; omega
    simp only [scan, Finite.foldChecked, step, small, selected, next, and_self,
      ↓reduceIte, Finite.continueWith, List.foldl_cons]
    exact ih _ (offset + 1) (by simp only [List.length_cons] at capacity; omega)

theorem scan_empty {A : Type} (limit position : Nat) (current : A) (offset : Nat) :
    scan limit position [] current offset = .returned (current, offset) := rfl

theorem scan_refused {A : Type} (limit position : Nat) (value : A) (rest : List A)
    (current : A) (offset : Nat) (invalid : ¬ (offset < limit ∧ position < limit ∧ offset + 1 < limit)) :
    scan limit position (value :: rest) current offset = .stopped .refused := by
  simp [scan, Finite.foldChecked, step, invalid, Finite.continueWith]

end Zkc.Algorithms.ListReadback
