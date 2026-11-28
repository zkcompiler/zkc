module

public import Mathlib.Data.List.OfFn

@[expose] public section

/-!
A sequence of a fixed size, as a function on its positions.

A valid value of a sequence type with a size is a list of that length. A proof about a program
that reads such a sequence at a position reads the list of a function: the entry at a position
below the size is the value of the function there, with no case for a position outside.

The last three lemmas are the steps of the two common invariants of a loop over the positions
of a sequence: a loop that collects a known list, and a loop that carries whether a statement
held at every position so far.
-/

/-- A list of `n` entries is the list of a function on the `n` positions. -/
theorem List.exists_ofFn_of_length {α : Type} (xs : List α) (n : ℕ) (length : xs.length = n) :
    ∃ f : Fin n → α, xs = List.ofFn f := by
  subst length
  exact ⟨xs.get, (List.ofFn_get xs).symm⟩

/-- The entry of the list of a function at a position below its size. -/
theorem List.getElem?_ofFn_of_lt {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (below : i < n) :
    (List.ofFn f)[i]? = some (f ⟨i, below⟩) := by
  simp [below]

/-- What a loop has collected, latest first, holds the first `i` values of a list in order; with
the next value of the list before it, it holds the first `i + 1`. The invariant of a loop that
collects a known list, and its step. -/
theorem List.collected_next {α : Type} (all collected : List α) (i : Nat) (x : α)
    (soFar : collected.reverse = all.take i) (next : all[i]? = some x) :
    (x :: collected).reverse = all.take (i + 1) := by
  rw [List.reverse_cons, soFar, List.take_add_one, next]
  rfl

/-- What was collected of a list after as many iterations as it is long is the list. -/
theorem List.collected_all {α : Type} (all collected : List α) (n : Nat) (length : all.length = n)
    (soFar : collected.reverse = all.take n) : collected.reverse = all := by
  rw [soFar, List.take_of_length_le (by omega)]

/-- A statement of the positions below `j + 1` is the statement of those below `j` and the
statement at `j`: the step of a loop that carries whether a statement held at every position so
far. -/
theorem Fin.forall_val_lt_succ {n : Nat} (P : Fin n → Prop) (j : Nat) (below : j < n) :
    (∀ q : Fin n, q.val < j + 1 → P q) ↔ (∀ q : Fin n, q.val < j → P q) ∧ P ⟨j, below⟩ := by
  refine ⟨fun h => ⟨fun q lt => h q (by omega), h ⟨j, below⟩ (Nat.lt_succ_self j)⟩, ?_⟩
  rintro ⟨before, at_⟩ q lt
  by_cases same : q.val = j
  · obtain rfl : q = ⟨j, below⟩ := Fin.ext same
    exact at_
  · exact before q (by omega)
