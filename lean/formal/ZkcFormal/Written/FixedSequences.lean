module

public import Mathlib.Data.List.OfFn

@[expose] public section

/-!
A sequence of a fixed size, as a function on its positions.

A valid value of a sequence type with a size is a list of that length. A proof about a program
that reads such a sequence at a position reads the list of a function: the entry at a position
below the size is the value of the function there, with no case for a position outside.
-/

/-- The entry of the list of a function at a position below its size. -/
theorem List.getElem?_ofFn_of_lt {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (below : i < n) :
    (List.ofFn f)[i]? = some (f ⟨i, below⟩) := by
  simp [below]
