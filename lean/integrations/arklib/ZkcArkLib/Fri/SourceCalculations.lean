module

public import ZkcArkLib.Fri.Correspondence
public import Zkc.Source.Structured.IndexWords

@[expose] public section

/-! # Mathematical calculations for the current FRI helpers

These calculations follow `libraries/protocols/polynomial/fri/lib.zkc`: the unsigned
64-bit expression in `pair_low`, the two child addresses in `Fold`, the exact coefficient
padding in `padded`, and the prepared inverse coordinate in `fold_value`.

They prove only the mathematical sides of future source connections. In particular, they do
not provide typed-body association, `BodyIn`, primitive interpretation, oracle execution or
complete-outcome laws. The smooth-domain geometry in `prepared_inverse_fold` is a premise;
root names and successful source guards alone do not supply it.
-/

namespace ZkcSecurity.ArkLib.Fri

open Zkc.Source.Structured

/-- A low-bit mask selects the natural-order index of a binary folding pair. -/
theorem masked_pair_index (position m : ℕ) :
    position &&& (2 ^ m - 1) = position % 2 ^ m :=
  Nat.and_two_pow_sub_one_eq_mod position m

/-- Both children of a masked binary pair are in the original word. -/
theorem pair_indices_bounded (position m : ℕ) :
    position &&& (2 ^ m - 1) < 2 ^ m ∧
      (position &&& (2 ^ m - 1)) + 2 ^ m < 2 ^ (m + 1) := by
  rw [masked_pair_index]
  have low := Nat.mod_lt position (by positivity : 0 < 2 ^ m)
  rw [pow_succ]
  omega

/-- The exact total-word `pair_low` expression on a representable source index. -/
theorem machine_pair_low (position m : ℕ) (size : m + 1 ≤ 63)
    (representable : position < wordModulus) :
    bitAnd position (wrappingSubtract (logicalShiftRight (2 ^ (m + 1)) 1) 1) =
      position % 2 ^ m := by
  have rows : 2 ^ (m + 1) < wordModulus :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have half : 2 ^ m < wordModulus := by
    apply lt_trans _ rows
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have shifted : logicalShiftRight (2 ^ (m + 1)) 1 = 2 ^ m := by
    rw [logicalShiftRight_of_lt _ (by decide), Nat.mod_eq_of_lt rows]
    simp [pow_succ]
  rw [shifted, wrappingSubtract_of_le (b := 1) half (by
    have := Nat.two_pow_pos m
    omega)]
  unfold bitAnd
  rw [Nat.mod_eq_of_lt representable, Nat.mod_eq_of_lt (by omega)]
  exact masked_pair_index position m

/-- The high child addition cannot wrap under the source log-size bound. -/
theorem machine_high_index (position m : ℕ) (size : m + 1 ≤ 63) :
    wrappingAdd (position % 2 ^ m) (2 ^ m) = position % 2 ^ m + 2 ^ m := by
  have rows : 2 ^ (m + 1) < wordModulus :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have bounds := (pair_indices_bounded position m).2
  rw [masked_pair_index] at bounds
  exact Nat.mod_eq_of_lt (bounds.trans rows)

variable {F : Type} [Field F]

/-- Appending any number of zero coefficients preserves ascending Horner evaluation. -/
theorem evaluate_zero_padding (coefficients : List F) (padding : ℕ) (x : F) :
    evaluate (coefficients ++ List.replicate padding 0) x = evaluate coefficients x := by
  have zeroes : ∀ count : ℕ,
      (List.replicate count (0 : F)).foldr (fun coefficient value ↦ coefficient + x * value) 0 =
        0 := by
    intro count
    induction count with
    | zero => rfl
    | succ count ih =>
        simp only [List.replicate_succ, List.foldr_cons, ih, mul_zero, add_zero]
  unfold evaluate
  rw [List.foldr_append, zeroes]

/-- Padding reaches the exact requested length precisely when the input is not too long.
This mathematical expression does not implement the source's rejecting branch. -/
theorem exact_padded_length_iff (coefficients : List F) (count : ℕ) :
    (coefficients ++ List.replicate (count - coefficients.length) 0).length = count ↔
      coefficients.length ≤ count := by
  simp only [List.length_append, List.length_replicate]
  omega

/-- The successful source padding branch has exact length, rather than just an upper bound. -/
theorem exact_padded_length (coefficients : List F) (count : ℕ)
    (bounded : coefficients.length ≤ count) :
    (coefficients ++ List.replicate (count - coefficients.length) 0).length = count :=
  (exact_padded_length_iff coefficients count).mpr bounded

omit [Field F] in
/-- The current exact terminal length implies the historical verifier's weaker length guard. -/
theorem exact_coefficients_imply_old_bound (t : ℕ) (coefficients : List F)
    (exact : coefficients.length = 2 ^ t) : bounded t coefficients = true := by
  simp [bounded, exact]

variable [DecidableEq F]

/-- The prepared inverse used by the source fold gives ArkLib's binary fold, assuming the
actual domain is the stated natural-order coset. Field inversion is mathematical here. -/
theorem prepared_inverse_fold (roots : ℕ → F) {m : ℕ}
    (domain : Domain.SmoothCosetFftDomain (m + 1) F) (shift : F)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), domain i = point roots shift (m + 1) i)
    (word : Fin (2 ^ (m + 1)) → F) (beta : F) (low : Fin (2 ^ m)) :
    foldValue (word (lowIndex low)) (word (highIndex low)) beta (2 : F)⁻¹
        (shift⁻¹ * (roots (m + 1))⁻¹ ^ low.val) =
      ProximityGap.foldWord domain word 1 beta low := by
  simpa [foldedValue, point, mul_inv, inv_pow, one_add_one_eq_two, mul_comm] using
    foldedValue_eq roots domain shift geometry word beta low

omit [Field F] [DecidableEq F] in
/-- Query-ordinal checks determine the sampled vector, including duplicate positions.
They do not determine the whole initial word. -/
theorem associated_values_fixed {n s : ℕ} (initial : Fin (2 ^ n) → F)
    (positions : Fin s → Fin (2 ^ n)) (first : Fin s → F)
    (checks : ∀ query, initial (positions query) = first query) :
    (fun query ↦ initial (positions query)) = first := funext checks

end ZkcSecurity.ArkLib.Fri
