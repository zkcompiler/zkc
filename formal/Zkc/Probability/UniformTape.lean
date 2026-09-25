import Zkc.Probability.AdaptiveTape
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fintype.BigOperators

/-! Independent uniform finite tapes, with executable rational expectations.

The product is explicit: every coordinate ranges over the whole finite sample
space independently. Adaptive decisions may use the consumed prefix; they do
not choose the unused tape distribution.
-/

set_option autoImplicit false

namespace Zkc.Probability.UniformTape

open AdaptiveTape
open scoped BigOperators

variable {F : Type} [Fintype F] [Nonempty F]

/-- Exact uniform expectation over a finite product tape. -/
def average : (n : Nat) → (Tape F n → ℚ) → ℚ
  | 0, f => f ()
  | n + 1, f => (∑ r : F, average n (fun tail => f (r, tail))) / Fintype.card F

theorem card_positive : (0 : ℚ) < Fintype.card F := by
  exact_mod_cast Fintype.card_pos

theorem constant (n : Nat) (c : ℚ) : average (F := F) n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [average, ih, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_div_cancel_left₀ c (ne_of_gt card_positive)

theorem monotone (n : Nat) (f g : Tape F n → ℚ) (le : ∀ coins, f coins ≤ g coins) :
    average n f ≤ average n g := by
  induction n with
  | zero => exact le ()
  | succ n ih =>
      exact div_le_div_of_nonneg_right
        (Finset.sum_le_sum (fun r _ => ih _ _ (fun tail => le (r, tail))))
        (le_of_lt card_positive)

theorem nonnegative (n : Nat) (f : Tape F n → ℚ) (positive : ∀ coins, 0 ≤ f coins) :
    0 ≤ average n f := by
  rw [← constant (F := F) n 0]
  exact monotone n _ _ positive

theorem at_most_one (n : Nat) (f : Tape F n → ℚ) (bounded : ∀ coins, f coins ≤ 1) :
    average n f ≤ 1 := by
  rw [← constant (F := F) n 1]
  exact monotone n _ _ bounded

omit [Nonempty F] in
/-- The recursive average is exactly the ordinary normalized sum over all
complete tapes, rather than a separate operational probability notion. -/
theorem average_eq_sum (n : Nat) (f : Tape F n → ℚ) :
    average n f = (∑ coins : Tape F n, f coins) / Fintype.card (Tape F n) := by
  induction n with
  | zero =>
      change f () = (∑ coins : Unit, f coins) / Fintype.card Unit
      erw [Fintype.sum_unique, Fintype.card_unique]
      simp
  | succ n ih =>
      simp only [average, ih]
      change (∑ r : F, (∑ tail : Tape F n, f (r, tail)) /
        Fintype.card (Tape F n)) / Fintype.card F =
          (∑ coins : F × Tape F n, f coins) / Fintype.card (F × Tape F n)
      erw [Fintype.sum_prod_type, ← Finset.sum_div, Fintype.card_prod, Nat.cast_mul]
      rw [div_div, mul_comm]

end Zkc.Probability.UniformTape
