import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Abel

/-! Affine observations of a uniform finite additive mask.

The range criterion and an explicit translation equivalence justify equality
of normalized finite counts. Concrete source and observer adequacy are separate.
-/

set_option autoImplicit false

namespace Zkc.Probability.AffineMask
variable {G H : Type} [AddCommGroup G] [AddCommGroup H]
def shiftedRange (L : G →+ H) (b : H) : Set H := {y | ∃ r, y=L r+b}
theorem coset_eq_iff (L : G →+ H) (b c : H) :
    shiftedRange L b = shiftedRange L c ↔ ∃ u, b-c=L u := by
  constructor
  · intro h
    have hb : b ∈ shiftedRange L b := ⟨0, by simp⟩
    rw [h] at hb
    obtain ⟨u, hu⟩ := hb
    exact ⟨u, by rw [hu]; abel⟩
  · rintro ⟨u, hu⟩
    have hb : b=L u+c := by rw [← hu]; abel
    ext y
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r+u, by simp [hb, map_add, add_assoc]⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r-u, by simp [hb, map_sub]; abel⟩
theorem mask_shift_bijective (u : G) : Function.Bijective (fun r : G => r+u) := by
  constructor
  · intro a b h; exact add_right_cancel h
  · intro b; exact ⟨b-u, by abel⟩
theorem coupled_observation (L : G →+ H) (b c : H) (u : G)
    (h : b-c=L u) (r : G) : L r+b = L (r+u)+c := by
  have hb : b=L u+c := by rw [← h]; abel
  simp [map_add, hb, add_assoc]

def fiberShift (L : G →+ H) (b c : H) (u : G) (h : b-c=L u) (y : H) :
    {r : G // L r+b=y} ≃ {r : G // L r+c=y} where
  toFun r := ⟨r.val+u, by rw [← coupled_observation L b c u h]; exact r.property⟩
  invFun r := ⟨r.val-u, by
    rw [coupled_observation L b c u h, sub_add_cancel]; exact r.property⟩
  left_inv r := by apply Subtype.ext; simp
  right_inv r := by apply Subtype.ext; simp

theorem uniform_mask_mass [Fintype G] [DecidableEq H]
    (L : G →+ H) (b c : H) (u : G) (h : b-c=L u) (y : H) :
    (Fintype.card {r : G // L r+b=y} : ℚ) / Fintype.card G =
    (Fintype.card {r : G // L r+c=y} : ℚ) / Fintype.card G := by
  rw [Fintype.card_congr (fiberShift L b c u h y)]

end Zkc.Probability.AffineMask
