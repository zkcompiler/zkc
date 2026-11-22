module

public import Init.Grind.Ring.Field

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck.Algebra
open Lean.Grind

variable {F : Type} [CommRing F]

theorem mul_sub (a b c : F) : a * (b - c) = a*b - a*c := by
  rw [Ring.sub_eq_add_neg, Semiring.left_distrib, Ring.mul_neg, Ring.sub_eq_add_neg]

theorem sub_mul (a b c : F) : (a - b) * c = a*c - b*c := by
  rw [Ring.sub_eq_add_neg, Semiring.right_distrib, Ring.neg_mul, Ring.sub_eq_add_neg]

theorem add_sub_add (a b c d : F) : (a + b) - (c + d) = (a - c) + (b - d) := by
  simp only [Ring.sub_eq_add_neg, AddCommGroup.neg_add, Semiring.add_assoc,
    AddCommMonoid.add_left_comm]

theorem add_sub_add_left (a b c : F) : (a + b) - (a + c) = b - c := by
  rw [add_sub_add, AddCommGroup.sub_self, AddCommMonoid.zero_add]

theorem affine_difference (c k r s : F) : (c + r*k) - (c + s*k) = (r-s)*k := by
  rw [add_sub_add_left, sub_mul]

/-- Subtract two agreements to eliminate the constant term on each side. -/
theorem affine_slope_products {a b k l r s : F}
    (hr : a + r*k = b + r*l) (hs : a + s*k = b + s*l) : (r-s)*k = (r-s)*l := by
  rw [← affine_difference a, ← affine_difference b, hr, hs]

theorem difference_of_squares (r s : F) : (r-s)*(r+s) = r*r - s*s := by
  rw [sub_mul, Semiring.left_distrib, Semiring.left_distrib, CommSemiring.mul_comm s r,
    Semiring.add_comm (r*r), add_sub_add_left]

theorem cancel_left {F : Type} [Field F] {k a b : F} (nz : k ≠ 0) (h : k*a = k*b) : a = b := by
  have scaled := congrArg (k⁻¹ * ·) h
  simpa only [← Semiring.mul_assoc, Field.inv_mul_cancel nz, Semiring.one_mul] using scaled

end ZkcFormal.Interactive.Sumcheck.Algebra
