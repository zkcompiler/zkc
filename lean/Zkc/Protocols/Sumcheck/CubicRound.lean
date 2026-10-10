import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Cubic sumcheck coefficient expansion

The four coefficients used by a weighted multiplication constraint. This
identity justifies the local round calculation; degree admission, boundary
checking and the enclosing commitment remain separate obligations.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck

open scoped BigOperators

variable {F I : Type*} [CommRing F]

theorem cubic_coordinate (e a b c de da db dc x : F) :
    (e + x * de) * ((a + x * da) * (b + x * db) - (c + x * dc)) =
    e * (a * b - c) +
      x * (e * (a * db + da * b - dc) + de * (a * b - c)) +
      x ^ 2 * (e * da * db + de * (a * db + da * b - dc)) +
      x ^ 3 * (de * da * db) := by
  ring

/-- Summing coordinate coefficients gives the exact round polynomial, including
the residual when the multiplication constraint is false. -/
theorem cubic_round [Fintype I] (e a b c de da db dc : I → F) (x : F) :
    (∑ i, (e i + x * de i) *
      ((a i + x * da i) * (b i + x * db i) - (c i + x * dc i))) =
    (∑ i, e i * (a i * b i - c i)) +
      x * (∑ i, (e i * (a i * db i + da i * b i - dc i) + de i * (a i * b i - c i))) +
      x ^ 2 * (∑ i, (e i * da i * db i + de i * (a i * db i + da i * b i - dc i))) +
      x ^ 3 * (∑ i, de i * da i * db i) := by
  simp_rw [cubic_coordinate]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

end Zkc.Protocols.Sumcheck
