import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Matrix.Mul

/-!
# Finite linear combinations

The scalar case of `linearCombination_rows` is Mathlib's
`Matrix.dotProduct_mulVec`. The module-valued form also covers group contractions.
These are algebraic laws; allocation, shape admission, observation order and
implementation correspondence are separate obligations of a compiler consumer.
-/

set_option autoImplicit false

namespace Zkc.Algebra

open scoped BigOperators Matrix

variable {R M I J : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A finite weighted sum, with scalar coefficients and module-valued entries. -/
def linearCombination [Fintype I] (weights : I → R) (values : I → M) : M :=
  ∑ i, weights i • values i

/-- Move a linear map from the values to the contraction weights. The coefficient
order is meaningful even over a noncommutative semiring. -/
theorem linearCombination_rows [Fintype I] [Fintype J]
    (matrix : Matrix I J R) (weights : I → R) (values : J → M) :
    linearCombination weights (fun i => linearCombination (matrix i) values) =
      linearCombination (weights ᵥ* matrix) values := by
  simp only [linearCombination, Matrix.vecMul, dotProduct,
    Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- A diagonal map can be consumed without materializing scaled values. -/
theorem linearCombination_smul [Fintype I]
    (weights factors : I → R) (values : I → M) :
    linearCombination weights (fun i => factors i • values i) =
      linearCombination (fun i => weights i * factors i) values := by
  simp only [linearCombination, smul_smul]

/-- Nested contractions flatten into ordered Kronecker weights. Repeated use
gives the binary weight accumulation used by a flat inner-product verifier.
The outer index precedes the inner index; swapping them changes coordinates. -/
theorem linearCombination_product [Fintype I] [Fintype J]
    (outer : I → R) (inner : J → R) (values : I → J → M) :
    linearCombination outer (fun i => linearCombination inner (values i)) =
      linearCombination (fun p : I × J => outer p.1 * inner p.2)
        (fun p => values p.1 p.2) := by
  simp only [linearCombination, Finset.smul_sum, smul_smul,
    Fintype.sum_prod_type]

end Zkc.Algebra
