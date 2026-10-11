import Zkc.Semantics.FiniteComputation.Algebra
import Zkc.Algebra.FiniteVectors
import Zkc.Algebra.LinearCombination
import Mathlib.Algebra.BigOperators.Fin

/-! Abstract consumers of ordered folds: dot, module-valued MSM and matrix
contraction. The vector comparison is between independent Lean definitions.
No concrete curve, scalar codec, matrix storage or native kernel is verified. -/

set_option autoImplicit false

namespace Zkc.FiniteComputation

open scoped BigOperators Matrix

/-- A bounded equal-length zip followed by multiplication and sum agrees with
the existing independent dot model. Native admission and error codes are not
identified; in particular these hypotheses cannot erase unused zip children. -/
theorem dot_admitted {F : Type} [CommRing F] (xs ys : List F)
    (shape : xs.length = ys.length) (bound : xs.length ≤ Zkc.Algebra.FiniteVectors.limit) :
    Local.runFold (.zip (.elements xs) (.elements ys)) (fun _ => .ok true)
      (fun pair => .ok (pair.1 * pair.2)) (fun state value => .ok (state + value)) 0 =
      Zkc.Algebra.FiniteVectors.dot xs ys := by
  rw [Local.runFold_total _ _ (Domain.zip_elements xs ys shape), sumMap_fold]
  have rightBound : ys.length ≤ Zkc.Algebra.FiniteVectors.limit := shape ▸ bound
  simp [sumMap, Zkc.Algebra.FiniteVectors.dot, Zkc.Algebra.FiniteVectors.zipExact,
    Zkc.Algebra.FiniteVectors.bounded, Zkc.Algebra.FiniteVectors.check, shape, rightBound]
  rfl

/-- Heterogeneous group/scalar zip realizes an ordered weighted sum after exact
shape admission. Module laws are mathematical assumptions about the meanings. -/
theorem msm_admitted {R M : Type} [Semiring R] [AddCommMonoid M] [Module R M]
    (points : List M) (scalars : List R) (shape : points.length = scalars.length) :
    Local.runFold (.zip (.elements points) (.elements scalars)) (fun _ => .ok true)
      (fun pair => .ok (pair.2 • pair.1)) (fun state value => .ok (state + value)) 0 =
      .ok (sumMap (points.zip scalars) (fun pair => pair.2 • pair.1)) := by
  rw [Local.runFold_total _ _ (Domain.zip_elements points scalars shape), sumMap_fold, zero_add]

/-- Scaling each weighted term can be fused into its scalar. Scalar order is
retained even for a noncommutative semiring. -/
theorem weighted_sum_scale {α R M : Type} [Semiring R] [AddCommMonoid M] [Module R M]
    (items : List α) (weights : α → R) (points : α → M) (factor : R) :
    factor • sumMap items (fun item => weights item • points item) =
      sumMap items (fun item => (factor * weights item) • points item) := by
  simp [sumMap, List.smul_sum, List.map_map, smul_smul, Function.comp_def]

/-- Enumerating all positions once connects the ordered sum to the existing
finite module contraction. Repeated *values* are retained at distinct indices. -/
theorem sumMap_linearCombination {R M : Type} [Semiring R] [AddCommMonoid M] [Module R M]
    {n : Nat} (weights : Fin n → R) (points : Fin n → M) :
    sumMap (List.finRange n) (fun i => weights i • points i) =
      Zkc.Algebra.linearCombination weights points := by
  simp [sumMap, ← List.ofFn_eq_map, List.sum_ofFn, Zkc.Algebra.linearCombination]

/-- Ordered row contractions may move to the weights under the existing module
laws. Explicit finite row/column indices fix the axes; no storage order is inferred.
The interchange uses commutative addition, beyond mere ordered-fold laws. -/
theorem matrix_contraction {R M : Type} [Semiring R] [AddCommMonoid M] [Module R M]
    {rows columns : Nat} (matrix : Matrix (Fin rows) (Fin columns) R)
    (weights : Fin rows → R) (points : Fin columns → M) :
    sumMap (List.finRange rows) (fun i => weights i •
      sumMap (List.finRange columns) (fun j => matrix i j • points j)) =
    sumMap (List.finRange columns) (fun j => (weights ᵥ* matrix) j • points j) := by
  simp only [sumMap_linearCombination]
  exact Zkc.Algebra.linearCombination_rows matrix weights points

end Zkc.FiniteComputation
