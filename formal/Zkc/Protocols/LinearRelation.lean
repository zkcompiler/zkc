import Zkc.Algebra.LinearCombination
import Mathlib.Algebra.Module.LinearMap.Prod
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Abel

/-! Sigma equations for a fixed linear map, specialized to committed vectors.

The extractor uses the same map, statement and first message in both accepting
equations. This is algebraic special soundness, not a knowledge reduction,
randomness theorem, native/source correspondence, hiding or Fiat-Shamir theorem.
-/

set_option autoImplicit false

namespace Zkc.Protocols.LinearRelation

open scoped BigOperators

variable {F X Y : Type*} [Field F]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]

def accepts (L : X →ₗ[F] Y) (y t : Y) (c : F) (z : X) : Prop :=
  L z = t + c • y

theorem complete (L : X →ₗ[F] Y) (x r : X) (c : F) :
    accepts L (L x) (L r) c (r + c • x) := by
  simp [accepts]

/-- Distinct challenges and two accepting equations yield a preimage of y.
Neither injectivity nor independence of the commitment bases is needed. -/
theorem extract (L : X →ₗ[F] Y) (y t : Y) (c c' : F) (z z' : X)
    (distinct : c ≠ c') (first : accepts L y t c z)
    (second : accepts L y t c' z') :
    L ((c - c')⁻¹ • (z - z')) = y := by
  have difference : L (z - z') = (c - c') • y := by
    rw [map_sub, first, second, sub_smul]
    abel
  rw [map_smul, difference, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr distinct), one_smul]

variable {G I J : Type*} [AddCommGroup G] [Module F G] [Fintype I]

/-- The existing finite weighted sum, viewed as a linear map in its weights. -/
def msmMap (bases : I → G) : (I → F) →ₗ[F] G where
  toFun x := Zkc.Algebra.linearCombination x bases
  map_add' x z := by
    simp [Zkc.Algebra.linearCombination, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp [Zkc.Algebra.linearCombination, Finset.smul_sum, smul_smul]

/-- Matrix rows are scalar-valued linear combinations of the same coordinates. -/
def matrixMap (matrix : J → I → F) : (I → F) →ₗ[F] (J → F) :=
  LinearMap.pi fun j => msmMap (matrix j)

def relationMap (bases : I → G) (matrix : J → I → F) :
    (I → F) →ₗ[F] (G × (J → F)) :=
  (msmMap bases).prod (matrixMap matrix)

/-- Explicit bridge: acceptance in the product map means the group equation
AND every matrix coordinate, using exactly the same first message (t,u).
This is a mathematical bridge, not an assertion about the native PIR decoder. -/
theorem accepts_iff (bases : I → G) (matrix : J → I → F)
    (commitment t : G) (b u : J → F) (c : F) (z : I → F) :
    accepts (relationMap bases matrix) (commitment, b) (t, u) c z ↔
      Zkc.Algebra.linearCombination z bases = t + c • commitment ∧
      ∀ j, (∑ i, matrix j i * z i) = u j + c * b j := by
  simp [accepts, relationMap, msmMap, matrixMap,
    Zkc.Algebra.linearCombination, Prod.ext_iff, funext_iff, mul_comm]

/-- The extracted vector opens C and satisfies all rows, even for singular A. -/
theorem extract_relation (bases : I → G) (matrix : J → I → F)
    (commitment t : G) (b u : J → F) (c c' : F) (z z' : I → F)
    (distinct : c ≠ c')
    (first : accepts (relationMap bases matrix) (commitment, b) (t, u) c z)
    (second : accepts (relationMap bases matrix) (commitment, b) (t, u) c' z') :
    let x := (c - c')⁻¹ • (z - z')
    Zkc.Algebra.linearCombination x bases = commitment ∧
      ∀ j, (∑ i, matrix j i * x i) = b j := by
  have result := extract (relationMap bases matrix) (commitment, b) (t, u)
    c c' z z' distinct first second
  change (relationMap bases matrix) ((c - c')⁻¹ • (z - z')) = (commitment, b) at result
  have components := Prod.mk.inj result
  constructor
  · exact components.1
  · intro j
    have row := congrFun components.2 j
    change (∑ i, (((c - c')⁻¹ • (z - z')) i) * matrix j i) = b j at row
    simpa only [mul_comm] using row

end Zkc.Protocols.LinearRelation
