import Zkc.Algebra.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Inner-product argument folding

A nonzero round challenge preserves the group relation after adding the two
cross commitments. This is a completeness identity, not an extraction or
Fiat–Shamir theorem. Generator independence, sampling, encodings and native
group implementations are not asserted here.
-/

set_option autoImplicit false

namespace Zkc.Protocols.InnerProduct

open scoped BigOperators

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- One coordinate of the inner-product commitment relation. -/
theorem fold_coordinate (a b c d u : F) (hu : u ≠ 0) (G H G' H' Q : M) :
    (u * a + u⁻¹ * c) • (u⁻¹ • G + u • G') +
      (u⁻¹ * b + u * d) • (u • H + u⁻¹ • H') +
      ((u * a + u⁻¹ * c) * (u⁻¹ * b + u * d)) • Q =
    (a • G + c • G' + b • H + d • H' + (a * b + c * d) • Q) +
      u ^ 2 • (a • G' + d • H + (a * d) • Q) +
      (u⁻¹) ^ 2 • (c • G + b • H' + (c * b) • Q) := by
  match_scalars <;> field_simp <;> ring

/-- The commitment to two vectors and their inner product. -/
def commitment {I : Type*} [Fintype I]
    (a b : I → F) (G H : I → M) (Q : M) : M :=
  ∑ i, (a i • G i + b i • H i + (a i * b i) • Q)

/-- Folding halves and updating the parent commitment preserves the same
relation. A caller must connect this parent to its enclosing protocol's claim. -/
theorem fold_commitment {I : Type*} [Fintype I]
    (a b c d : I → F) (u : F) (hu : u ≠ 0)
    (G H G' H' : I → M) (Q : M) :
    commitment (fun i => u * a i + u⁻¹ * c i) (fun i => u⁻¹ * b i + u * d i)
      (fun i => u⁻¹ • G i + u • G' i) (fun i => u • H i + u⁻¹ • H' i) Q =
    commitment a b G H Q + commitment c d G' H' Q +
      u ^ 2 • commitment a d G' H Q + (u⁻¹) ^ 2 • commitment c b G H' Q := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => fold_coordinate (a i) (b i) (c i) (d i) u hu
      (G i) (H i) (G' i) (H' i) Q)
  dsimp only [commitment]
  rw [h]
  simp only [add_smul, smul_add, Finset.sum_add_distrib, ← Finset.smul_sum]
  abel

end Zkc.Protocols.InnerProduct
