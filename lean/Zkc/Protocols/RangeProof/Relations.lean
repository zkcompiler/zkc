import Zkc.Algebra.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Algebraic connections in a range reduction

These identities connect bit witnesses, the constant term of the range
polynomial, and the parent of an inner-product argument. They do not infer
bitness from a commitment, prove extraction, or establish a sampling theorem.
In particular, the non-bit residual in `constant_term` is retained explicitly.
-/

set_option autoImplicit false

namespace Zkc.Protocols.RangeProof

open scoped BigOperators
open Zkc.Algebra

section Ring
variable {F I : Type*} [CommRing F]

/-- The bitness residual cannot be discarded for a malicious witness. -/
theorem constant_coordinate (a z y d : F) :
    (a - z) * (y * (a - 1 + z) + d) =
      y * (a * (a - 1)) + (z - z ^ 2) * y + (a - z) * d := by
  ring

/-- The constant term before using any bit-witness premise. -/
theorem constant_term [Fintype I] (a y d : I → F) (z : F) :
    (∑ i, (a i - z) * (y i * (a i - 1 + z) + d i)) =
      (∑ i, y i * (a i * (a i - 1))) +
      (z - z ^ 2) * (∑ i, y i) +
      (∑ i, a i * d i) - z * (∑ i, d i) := by
  simp_rw [constant_coordinate, sub_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/-- Bitness justifies removing precisely the first residual. Reconstructing the
claimed integer values from the weighted bits remains a separate connection. -/
theorem constant_term_of_bits [Fintype I] (a y d : I → F) (z : F)
    (bits : ∀ i, a i * (a i - 1) = 0) :
    (∑ i, (a i - z) * (y i * (a i - 1 + z) + d i)) =
      (z - z ^ 2) * (∑ i, y i) +
      (∑ i, a i * d i) - z * (∑ i, d i) := by
  rw [constant_term]
  simp only [bits, mul_zero, Finset.sum_const_zero, zero_add]

/-- Weighted reconstruction uses the actual party/bit indexing. Reordering a
flat vector is admissible only with a corresponding reindexing of these weights. -/
theorem weighted_reconstruction {J K : Type*} [Fintype J] [Fintype K]
    (bits : J → K → F) (party : J → F) (place : K → F) :
    (∑ j, ∑ k, bits j k * (party j * place k)) =
      ∑ j, party j * (∑ k, place k * bits j k) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end Ring

section Group
variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- Coordinate connection between the two vector commitments and the actual IPA
parent. The inverse is justified by the nonzero challenge, not by resampling. -/
theorem parent_coordinate (a sL sR x z y d : F) (hy : y ≠ 0) (G H : M) :
    a • G + (a - 1) • H + x • (sL • G + sR • H) - z • G +
      (z * y + d) • (y⁻¹ • H) =
    (a - z + x * sL) • G +
      (y * (a - 1 + z) + d + x * y * sR) • (y⁻¹ • H) := by
  match_scalars <;> field_simp <;> ring

/-- The scalar response removes the actual blindings of A and S. -/
theorem blinding_cancellation (alpha rho x : F) (B : M) :
    alpha • B + x • (rho • B) - (alpha + x * rho) • B = 0 := by
  simp only [smul_smul, add_smul, sub_self]

end Group

end Zkc.Protocols.RangeProof
