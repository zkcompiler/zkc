import Zkc.Algebra.LinearCombination

/-!
# Ordered weights for repeated binary folding

The first challenge selects the outer (most significant) branch. Later
challenges select inner branches. This is the ordered Kronecker convention of
the flat verifier; it does not identify arbitrary array layouts or prove a
native implementation of indexing.
-/

set_option autoImplicit false

namespace Zkc.Protocols.InnerProduct

open Zkc.Algebra
open scoped BigOperators

def BinaryCoordinates : Nat → Type
  | 0 => Unit
  | n + 1 => Bool × BinaryCoordinates n

instance binaryCoordinatesFintype : (n : Nat) → Fintype (BinaryCoordinates n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 =>
      letI := binaryCoordinatesFintype n
      inferInstanceAs (Fintype (Bool × BinaryCoordinates n))

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- Left branches get the inverse weight and right branches the direct weight.
Swapping these functions supplies the other IPA basis family. -/
def binaryWeights : (n : Nat) → (Fin n → F) → BinaryCoordinates n → F
  | 0, _ => fun _ => 1
  | n + 1, challenges => fun i =>
      (if i.1 then challenges 0 else (challenges 0)⁻¹) *
        binaryWeights n (Fin.tail challenges) i.2

/-- Fold contiguous halves, one coordinate at a time. -/
def foldBasis : (n : Nat) → (Fin n → F) → (BinaryCoordinates n → M) → M
  | 0, _, values => values ()
  | n + 1, challenges, values =>
      foldBasis n (Fin.tail challenges) (fun rest =>
        (challenges 0)⁻¹ • values (false, rest) + challenges 0 • values (true, rest))

/-- The recursively folded basis equals one contraction against the ordered
product weights. Nonzero challenges are needed by the enclosing folding
protocol, but this expansion identity itself does not cancel inverses. -/
theorem foldBasis_eq_weights (n : Nat) (challenges : Fin n → F)
    (values : BinaryCoordinates n → M) :
    foldBasis n challenges values = linearCombination (binaryWeights n challenges) values := by
  induction n with
  | zero =>
      change values () = ∑ i : Unit, (1 : F) • values i
      rw [Fintype.sum_unique]
      exact (one_smul F (values ())).symm
  | succ n ih =>
      simp only [foldBasis]
      rw [ih]
      change (∑ i : BinaryCoordinates n, binaryWeights n (Fin.tail challenges) i •
        ((challenges 0)⁻¹ • values (false, i) + challenges 0 • values (true, i))) =
        ∑ i : Bool × BinaryCoordinates n,
          ((if i.1 then challenges 0 else (challenges 0)⁻¹) *
            binaryWeights n (Fin.tail challenges) i.2) • values i
      rw [Fintype.sum_prod_type]
      simp [smul_add, smul_smul, mul_comm, Finset.sum_add_distrib, add_comm]

end Zkc.Protocols.InnerProduct
