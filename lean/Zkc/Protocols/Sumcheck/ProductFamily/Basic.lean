import Zkc.Protocols.AlgebraicRounds.Scalar
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.ProductFamily
open Zkc.Protocols.AlgebraicRounds.Scalar
variable {F : Type} [CommRing F] [DecidableEq F]
-- The next message sees the first challenge, the prefix product and remaining
-- public dimension. Its a,b,c do not inspect the next challenge or any suffix.
def honestTail (first prefixProduct : F) : List F → List (Round F)
  | [] => []
  | r :: rs => ⟨first * 2 ^ rs.length, prefixProduct, 0, r⟩ ::
      honestTail first (prefixProduct * r) rs

omit [DecidableEq F] in
theorem honest_tail_length (x p : F) (rs : List F) :
    (honestTail x p rs).length = rs.length := by
  induction rs generalizing p with
  | nil => rfl
  | cons r rs ih => simp [honestTail, ih]

theorem honest_tail_run (x p : F) (rs : List F) :
    run (p + x * 2 ^ rs.length) (honestTail x p rs) =
      some (p * rs.prod + x) := by
  induction rs generalizing p with
  | nil => simp [honestTail, run]
  | cons r rs ih =>
    have hb : boundary (⟨x * 2 ^ rs.length, p, 0, r⟩ : Round F) =
        p + x * 2 ^ (r :: rs).length := by
      simp only [boundary, List.length_cons, pow_succ]; ring
    have hv : value (⟨x * 2 ^ rs.length, p, 0, r⟩ : Round F) =
        p * r + x * 2 ^ rs.length := by simp [value]; ring
    simp only [honestTail, run, hb, ↓reduceIte, hv]
    rw [ih]; simp [List.prod_cons, mul_assoc]

def honest (first : F) (rest : List F) : List (Round F) :=
  ⟨0, 1 + 2 ^ rest.length, 0, first⟩ :: honestTail first first rest

theorem honest_complete (first : F) (rest : List F) :
    run (1 + 2 ^ rest.length) (honest first rest) =
      some ((first :: rest).prod + first) := by
  have hv : value (⟨0, 1 + 2 ^ rest.length, 0, first⟩ : Round F) =
      first + first * 2 ^ rest.length := by simp [value]; ring
  simp only [honest, run, boundary, zero_add, add_zero, ↓reduceIte]
  rw [hv, honest_tail_run]; rfl

-- Finite Boolean summation gives the same initial claim as the source family.
-- Recursion expands all Boolean assignments, rather than assuming the answer.
def booleanSumTail (x p : F) : Nat → F
  | 0 => p + x
  | k+1 => booleanSumTail x 0 k + booleanSumTail x p k
omit [DecidableEq F] in
theorem boolean_sum_tail (x p : F) (k : Nat) :
    booleanSumTail x p k = p + x * 2 ^ k := by
  induction k generalizing p with
  | zero => simp [booleanSumTail]
  | succ k ih => simp only [booleanSumTail, ih, pow_succ]; ring
omit [DecidableEq F] in
theorem boolean_sum_family (k : Nat) :
    booleanSumTail (0 : F) 0 k + booleanSumTail (1 : F) 1 k = 1 + 2 ^ k := by
  simp [boolean_sum_tail]


end Zkc.Protocols.Sumcheck.ProductFamily
