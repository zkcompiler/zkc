import Zkc.Algebra.Representations
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace Tests.Representations
open Zkc.Algebra.Representations

-- Exact axis fixture over Q. Native tests separately execute BabyBear arithmetic.
example : lerp (5 : ℚ) (lerp 3 1 2) (lerp 3 4 8) = 64 := by
  norm_num [lerp]
example : lerp (3 : ℚ) (lerp 5 1 2) (lerp 5 4 8) = 60 := by
  norm_num [lerp]
example : lerp (5 : ℚ) (lerp 3 1 2) (lerp 3 4 8) ≠
    lerp (3 : ℚ) (lerp 5 1 2) (lerp 5 4 8) := by norm_num [lerp]

-- Finite cyclic control, not an Edwards model or an upstream security claim.
-- The full group has order 8*5; scalar reduction modulo 5 is not a module action
-- on all 40 elements. Clearing first differs from reducing the coefficient.
def rawAction (a : ZMod 5) (p : ZMod 40) : ZMod 40 := (a.val : ZMod 40) * p
example : rawAction (-1) (8 * 1) ≠ rawAction ((-1) * 8) 1 := by decide

-- Raw observations differ although their clearing images are equal.
example : (8 * (1 : ZMod 40)) = 8 * 6 ∧ (1 : ZMod 40) ≠ 6 := by decide

example (p : ℚ) : (8 : ℚ) • ((8 : ℚ)⁻¹ • p) = p :=
  inverse_eight_cancel (by norm_num) p

#print axioms decodeAndClear_observation
#print axioms same_image_not_raw
#print axioms scalar_reassociate
#print axioms inverse_eight_rewrite
#print axioms inverse_eight_cancel
#print axioms adjacent_half_transpose
#print axioms embedding_lerp
#print axioms reindex_inverse
#print axioms rotate_add
end Tests.Representations
