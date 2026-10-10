import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Zkc.Transformations.EncodingReuse

set_option autoImplicit false

namespace Tests.ScalarBytecode.HonestPolynomial
-- Generated from actual PIR check AST and whitelisted Python producer AST.
-- The generator/decoder is not proved correct in Lean.
variable {F : Type} [CommRing F]
def round1 (s g1_0 g1_1 g1_2 : F) : Prop := ((((g1_0 + g1_0) + g1_1) + g1_2) = s)
def round2 (g1_0 g1_1 g1_2 c1 g2_0 g2_1 g2_2 : F) : Prop := ((((g2_0 + g2_0) + g2_1) + g2_2) = (g1_0 + ((g1_1 * c1) + (g1_2 * (c1 * c1)))))
def final (g2_0 g2_1 g2_2 c1 c2 : F) : Prop := ((g2_0 + ((g2_1 * c2) + (g2_2 * (c2 * c2)))) = ((c1 * c2) + c1))
def first (F : Type) [CommRing F] : List F := [0, 3, 0]
def second (r : F) : List F := [r, r, 0]
theorem actual_honest_checks (r t : F) :
    round1 (3 : F) 0 3 0 ∧
    round2 0 3 0 r r r 0 ∧
    final r r 0 r t := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [round1, round2, final] <;> ring
-- This is a meaning theorem for arbitrary legal malicious coefficients.
theorem actual_round2_meaning (a b c r u v w : F) :
    round2 a b c r u v w ↔ (u + u + v + w = a + b*r + c*(r*r)) := by
  simp only [round2]; constructor <;> intro h <;> linear_combination h
theorem actual_cached_producer {S B : Type} (encode : F → List B)
    (absorb : S → List B → S) (draw : S → S × F) (initial : S) (claim : F) :
    Zkc.Transformations.EncodingReuse.cached encode absorb draw initial claim (first F) second =
    Zkc.Transformations.EncodingReuse.direct encode absorb draw initial claim (first F) second :=
  Zkc.Transformations.EncodingReuse.cache_encoding_preserves encode absorb draw initial claim (first F) second
theorem actual_join {S B : Type} (encode : F → List B)
    (absorb : S → List B → S) (draw : S → S × F) (initial : S) (t : F) :
    let r := (draw ((first F).foldl (fun s x => absorb s (encode x))
      (absorb initial (encode 3)))).2
    Zkc.Transformations.EncodingReuse.cached encode absorb draw initial (3 : F) (first F) second =
      Zkc.Transformations.EncodingReuse.direct encode absorb draw initial (3 : F) (first F) second ∧
    round1 (3 : F) 0 3 0 ∧ round2 0 3 0 r r r 0 ∧ final r r 0 r t := by
  exact ⟨actual_cached_producer encode absorb draw initial 3, actual_honest_checks _ t⟩
-- The honest table is DERIVED from final RHS xy+x, not decoded claim data.
theorem derived_table_round2 (r : F) :
    (1-r)*0+r*1 = r ∧ (1-r)*0+r*2 - ((1-r)*0+r*1) = r := by
  constructor <;> ring

end Tests.ScalarBytecode.HonestPolynomial
