import Examples.OpeningReduction.MultiplePoints
import Examples.OpeningReduction.Rounds

/-! Two fixed evaluation claims followed by a fresh batching scalar and Sumcheck.

The points and claimed values are fixed outside both averages. The prover may
adapt to the batching scalar and then to every subsequent Sumcheck challenge.
The terminal here tests the true residual; the PCS join is a separate theorem.
-/

set_option autoImplicit false

namespace Examples.OpeningReduction.Batching
open Zkc.Probability
open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem cancellation_card (a b : F) (nonzero : a ≠ 0 ∨ b ≠ 0) :
    (Finset.univ.filter fun alpha : F => a + alpha * b = 0).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro alpha ha beta hb
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  by_cases zero : b = 0
  · have := nonzero.resolve_right (by simpa only [not_ne_iff] using zero)
    simp only [zero, mul_zero, add_zero] at ha'
    exact False.elim (this ha')
  · apply mul_right_cancel₀ zero
    exact add_left_cancel (ha'.trans hb'.symm)

def acceptance {n : Nat} (table : Table F n) (u v : Fin n → F) (cu cv : F)
    (prover : F → Rounds.Strategy F n) : ℚ :=
  (∑ alpha : F, Rounds.acceptance (MultiplePoints.reduction table alpha u v)
    (cu + alpha * cv) (prover alpha)) / Fintype.card F

/-- Ordinary soundness for fixed input claims. The extra `1/|F|` accounts for
cancellation of their errors; the three-factor engine gives a conservative
`3*n/|F|` instead of exploiting this instance's degree-two structure. -/
theorem soundness {n : Nat} (table : Table F n) (u v : Fin n → F) (cu cv : F)
    (prover : F → Rounds.Strategy F n)
    (falseClaim : cu ≠ table.eval u ∨ cv ≠ table.eval v) :
    acceptance table u v cu cv prover ≤ (1 + 3 * (n : ℚ)) / Fintype.card F := by
  have nonzero : cu - table.eval u ≠ 0 ∨ cv - table.eval v ≠ 0 := by
    simpa only [sub_ne_zero] using falseClaim
  have collision_iff (alpha : F) :
      cu + alpha * cv = (MultiplePoints.reduction table alpha u v).booleanSum ↔
        (cu - table.eval u) + alpha * (cv - table.eval v) = 0 := by
    rw [MultiplePoints.reduction_sum]
    have identity : (cu - table.eval u) + alpha * (cv - table.eval v) =
        (cu + alpha * cv) - (table.eval u + alpha * table.eval v) := by ring
    rw [identity, sub_eq_zero]
  have collisions : ((Finset.univ.filter fun alpha : F =>
      cu + alpha * cv = (MultiplePoints.reduction table alpha u v).booleanSum).card : ℚ) ≤ 1 := by
    simpa only [collision_iff] using
      (show ((Finset.univ.filter fun alpha : F =>
        (cu - table.eval u) + alpha * (cv - table.eval v) = 0).card : ℚ) ≤ 1 by
          exact_mod_cast cancellation_card _ _ nonzero)
  have pointwise (alpha : F) :
      Rounds.acceptance (MultiplePoints.reduction table alpha u v) (cu + alpha * cv) (prover alpha) ≤
        (if cu + alpha * cv = (MultiplePoints.reduction table alpha u v).booleanSum then (1 : ℚ) else 0) +
          3 * (n : ℚ) / Fintype.card F := by
    split
    · exact (Rounds.acceptance_le_one _ _ _).trans (le_add_of_nonneg_right
        (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
          (le_of_lt (UniformTape.card_positive (F := F)))))
    · exact (Rounds.soundness _ _ _ (by assumption)).trans_eq (zero_add _).symm
  calc
    _ ≤ (∑ alpha : F,
        ((if cu + alpha * cv = (MultiplePoints.reduction table alpha u v).booleanSum then (1 : ℚ) else 0) +
          3 * (n : ℚ) / Fintype.card F)) / Fintype.card F :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun alpha _ => pointwise alpha))
        (le_of_lt (UniformTape.card_positive (F := F)))
    _ = ((Finset.univ.filter fun alpha : F =>
        cu + alpha * cv = (MultiplePoints.reduction table alpha u v).booleanSum).card + 3 * (n : ℚ)) /
          Fintype.card F := by
      rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const]
      simp only [Finset.card_univ, nsmul_eq_mul]
      congr 1
      field_simp
      simp only [mul_comm]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith [collisions])
      (le_of_lt (UniformTape.card_positive (F := F)))

omit [Fintype F] [DecidableEq F] in
/-- If the contributing claims can change after the batching scalar, the
same combined scalar can certify two false claims. -/
theorem adaptive_cancellation (alpha valueU valueV : F) :
    (valueU - alpha) + alpha * (valueV + 1) = valueU + alpha * valueV ∧
      valueV + 1 ≠ valueV := by
  constructor
  · ring
  · simp

end Examples.OpeningReduction.Batching
