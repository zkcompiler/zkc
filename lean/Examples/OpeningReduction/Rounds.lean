import Examples.OpeningReduction.Polynomial
import Zkc.Probability.UniformTape
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Finset

/-! Arbitrary-round ordinary soundness for a virtual product of three tables.

The reference verifier below is a mathematical test, not the deployed verifier:
it evaluates the residual product only to define the true-claim event. Source
execution returns opening obligations instead. Proofs adapt the maintained
Sumcheck induction to the independently instantiated cubic round laws.
-/

set_option autoImplicit false

namespace Examples.OpeningReduction.Rounds

open Zkc.Probability
open AdaptiveTape (Tape)
open scoped BigOperators

/-- A bounded adaptive prover. Fixed private randomness can be included in the
choice of this entire strategy; the fresh verifier tape is separate. -/
inductive Strategy (F : Type) : Nat → Type where
  | done : Strategy F 0
  | send {n : Nat} : Message F → (F → Strategy F n) → Strategy F (n + 1)

variable {F : Type} {n : Nat}

section Ring
variable [CommRing F] [DecidableEq F]

def verify : {n : Nat} → Factors F n → F → Strategy F n → Tape F n → Bool
  | 0, p, claim, .done, _ => decide (claim = p.booleanSum)
  | _ + 1, p, claim, .send message next, (challenge, tail) =>
      if message.boundary = claim then
        verify (p.restrict challenge) (message.eval challenge) (next challenge) tail
      else false

def honest : {n : Nat} → Factors F n → Strategy F n
  | 0, _ => .done
  | _ + 1, p => .send (p.round) (fun r => honest (p.restrict r))

theorem completeness (p : Factors F n) (coins : Tape F n) :
    verify p p.booleanSum (honest p) coins = true := by
  induction n with
  | zero => cases p; simp [verify, honest]
  | succ n ih =>
      rcases coins with ⟨r, tail⟩
      simp only [honest, verify, Factors.round_boundary, Factors.round_eval]
      exact ih _ tail

end Ring

variable [Field F] [Fintype F] [DecidableEq F]

/-- Acceptance under independent uniform challenges, with no distribution
assumption on prover messages. -/
def acceptance (p : Factors F n) (claim : F) (strategy : Strategy F n) : ℚ :=
  UniformTape.average n (fun coins => if verify p claim strategy coins then 1 else 0)

theorem acceptance_nonnegative (p : Factors F n) (claim : F) (strategy : Strategy F n) :
    0 ≤ acceptance p claim strategy :=
  UniformTape.nonnegative n _ (by intro coins; split <;> norm_num)

theorem acceptance_le_one (p : Factors F n) (claim : F) (strategy : Strategy F n) :
    acceptance p claim strategy ≤ 1 :=
  UniformTape.at_most_one n _ (by intro coins; split <;> norm_num)

theorem perfect_completeness (p : Factors F n) :
    acceptance p p.booleanSum (honest p) = 1 := by
  simp only [acceptance, completeness, if_true]
  exact UniformTape.constant n 1

theorem acceptance_step (p : Factors F (n + 1)) (claim : F)
    (message : Message F) (next : F → Strategy F n) :
    acceptance p claim (.send message next) =
      if message.boundary = claim then
        (∑ r : F, acceptance (p.restrict r) (message.eval r) (next r)) / Fintype.card F
      else 0 := by
  by_cases passes : message.boundary = claim
  · simp only [acceptance, UniformTape.average, verify, if_pos passes]
  · have all : (fun coins : Tape F (n + 1) =>
        if verify p claim (.send message next) coins then (1 : ℚ) else 0) = (fun _ => 0) := by
      funext coins
      rcases coins with ⟨r, tail⟩
      simp [verify, passes]
    rw [acceptance, all, UniformTape.constant, if_neg passes]

set_option maxHeartbeats 800000 in
/-- Ordinary soundness: a false claimed Boolean sum is accepted with probability
at most `3*n/|F|`. The bound is valid but may be uninformative in small fields.
This is neither knowledge soundness nor Fiat–Shamir security. -/
theorem soundness (p : Factors F n) (claim : F) (strategy : Strategy F n)
    (falseClaim : claim ≠ p.booleanSum) :
    acceptance p claim strategy ≤ (3 * (n : ℚ)) / Fintype.card F := by
  induction n generalizing claim with
  | zero =>
      cases strategy
      simp [acceptance, UniformTape.average, verify, falseClaim]
  | succ n ih =>
      cases strategy with
      | send message next =>
          rw [acceptance_step]
          by_cases passes : message.boundary = claim
          · rw [if_pos passes]
            have different : message.boundary ≠ p.booleanSum := passes ▸ falseClaim
            have collisions : ((Finset.univ.filter fun r =>
                message.eval r = (p.restrict r).booleanSum).card : ℚ) ≤ 3 := by
              have h := Message.collision_card message p.round (by simpa only [Factors.round_boundary] using different)
              simpa only [Factors.round_eval] using (show ((Finset.univ.filter fun r => message.eval r = p.round.eval r).card : ℚ) ≤ 3 by exact_mod_cast h)
            have pointwise (r : F) :
                acceptance (p.restrict r) (message.eval r) (next r) ≤
                  (if message.eval r = (p.restrict r).booleanSum then (1 : ℚ) else 0) +
                    (3 * (n : ℚ)) / Fintype.card F := by
              by_cases same : message.eval r = (p.restrict r).booleanSum
              · rw [if_pos same]
                exact (acceptance_le_one _ _ _).trans (le_add_of_nonneg_right
                  (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
                    (le_of_lt (UniformTape.card_positive (F := F)))))
              · rw [if_neg same, zero_add]
                exact ih _ _ _ same
            calc
              _ ≤ (∑ r : F, ((if message.eval r = (p.restrict r).booleanSum then (1 : ℚ) else 0) +
                  (3 * (n : ℚ)) / Fintype.card F)) / Fintype.card F :=
                div_le_div_of_nonneg_right (Finset.sum_le_sum (fun r _ => pointwise r))
                  (le_of_lt (UniformTape.card_positive (F := F)))
              _ = ((Finset.univ.filter fun r =>
                  message.eval r = (p.restrict r).booleanSum).card + 3 * (n : ℚ)) /
                    Fintype.card F := by
                rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const]
                simp only [Finset.card_univ, nsmul_eq_mul]
                congr 1
                field_simp
              _ ≤ (3 + 3 * (n : ℚ)) / Fintype.card F :=
                div_le_div_of_nonneg_right (by linarith [collisions])
                  (le_of_lt (UniformTape.card_positive (F := F)))
              _ = _ := by push_cast; ring
          · rw [if_neg passes]
            exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg (n + 1)))
              (le_of_lt (UniformTape.card_positive (F := F)))

end Examples.OpeningReduction.Rounds
