module

public import Zkc.Protocols.Sumcheck.Verifier
public import ZkcSecurity.Mathematics.Probability.UniformTape
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity.Finset

@[expose] public section

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck

open Zkc.Polynomial Zkc.Probability AlgebraicRounds
open AdaptiveTape (Tape)
open scoped BigOperators

variable {F : Type} {n : Nat}

variable [Field F] [Fintype F] [DecidableEq F]

/-- Acceptance under independent uniform challenges, with no distribution
assumption on prover messages. -/
def acceptance (p : Quadratic F n) (claim : F) (strategy : Strategy F n) : ℚ :=
  UniformTape.average n (fun coins => if verify p claim strategy coins then 1 else 0)

theorem acceptance_nonnegative (p : Quadratic F n) (claim : F) (strategy : Strategy F n) :
    0 ≤ acceptance p claim strategy :=
  UniformTape.nonnegative n _ (by intro coins; split <;> norm_num)

theorem acceptance_le_one (p : Quadratic F n) (claim : F) (strategy : Strategy F n) :
    acceptance p claim strategy ≤ 1 :=
  UniformTape.at_most_one n _ (by intro coins; split <;> norm_num)

theorem perfect_completeness (p : Quadratic F n) :
    acceptance p p.booleanSum (honest p) = 1 := by
  simp only [acceptance, completeness, ite_true]
  exact UniformTape.constant n 1

theorem acceptance_step (p : Quadratic F (n + 1)) (claim : F)
    (message : Message F) (next : F → Strategy F n) :
    acceptance p claim (.send message next) =
      if message.boundary = claim then
        (∑ r : F, acceptance (p.restrict r) (message.evaluate r) (next r)) / Fintype.card F
      else 0 := by
  by_cases passes : message.boundary = claim
  · simp only [acceptance, UniformTape.average, verify, ite_eq_left passes]
  · have all : (fun coins : Tape F (n + 1) =>
        if verify p claim (.send message next) coins then (1 : ℚ) else 0) = (fun _ => 0) := by
      funext coins
      rcases coins with ⟨r, tail⟩
      simp [verify, passes]
    rw [acceptance, all, UniformTape.constant, ite_eq_right passes]

/-- Ordinary soundness: a false claimed Boolean sum is accepted with probability
at most `2*n/|F|`. The bound is valid but may be uninformative in small fields.
This is neither knowledge soundness nor Fiat–Shamir security. -/
theorem soundness (p : Quadratic F n) (claim : F) (strategy : Strategy F n)
    (falseClaim : claim ≠ p.booleanSum) :
    acceptance p claim strategy ≤ (2 * (n : ℚ)) / Fintype.card F := by
  induction n generalizing claim with
  | zero =>
      cases p with
      | constant value =>
          cases strategy
          have differs : claim ≠ value := falseClaim
          simp [acceptance, UniformTape.average, verify, differs]
  | succ n ih =>
      cases strategy with
      | send message next =>
          rw [acceptance_step]
          by_cases passes : message.boundary = claim
          · rw [ite_eq_left passes]
            have different : message.boundary ≠ p.booleanSum := passes ▸ falseClaim
            have collisions : ((Finset.univ.filter fun r =>
                message.evaluate r = (p.restrict r).booleanSum).card : ℚ) ≤ 2 := by
              exact_mod_cast collision_card message p different
            have pointwise (r : F) :
                acceptance (p.restrict r) (message.evaluate r) (next r) ≤
                  (if message.evaluate r = (p.restrict r).booleanSum then (1 : ℚ) else 0) +
                    (2 * (n : ℚ)) / Fintype.card F := by
              by_cases same : message.evaluate r = (p.restrict r).booleanSum
              · rw [ite_eq_left same]
                exact (acceptance_le_one _ _ _).trans (le_add_of_nonneg_right
                  (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
                    (le_of_lt (UniformTape.card_positive (F := F)))))
              · rw [ite_eq_right same, zero_add]
                exact ih _ _ _ same
            calc
              _ ≤ (∑ r : F, ((if message.evaluate r = (p.restrict r).booleanSum then (1 : ℚ) else 0) +
                  (2 * (n : ℚ)) / Fintype.card F)) / Fintype.card F :=
                div_le_div_of_nonneg_right (Finset.sum_le_sum (fun r _ => pointwise r))
                  (le_of_lt (UniformTape.card_positive (F := F)))
              _ = ((Finset.univ.filter fun r =>
                  message.evaluate r = (p.restrict r).booleanSum).card + 2 * (n : ℚ)) /
                    Fintype.card F := by
                rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const]
                simp only [Finset.card_univ, nsmul_eq_mul]
                congr 1
                field_simp
              _ ≤ (2 + 2 * (n : ℚ)) / Fintype.card F :=
                div_le_div_of_nonneg_right (by linarith [collisions])
                  (le_of_lt (UniformTape.card_positive (F := F)))
              _ = _ := by push_cast; ring
          · rw [ite_eq_right passes]
            exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg (n + 1)))
              (le_of_lt (UniformTape.card_positive (F := F)))


end Zkc.Protocols.Sumcheck
