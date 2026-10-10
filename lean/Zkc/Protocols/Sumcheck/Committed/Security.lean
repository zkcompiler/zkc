import Zkc.Protocols.Sumcheck.Committed.Connection

/-! Conditional soundness for honestly committed fixed factor tables.

Probabilities are over the full finite field product tape, with the statement,
setup, claim, callbacks and private state fixed first. The only external loss
premise bounds BadOpening in this very experiment. It is not an assumption of
committed protocol soundness, extraction, or independence of the two openings.
The mathematical arity-zero case is included; a PCS adapter may require n > 0.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Committed

open Zkc.Probability
open AdaptiveTape (Tape)
open scoped BigOperators

variable {F S : Type} {n : Nat} {scheme : Scheme F n}
variable [Field F] [Fintype F] [DecidableEq F]

/-- Exact probability on independent, uniform full-field challenge tapes. -/
noncomputable def probability (event : Tape F n → Prop) : ℚ := by
  classical
  exact UniformTape.average n (fun coins => if event coins then 1 else 0)

private theorem average_add {A : Type} [Fintype A] [Nonempty A] (count : Nat)
    (f g : Tape A count → ℚ) :
    UniformTape.average count (fun coins => f coins + g coins) =
      UniformTape.average count f + UniformTape.average count g := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [UniformTape.average, ih, Finset.sum_add_distrib, add_div]

omit [DecidableEq F] in
/-- An ordinary union bound needs no independent-event premise. -/
theorem probability_le_add (a b c : Tape F n → Prop)
    (included : ∀ coins, a coins → b coins ∨ c coins) :
    probability a ≤ probability b + probability c := by
  classical
  unfold probability
  rw [← average_add]
  apply UniformTape.monotone
  intro coins
  have inclusion := included coins
  by_cases ha : a coins <;> by_cases hb : b coins <;> by_cases hc : c coins <;> simp_all

noncomputable def acceptanceProbability (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (prover : S) : ℚ := probability (Accepted statement adversary claim prover)

noncomputable def badOpeningProbability (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (prover : S) : ℚ := probability (BadOpening statement adversary claim prover)

theorem acceptance_le_source_add_bad (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (prover : S) :
    acceptanceProbability statement adversary claim prover ≤
      Security.sourceAcceptance adversary.send adversary.react statement.polynomial claim prover +
        badOpeningProbability statement adversary claim prover := by
  have bound := probability_le_add (Accepted statement adversary claim prover)
    (fun coins => (Execution.run adversary.send adversary.react statement.polynomial claim prover
      (tapeList n coins)).outcome = .returned true)
    (BadOpening statement adversary claim prover)
    (accepted_source_or_bad statement adversary claim prover)
  have sourceEq : probability (fun coins : Tape F n =>
      (Execution.run adversary.send adversary.react statement.polynomial claim prover
        (tapeList n coins)).outcome = .returned true) =
      Security.sourceAcceptance adversary.send adversary.react statement.polynomial claim prover := by
    unfold probability Security.sourceAcceptance
    apply congrArg (UniformTape.average n)
    funext coins
    by_cases accepted : (Execution.run adversary.send adversary.react statement.polynomial claim prover
        (tapeList n coins)).outcome = .returned true
    · rw [if_pos accepted, if_pos accepted]
    · rw [if_neg accepted, if_neg accepted]
  rw [sourceEq] at bound
  exact bound

/-- Conditional on the stated PCS experiment bound, a false original sum is
accepted with probability at most 2n/|F| + epsilonOpen. The premise concerns
joint reached false openings, even when the terminal equality fails. -/
theorem soundness (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (prover : S) (epsilonOpen : ℚ)
    (falseClaim : claim ≠ statement.polynomial.booleanSum)
    (openingBound : badOpeningProbability statement adversary claim prover ≤ epsilonOpen) :
    acceptanceProbability statement adversary claim prover ≤
      (2 * (n : ℚ)) / Fintype.card F + epsilonOpen := by
  apply (acceptance_le_source_add_bad statement adversary claim prover).trans
  exact add_le_add
    (Security.source_soundness adversary.send adversary.react statement.polynomial claim prover falseClaim)
    openingBound

/-- Private seeds are sampled independently before verifier coins. The joint
opening bound may hold only after mixing seeds; a per-seed bound is unnecessary. -/
theorem randomized_soundness {Seed : Type} [Fintype Seed] [Nonempty Seed]
    (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (privateState : Seed → S) (epsilonOpen : ℚ)
    (falseClaim : claim ≠ statement.polynomial.booleanSum)
    (openingBound : UniformTape.average (F := Seed) 1 (fun seed =>
      badOpeningProbability statement adversary claim (privateState seed.1)) ≤ epsilonOpen) :
    UniformTape.average (F := Seed) 1 (fun seed =>
      acceptanceProbability statement adversary claim (privateState seed.1)) ≤
        (2 * (n : ℚ)) / Fintype.card F + epsilonOpen := by
  calc
    _ ≤ UniformTape.average (F := Seed) 1 (fun seed =>
        Security.sourceAcceptance adversary.send adversary.react statement.polynomial claim
          (privateState seed.1) + badOpeningProbability statement adversary claim (privateState seed.1)) :=
      UniformTape.monotone 1 _ _ (fun _ => acceptance_le_source_add_bad statement adversary claim _)
    _ = _ := average_add 1 _ _
    _ ≤ _ := add_le_add
      (Security.randomized_source_soundness adversary.send adversary.react privateState
        statement.polynomial claim falseClaim) openingBound

end Zkc.Protocols.Sumcheck.Committed
