import Zkc.Protocols.Sumcheck.Security
import Zkc.Realization.Acceptance

/-! Full-domain direct evaluation as an acceptance-realization client.

The actual input contains the original polynomial, its arity, claim, prover
state and ordered challenge tape. The reference target checks the residual by
evaluating that original polynomial directly. It is not a succinct commitment
scheme, a challenge-generation theorem or a native implementation.
-/

namespace Zkc.Protocols.Sumcheck.Acceptance

open Zkc.Polynomial Zkc.Probability
open AlgebraicRounds (Message)
open AdaptiveTape (Tape)

structure Input (F S : Type) where
  rounds : Nat
  polynomial : Quadratic F rounds
  claim : F
  prover : S
  coins : Tape F rounds

variable {F S : Type} [CommSemiring F] [DecidableEq F]

def sourceAccepts (send : S → Message F × S) (react : S → F → S)
    (input : Input F S) (_ : Unit) : Prop :=
  (Execution.run send react input.polynomial input.claim input.prover
    (tapeList input.rounds input.coins)).outcome = .returned true

/-- Every satisfying residual value must be both produced by these rounds and
equal to the evaluation of this input's original object at its actual point. -/
def constraints (send : S → Message F × S) (react : S → F → S)
    (input : Input F S) (_ : Unit) (value : F) : Prop :=
  finalClaim (Execution.strategy send react input.rounds input.prover) input.claim input.coins =
      some value ∧
    value = input.polynomial.eval (tapePoint input.rounds input.coins)

theorem realization (send : S → Message F × S) (react : S → F → S) :
    Zkc.Realization.Acceptance (sourceAccepts send react) (constraints send react) where
  sound input _ value valid := by
    rw [sourceAccepts, Execution.accepted_iff, verify_iff_final]
    exact valid.2 ▸ valid.1
  complete input _ accepted := by
    rw [sourceAccepts, Execution.accepted_iff, verify_iff_final] at accepted
    exact ⟨input.polynomial.eval (tapePoint input.rounds input.coins), accepted, rfl⟩

/-- Executable reference target, with no restriction to Boolean challenges. -/
def check (send : S → Message F × S) (react : S → F → S) (input : Input F S) : Bool :=
  match finalClaim (Execution.strategy send react input.rounds input.prover) input.claim input.coins with
  | none => false
  | some value => decide (value = input.polynomial.eval (tapePoint input.rounds input.coins))

theorem check_iff (send : S → Message F × S) (react : S → F → S) (input : Input F S) :
    check send react input = true ↔ sourceAccepts send react input () := by
  rw [sourceAccepts, Execution.accepted_iff, verify_iff_final]
  unfold check
  cases finalClaim (Execution.strategy send react input.rounds input.prover) input.claim input.coins <;>
    simp

def honestInput {n : Nat} (p : Quadratic F n) (coins : Tape F n) : Input F (Security.HonestState F) :=
  ⟨n, p, p.booleanSum, ⟨n, p⟩, coins⟩

/-- This constructive binding covers every tape in the maintained source's
admitted profile. Completeness is imported from the actual source theorem. -/
theorem honest_complete {n : Nat} (p : Quadratic F n) (coins : Tape F n) :
    check Security.honestSend Security.honestReact (honestInput p coins) = true := by
  rw [check_iff]
  exact Security.source_completeness p coins

end Zkc.Protocols.Sumcheck.Acceptance
