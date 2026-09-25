import Zkc.Protocols.Sumcheck.Acceptance

/-! The actual round producer connected to direct residual evaluation.

The boundary exposes an ordered point and claimed value. The evaluator receives
the original polynomial through the fixed input. Both remain bound until the
connection is formed; no commitment scheme or challenge law is inferred.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Connection

open PIR Zkc.Polynomial
open Acceptance (Input)

structure Residual (F : Type) (n : Nat) where
  point : Fin n → F
  value : F

variable {F S : Type} [CommSemiring F] [DecidableEq F]

/-- The point is the actual tape's ordered point, and the value must be returned
by the maintained interactive round process. -/
def produces (send : S → AlgebraicRounds.Message F × S) (react : S → F → S)
    (input : Input F S) (residual : Residual F input.rounds) : Prop :=
  residual.point = tapePoint input.rounds input.coins ∧
    ((Source.rounds input.rounds ⟨input.claim, []⟩).run (Execution.handler send react)
      (input.prover, tapeList input.rounds input.coins)).outcome =
        .returned ⟨residual.value, tapeList input.rounds input.coins⟩

def roundConstraints (send : S → AlgebraicRounds.Message F × S) (react : S → F → S)
    (input : Input F S) (residual : Residual F input.rounds) (_ : Unit) : Prop :=
  residual.point = tapePoint input.rounds input.coins ∧
    finalClaim (Execution.strategy send react input.rounds input.prover) input.claim input.coins =
      some residual.value

theorem round_realization (send : S → AlgebraicRounds.Message F × S) (react : S → F → S) :
    Zkc.Realization.Acceptance (produces send react) (roundConstraints send react) := by
  have exactRound (input : Input F S) (residual : Residual F input.rounds) :
      roundConstraints send react input residual () ↔ produces send react input residual := by
    unfold roundConstraints produces
    rw [Execution.rounds_outcome]
    simp only [List.nil_append]
    cases finalClaim (Execution.strategy send react input.rounds input.prover) input.claim input.coins <;>
      simp
  exact ⟨fun input residual _ h => (exactRound input residual).mp h,
    fun input residual h => ⟨(), (exactRound input residual).mpr h⟩⟩

def evaluate (input : Input F S) (residual : Residual F input.rounds) : Bool :=
  decide (residual.value = input.polynomial.eval residual.point)

def evaluates (input : Input F S) (residual : Residual F input.rounds) : Prop :=
  evaluate input residual = true

def evaluationConstraints (input : Input F S) (residual : Residual F input.rounds)
    (_ : Unit) : Prop := residual.value = input.polynomial.eval residual.point

theorem evaluation_realization :
    Zkc.Realization.Acceptance (evaluates (F := F) (S := S)) evaluationConstraints where
  sound _ _ _ h := by simpa [evaluates, evaluate, evaluationConstraints] using h
  complete _ _ h := ⟨(), by simpa [evaluates, evaluate, evaluationConstraints] using h⟩

/-- Both component realizations meet at the same exposed residual. Their
local witnesses are separate; the connector cannot forget point or value. -/
theorem connected_realization (send : S → AlgebraicRounds.Message F × S) (react : S → F → S)
    (input : Input F S) :
    Relation.Connected (fun r => ∃ w, roundConstraints send react input r w) Eq
        (fun r => ∃ w, evaluationConstraints input r w) ↔
      Relation.Connected (produces send react input) Eq (evaluates input) :=
  (round_realization send react).connected evaluation_realization (fun _ => Eq) input

/-- Closing this connection is exactly the actual complete source's acceptance,
not merely compatibility between independently described predicates. -/
theorem connected_source (send : S → AlgebraicRounds.Message F × S) (react : S → F → S)
    (input : Input F S) :
    Relation.Connected (produces send react input) Eq (evaluates input) ↔
      Acceptance.sourceAccepts send react input () := by
  rw [← connected_realization]
  constructor
  · rintro ⟨left, right, ⟨_, point, produced⟩, same, ⟨_, checked⟩⟩
    subst right
    apply (Acceptance.realization send react).sound input () left.value
    exact ⟨produced, by simpa [evaluationConstraints, point] using checked⟩
  · intro accepted
    obtain ⟨value, produced, checked⟩ :=
      (Acceptance.realization send react).complete input () accepted
    exact ⟨⟨tapePoint input.rounds input.coins, value⟩,
      ⟨tapePoint input.rounds input.coins, value⟩, ⟨(), rfl, produced⟩,
      rfl, ⟨(), checked⟩⟩

theorem honest_connected {n : Nat} (polynomial : Quadratic F n)
    (coins : Zkc.Probability.AdaptiveTape.Tape F n) :
    Relation.Connected
      (produces Security.honestSend Security.honestReact (Acceptance.honestInput polynomial coins))
      Eq (evaluates (Acceptance.honestInput polynomial coins)) := by
  rw [connected_source]
  exact Security.source_completeness polynomial coins

end Zkc.Protocols.Sumcheck.Connection
