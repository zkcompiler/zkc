import Zkc.Protocols.Sumcheck.Preparation
import Zkc.Protocols.Sumcheck.Connection
import Zkc.Protocols.Sumcheck.Framed

set_option autoImplicit false

namespace Tests.SumcheckPreparation

open PIR Zkc.Source Zkc.Polynomial Zkc.Protocols
open Sumcheck
open AlgebraicRounds (Message)

variable {F S Q : Type} {n : Nat} [CommSemiring F] [DecidableEq F]

def price (_ : Sumcheck.Preparation.Key F) : Nat := 5
def prices : Zkc.Modules.Preparation.Prices (Sumcheck.Preparation.Key F) F :=
  ⟨fun _ _ => 1, fun _ _ => 1⟩

def inputs (p : Quadratic F n) (claim : F) : Values (Source.Value F n) [.accumulator, .polynomial] :=
  .cons ⟨claim, []⟩ (.cons p .nil)

def fresh (send : S → Message F × S) (react : S → F → S)
    (p : Quadratic F n) (claim : F) (prover : S) (coins : List F) :=
  ((Source.program n).denote (Sumcheck.Preparation.meaning AlgebraicRounds.Construction.fresh)
    (inputs p claim).get).run
      (PIR.Preparation.handler (Sumcheck.Preparation.provider price) prices .memo
        (AlgebraicRounds.Fresh.handler send react Execution.draw))
      (Zkc.Modules.Preparation.empty, (prover, coins))

theorem fresh_outcome (send : S → Message F × S) (react : S → F → S)
    (p : Quadratic F n) (claim : F) (prover : S) (coins : List F) :
    (fresh send react p claim prover coins).outcome =
      (Execution.run send react p claim prover coins).outcome :=
  (Sumcheck.Preparation.execution price prices .memo AlgebraicRounds.Construction.fresh
    (AlgebraicRounds.Fresh.handler send react Execution.draw) (Source.program n)
    (inputs p claim).get _ (prover, coins)
    (Zkc.Modules.ImmutableCache.empty_valid _)).outcome.symm

/-- Prepared execution and direct residual constraints use the same selected
input and source, including arbitrary prover callbacks and every satisfying value. -/
theorem acceptance_realization (send : S → Message F × S) (react : S → F → S) :
    Zkc.Realization.Acceptance
      (fun (input : Acceptance.Input F S) (_ : Unit) =>
        (fresh send react input.polynomial input.claim input.prover
          (tapeList input.rounds input.coins)).outcome = .returned true)
      (Acceptance.constraints send react) := by
  apply (Acceptance.realization send react).bindInput id
  intro input output
  rw [fresh_outcome]
  rfl

theorem connected_acceptance (send : S → Message F × S) (react : S → F → S)
    (input : Acceptance.Input F S) :
    Relation.Connected (Connection.produces send react input) Eq (Connection.evaluates input) ↔
      (fresh send react input.polynomial input.claim input.prover
        (tapeList input.rounds input.coins)).outcome = .returned true := by
  rw [Connection.connected_source, fresh_outcome]
  rfl

def framed (domain : String) (send : S → Message F × S) (react : S → F → S)
    (query : AlgebraicRounds.Construction.Query F Q) (p : Quadratic F n)
    (claim : F) (prover : S) (provider : Q) :=
  ((Source.program n).denote (Sumcheck.Preparation.meaning AlgebraicRounds.Construction.framed)
    (inputs p claim).get).run
      (PIR.Preparation.handler (Sumcheck.Preparation.provider price) prices .memo
        (AlgebraicRounds.Framed.handler send react query))
      (Zkc.Modules.Preparation.empty, Framed.initial domain p claim prover provider)

theorem framed_preserves (domain : String) (send : S → Message F × S) (react : S → F → S)
    (query : AlgebraicRounds.Construction.Query F Q) (p : Quadratic F n)
    (claim : F) (prover : S) (provider : Q) :
    let reference := Framed.run domain send react query p claim prover provider
    let actual := framed domain send react query p claim prover provider
    actual.outcome = reference.outcome ∧ actual.state.2 = reference.state ∧
      observeEvents PIR.Preparation.view actual.events = reference.events := by
  have law := Sumcheck.Preparation.execution price prices .memo AlgebraicRounds.Construction.framed
    (AlgebraicRounds.Framed.handler send react query) (Source.program n) (inputs p claim).get
    _ (Framed.initial domain p claim prover provider) (Zkc.Modules.ImmutableCache.empty_valid _)
  exact ⟨law.outcome.symm, law.state.2.symm,
    by simpa [observeEvents, framed, Framed.run, inputs] using law.events.symm⟩

abbrev Field := ZMod 7
def polynomial : Quadratic Field 2 :=
  .node (.node (.constant 0) (.constant 1) (.constant 0))
    (.node (.constant 0) (.constant 0) (.constant 0))
    (.node (.constant 0) (.constant 0) (.constant 0))

def failSecond : AlgebraicRounds.Construction.Query Field Nat := fun _ attempts =>
  if attempts = 0 then (.returned 2, attempts + 1) else (.stopped .exhausted, attempts + 1)

def failed := framed "prepared" Security.honestSend Security.honestReact failSecond
  polynomial polynomial.booleanSum ⟨2, polynomial⟩ 0

theorem failed_query_retains_attempt :
    failed.outcome = .stopped .exhausted ∧ failed.state.2.provider = 2 ∧
      failed.state.2.position = 1 := by decide +kernel

theorem failed_query_retains_statement :
    Framed.HasRoot (Framed.root "prepared" polynomial polynomial.booleanSum) failed.state.2 := by
  unfold failed
  rw [(framed_preserves "prepared" Security.honestSend Security.honestReact failSecond
    polynomial polynomial.booleanSum ⟨2, polynomial⟩ 0).2.1]
  exact Framed.root_retained _ _ _ _ _ _ _ _

theorem arbitrary_honest_tape (p : Quadratic F n) (coins : Zkc.Probability.AdaptiveTape.Tape F n) :
    (fresh Security.honestSend Security.honestReact p p.booleanSum ⟨n, p⟩
      (tapeList n coins)).outcome = .returned true := by
  rw [fresh_outcome]
  exact Security.source_completeness p coins

end Tests.SumcheckPreparation
