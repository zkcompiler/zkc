module

public import Zkc.Protocols.Sumcheck.Committed.Connection
public import Zkc.Semantics.ExactRefinement

@[expose] public section

/-! Implementation contracts for the actual residual passed to PCS openings.
A round certificate preserves the accumulator, private successor state, unused
coins, stops and events. It contains no cryptographic or probability claim.
-/
set_option autoImplicit false
namespace Zkc.Protocols.Sumcheck.Committed
open Zkc.Polynomial Zkc.Probability
open AdaptiveTape (Tape)

variable {F S : Type} {n : Nat} {scheme : Scheme F n}
variable [Field F] [DecidableEq F]

abbrev RoundImplementation (F : Type) :=
  F → PIR.Process (AlgebraicRounds.interface F) (Source.Accumulator F)

structure RoundContract (implementation : RoundImplementation F) (count : Nat) : Prop where
  realizes : ∀ claim, PIR.ExactRefinement (implementation claim) (Source.rounds count ⟨claim, []⟩)

/-- Complete execution is the boundary: equality of acceptance bits is insufficient. -/
theorem RoundContract.execution {implementation : RoundImplementation F}
    (certificate : RoundContract implementation n) (adversary : Adversary scheme S)
    (claim : F) (prover : S) (coins : Tape F n) :
    (implementation claim).run (Execution.handler adversary.send adversary.react)
      (prover, tapeList n coins) = roundExecution adversary claim prover coins :=
  (certificate.realizes claim).run_eq _ _

/-- Opening callbacks consume the actual successful round state and residual. -/
def runWith (implementation : RoundImplementation F) (statement : Statement scheme)
    (adversary : Adversary scheme S) (claim : F) (prover : S) (coins : Tape F n) :
    Option (Terminal scheme) :=
  let rounds := (implementation claim).run (Execution.handler adversary.send adversary.react)
    (prover, tapeList n coins)
  match rounds.outcome with
  | .stopped _ => none
  | .returned accumulator =>
    let query : Query F n := ⟨coordinates n accumulator.challenges, accumulator.claim⟩
    let (left, next) := adversary.openLeft rounds.state.1 query
    let right := if leftCheck statement query left then
      some (adversary.openRight next query left) else none
    some ⟨query, left, right⟩

theorem RoundContract.runWith_eq {implementation : RoundImplementation F}
    (certificate : RoundContract implementation n) (statement : Statement scheme)
    (adversary : Adversary scheme S) (claim : F) (prover : S) (coins : Tape F n) :
    runWith implementation statement adversary claim prover coins =
      run statement adversary claim prover coins := by
  unfold runWith run
  rw [certificate.execution]
  rfl

def AcceptedWith (implementation : RoundImplementation F) (statement : Statement scheme)
    (adversary : Adversary scheme S) (claim : F) (prover : S) (coins : Tape F n) : Prop :=
  ∃ terminal, runWith implementation statement adversary claim prover coins = some terminal ∧
    terminal.accepts statement = true

def BadOpeningWith (implementation : RoundImplementation F) (statement : Statement scheme)
    (adversary : Adversary scheme S) (claim : F) (prover : S) (coins : Tape F n) : Prop :=
  ∃ terminal, runWith implementation statement adversary claim prover coins = some terminal ∧
    terminal.badOpening statement

theorem RoundContract.accepted_source_or_bad {implementation : RoundImplementation F}
    (certificate : RoundContract implementation n) (statement : Statement scheme)
    (adversary : Adversary scheme S) (claim : F) (prover : S) (coins : Tape F n)
    (accepted : AcceptedWith implementation statement adversary claim prover coins) :
    (Execution.run adversary.send adversary.react statement.polynomial claim prover
      (tapeList n coins)).outcome = .returned true ∨
    BadOpeningWith implementation statement adversary claim prover coins := by
  simp only [AcceptedWith, certificate.runWith_eq] at accepted
  simpa only [BadOpeningWith, BadOpening, certificate.runWith_eq] using
    Zkc.Protocols.Sumcheck.Committed.accepted_source_or_bad statement adversary claim prover coins accepted


end Zkc.Protocols.Sumcheck.Committed
