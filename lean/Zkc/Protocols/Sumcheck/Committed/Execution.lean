import Zkc.Protocols.Sumcheck.Committed.Statement
import Zkc.Protocols.Sumcheck.Acceptance

/-! Actual adaptive rounds followed by two sequential opening checks.

The round runner is the maintained source round process and handler. Its entire
execution, including stopped prefixes, remains available. Opening replies have
no correctness restriction; the second may depend on the first. A failed first
check prevents the second request. No opening request is made after round failure.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Committed

open Zkc.Polynomial Zkc.Probability
open AdaptiveTape (Tape)
open AlgebraicRounds (Message)

structure Query (F : Type) (n : Nat) where
  point : Fin n → F
  claim : F

structure Reply {F : Type} {n : Nat} (scheme : Scheme F n) where
  value : F
  proof : scheme.Proof

/-- All private randomness may be fixed in the initial state. Callbacks have
no access to the unconsumed verifier tape. -/
structure Adversary {F : Type} {n : Nat} (scheme : Scheme F n) (S : Type) where
  send : S → Message F × S
  react : S → F → S
  openLeft : S → Query F n → Reply scheme × S
  openRight : S → Query F n → Reply scheme → Reply scheme

structure Terminal {F : Type} {n : Nat} (scheme : Scheme F n) where
  query : Query F n
  left : Reply scheme
  right : Option (Reply scheme)

variable {F S : Type} {n : Nat} {scheme : Scheme F n}
variable [CommRing F] [DecidableEq F]

def leftCheck (statement : Statement scheme) (query : Query F n) (reply : Reply scheme) : Bool :=
  scheme.check (scheme.verifierKey statement.setup) statement.leftCommitment
    query.point reply.value reply.proof

def rightCheck (statement : Statement scheme) (query : Query F n) (reply : Reply scheme) : Bool :=
  scheme.check (scheme.verifierKey statement.setup) statement.rightCommitment
    query.point reply.value reply.proof

def Terminal.accepts (terminal : Terminal scheme) (statement : Statement scheme) : Bool :=
  leftCheck statement terminal.query terminal.left && match terminal.right with
    | none => false
    | some right => rightCheck statement terminal.query right &&
        decide (terminal.query.claim = terminal.left.value * right.value)

/-- False accepted openings on the actual sequential queries. This event does
not require final product equality or overall protocol acceptance. The right
check is reached only if the left check passes; no independence is asserted. -/
def Terminal.badOpening (terminal : Terminal scheme) (statement : Statement scheme) : Prop :=
  leftCheck statement terminal.query terminal.left = true ∧
    (terminal.left.value ≠ statement.leftValue terminal.query.point ∨
      ∃ right, terminal.right = some right ∧ rightCheck statement terminal.query right = true ∧
        right.value ≠ statement.rightValue terminal.query.point)

def Terminal.correctOpenings (terminal : Terminal scheme) (statement : Statement scheme) : Prop :=
  terminal.left.value = statement.leftValue terminal.query.point ∧
    ∀ right, terminal.right = some right → right.value = statement.rightValue terminal.query.point

/-- The original process retains the failed message, rejection event, private
successor state and unconsumed suffix; it does not fill in a failed query. -/
def roundExecution (adversary : Adversary scheme S) (claim : F) (prover : S) (coins : Tape F n) :=
  (Source.rounds n ⟨claim, []⟩).run (Execution.handler adversary.send adversary.react)
    (prover, tapeList n coins)

def run (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (prover : S) (coins : Tape F n) : Option (Terminal scheme) :=
  let rounds := roundExecution adversary claim prover coins
  match rounds.outcome with
  | .stopped _ => none
  | .returned accumulator =>
      let query : Query F n := ⟨coordinates n accumulator.challenges, accumulator.claim⟩
      let (left, next) := adversary.openLeft rounds.state.1 query
      let right := if leftCheck statement query left then
        some (adversary.openRight next query left) else none
      some ⟨query, left, right⟩

def Accepted (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (prover : S) (coins : Tape F n) : Prop :=
  ∃ terminal, run statement adversary claim prover coins = some terminal ∧
    terminal.accepts statement = true

def BadOpening (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (prover : S) (coins : Tape F n) : Prop :=
  ∃ terminal, run statement adversary claim prover coins = some terminal ∧
    terminal.badOpening statement

def CorrectReachedOpenings (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (prover : S) (coins : Tape F n) : Prop :=
  ∀ terminal, run statement adversary claim prover coins = some terminal →
    terminal.correctOpenings statement

theorem roundExecution_outcome (adversary : Adversary scheme S) (claim : F)
    (prover : S) (coins : Tape F n) :
    (roundExecution adversary claim prover coins).outcome =
      match finalClaim (Execution.strategy adversary.send adversary.react n prover) claim coins with
      | none => .stopped .reject
      | some value => .returned ⟨value, tapeList n coins⟩ := by
  have outcome := Execution.rounds_outcome adversary.send adversary.react n ⟨claim, []⟩ prover coins
  cases result : finalClaim (Execution.strategy adversary.send adversary.react n prover) claim coins <;>
    simpa only [roundExecution, result, List.nil_append] using outcome

theorem failed_rounds_no_openings (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (prover : S) (coins : Tape F n)
    (failed : finalClaim (Execution.strategy adversary.send adversary.react n prover) claim coins = none) :
    run statement adversary claim prover coins = none := by
  simp [run, roundExecution_outcome, failed]

/-- The point and terminal scalar are derived from the execution, not supplied
as a correctness premise about an unrelated query. -/
theorem reached_query (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (prover : S) (coins : Tape F n) (terminal : Terminal scheme)
    (reached : run statement adversary claim prover coins = some terminal) :
    terminal.query.point = tapePoint n coins ∧
      finalClaim (Execution.strategy adversary.send adversary.react n prover) claim coins =
        some terminal.query.claim := by
  simp only [run, roundExecution_outcome] at reached
  cases result : finalClaim (Execution.strategy adversary.send adversary.react n prover) claim coins with
  | none => simp [result] at reached
  | some value =>
      simp only [result, tapeList_ofFn, coordinates_ofFn] at reached
      cases sent : adversary.openLeft (roundExecution adversary claim prover coins).state.1
          ⟨tapePoint n coins, value⟩ with
      | mk left next =>
          simp only [sent, Option.some.injEq] at reached
          subst terminal
          exact ⟨rfl, rfl⟩

end Zkc.Protocols.Sumcheck.Committed
