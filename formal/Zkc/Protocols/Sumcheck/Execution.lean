import Zkc.Protocols.Sumcheck.Source

/-! The whole typed source runs under the same staged Fresh construction as
algebraic rounds. Its acceptance event is exactly the complete verifier game. -/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Execution

open PIR Zkc.Source Zkc.Polynomial Zkc.Probability
open AlgebraicRounds (Message)
open AlgebraicRounds.Construction (Event)
open AdaptiveTape (Tape)

variable {F S : Type}

/-- All private prover state is explicit. The next message is selected before
this round's verifier coin is delivered. -/
def strategy (send : S → Message F × S) (react : S → F → S) :
    (n : Nat) → S → Strategy F n
  | 0, _ => .done
  | n + 1, state =>
      let (message, next) := send state
      .send message (fun r => strategy send react n (react next r))

def draw : List F → Outcome F × List F
  | [] => (.stopped .exhausted, [])
  | r :: tail => (.returned r, tail)

/-- Direct operational handler for the three interactive effects. -/
def handler (send : S → Message F × S) (react : S → F → S) :
    Handler (AlgebraicRounds.interface F) (S × List F) (Event F)
  | .message, (prover, coins) =>
      let (message, next) := send prover
      ⟨.returned message, (next, coins), [.message message]⟩
  | .challenge, (prover, []) => ⟨.stopped .exhausted, (prover, []), []⟩
  | .challenge, (prover, r :: tail) => ⟨.returned r, (react prover r, tail), [.challenge r]⟩
  | .reject, state => ⟨.returned (), state, [.reject]⟩

theorem handler_fresh (send : S → Message F × S) (react : S → F → S) :
    handler send react = fun op state =>
      (AlgebraicRounds.Construction.fresh op).run (AlgebraicRounds.Fresh.handler send react draw) state := by
  funext op state
  rcases state with ⟨prover, coins⟩
  cases op with
  | message => cases sent : send prover; simp [handler, AlgebraicRounds.Construction.fresh,
      AlgebraicRounds.Fresh.handler, Proc.run, Execution.follow, sent]
  | challenge => cases coins <;> rfl
  | reject => rfl

variable [CommSemiring F] [DecidableEq F]

theorem rounds_outcome (send : S → Message F × S) (react : S → F → S)
    (count : Nat) (accumulator : Source.Accumulator F) (prover : S) (coins : Tape F count) :
    ((Source.rounds count accumulator).run (handler send react) (prover, tapeList count coins)).outcome =
      match finalClaim (strategy send react count prover) accumulator.claim coins with
      | none => .stopped .reject
      | some claim => .returned ⟨claim, accumulator.challenges ++ tapeList count coins⟩ := by
  induction count generalizing accumulator prover with
  | zero => simp [Source.rounds, Proc.run, strategy, finalClaim, tapeList]
  | succ count ih =>
      rcases coins with ⟨r, tail⟩
      cases sent : send prover with
      | mk message next =>
          by_cases passes : message.boundary = accumulator.claim
          · simp only [Source.rounds, Proc.run, handler, sent, Execution.follow, tapeList,
              if_pos passes]
            rw [ih]
            simp only [strategy, sent, finalClaim, if_pos passes]
            cases result : finalClaim (strategy send react count (react next r)) (message.evaluate r) tail <;>
              simp [Source.advance, List.append_assoc, result]
          · simp [Source.rounds, Proc.run, handler, sent, Execution.follow, tapeList,
              passes, strategy, finalClaim]

/-- This entry uses the staged construction, not an unrelated replay function. -/
def run (send : S → Message F × S) (react : S → F → S)
    {n : Nat} (p : Quadratic F n) (claim : F) (prover : S) (coins : List F) :
    PIR.Execution (S × List F) (Event F) Bool :=
  ((Source.program n).denote (Source.meaning.translate AlgebraicRounds.Construction.fresh)
    (Values.cons (ty := Source.Ty.accumulator) ⟨claim, []⟩
      (Values.cons (ty := Source.Ty.polynomial) p .nil)).get).run
    (AlgebraicRounds.Fresh.handler send react draw) (prover, coins)

theorem source_outcome (send : S → Message F × S) (react : S → F → S)
    {n : Nat} (p : Quadratic F n) (claim : F) (prover : S) (coins : Tape F n) :
    (run send react p claim prover (tapeList n coins)).outcome =
      match finalClaim (strategy send react n prover) claim coins with
      | none => .stopped .reject
      | some result => .returned (decide (result = p.eval (tapePoint n coins))) := by
  rw [run, Program.denote_translate, Proc.run_interpret, ← handler_fresh, Source.program_denote,
    PIR.run_bind]
  simp only [Values.get, Execution.follow]
  have outcome := rounds_outcome send react n ⟨claim, []⟩ prover coins
  simp only [List.nil_append] at outcome
  rw [outcome]
  cases result : finalClaim (strategy send react n prover) claim coins with
  | none => rfl
  | some value =>
      simp [Source.terminal, Proc.run, tapeList_ofFn, coordinates_ofFn]
      rfl

theorem accepted_iff (send : S → Message F × S) (react : S → F → S)
    {n : Nat} (p : Quadratic F n) (claim : F) (prover : S) (coins : Tape F n) :
    (run send react p claim prover (tapeList n coins)).outcome = .returned true ↔
      verify p claim (strategy send react n prover) coins = true := by
  rw [source_outcome, verify_iff_final]
  cases result : finalClaim (strategy send react n prover) claim coins <;> simp

end Zkc.Protocols.Sumcheck.Execution
