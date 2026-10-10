import Examples.OpeningReduction.Source
import Zkc.Protocols.Sumcheck.Transcript

/-! Connect the structured cubic source to arbitrary adaptive prover callbacks.

The returned scalar and ordered point describe a residual evaluation claim.
Its truth is checked only in the semantic experiment. The source and its handler
never receive the private factor tables.
-/

set_option autoImplicit false

namespace Examples.OpeningReduction.Execution
open PIR Zkc.Source Zkc.Probability
open AdaptiveTape (Tape)
open Zkc.Protocols.Sumcheck (tapePoint tapeList tapeList_length)
open Rounds (Strategy)

inductive Event (F : Type) where
  | message : Message F → Event F
  | challenge : F → Event F
  | openingValues : List F → Event F
  | reject : Event F
  deriving Repr, DecidableEq

variable {F S : Type}

def strategy (send : S → Message F × S) (react : S → F → S) :
    (n : Nat) → S → Strategy F n
  | 0, _ => .done
  | n + 1, state =>
      let (message, next) := send state
      .send message (fun r => strategy send react n (react next r))

def handler (send : S → Message F × S) (react : S → F → S) :
    Handler (Source.interface F) (S × List F) (Event F)
  | .message, (state, coins) =>
      let (message, next) := send state
      ⟨.returned message, (next, coins), [.message message]⟩
  | .challenge, (state, []) => ⟨.stopped .exhausted, (state, []), []⟩
  | .challenge, (state, r :: tail) => ⟨.returned r, (react state r, tail), [.challenge r]⟩
  | .reject, state => ⟨.returned (), state, [.reject]⟩

variable [CommRing F] [DecidableEq F]

def finalClaim : {n : Nat} → Strategy F n → F → Tape F n → Option F
  | 0, .done, claim, _ => some claim
  | _ + 1, .send message next, claim, (r, tail) =>
      if message.boundary = claim then finalClaim (next r) (message.eval r) tail else none

theorem verify_iff_final {n : Nat} (p : Factors F n) (claim : F) (prover : Strategy F n)
    (coins : Tape F n) :
    Rounds.verify p claim prover coins = true ↔
      finalClaim prover claim coins = some (p.eval (tapePoint n coins)) := by
  induction n generalizing claim with
  | zero =>
      cases prover
      have point : tapePoint 0 coins = Fin.elim0 := funext (fun i => Fin.elim0 i)
      simp only [Rounds.verify, finalClaim, Option.some.injEq]
      change decide (claim = p.eval Fin.elim0) = true ↔ claim = p.eval (tapePoint 0 coins)
      rw [point]
      exact decide_eq_true_iff
  | succ n ih =>
      cases prover with
      | send message next =>
          rcases coins with ⟨r, tail⟩
          by_cases passes : message.boundary = claim
          · simp only [Rounds.verify, finalClaim, if_pos passes]
            rw [ih, Factors.eval_restrict]
            rfl
          · simp [Rounds.verify, finalClaim, passes]

theorem rounds_outcome (send : S → Message F × S) (react : S → F → S)
    (count : Nat) (acc : Source.Accumulator F) (state : S) (coins : Tape F count) :
    ((Source.rounds count acc).run (handler send react) (state, tapeList count coins)).outcome =
      match finalClaim (strategy send react count state) acc.claim coins with
      | none => .stopped .reject
      | some claim => .returned ⟨claim, acc.challenges ++ tapeList count coins⟩ := by
  induction count generalizing acc state with
  | zero => simp [Source.rounds, Proc.run, strategy, finalClaim, tapeList]
  | succ count ih =>
      rcases coins with ⟨r, tail⟩
      cases sent : send state with
      | mk message next =>
          by_cases passes : message.boundary = acc.claim
          · simp only [Source.rounds, Proc.run, handler, sent, Execution.follow, tapeList,
              if_pos passes]
            rw [ih]
            simp only [strategy, sent, finalClaim, if_pos passes]
            cases result : finalClaim (strategy send react count (react next r)) (message.eval r) tail <;>
              simp [Source.advance, List.append_assoc, result]
          · simp [Source.rounds, Proc.run, handler, sent, Execution.follow, tapeList,
              passes, strategy, finalClaim]

def run (send : S → Message F × S) (react : S → F → S)
    (count : Nat) (claim : F) (state : S) (coins : List F) :
    PIR.Execution (S × List F) (Event F) (Source.Accumulator F) :=
  ((Source.program count).denote Source.meaning
    (Values.cons (ty := Source.Ty.accumulator) ⟨claim, []⟩ .nil).get).run
    (handler send react) (state, coins)

theorem source_outcome (send : S → Message F × S) (react : S → F → S)
    (count : Nat) (claim : F) (state : S) (coins : Tape F count) :
    (run send react count claim state (tapeList count coins)).outcome =
      match finalClaim (strategy send react count state) claim coins with
      | none => .stopped .reject
      | some result => .returned ⟨result, tapeList count coins⟩ := by
  rw [run, Source.program_denote]
  simpa only [Values.get, List.nil_append] using rounds_outcome send react count ⟨claim, []⟩ state coins

theorem returned_iff {n : Nat} (send : S → Message F × S) (react : S → F → S)
    (p : Factors F n) (claim : F) (state : S) (coins : Tape F n) :
    (run send react n claim state (tapeList n coins)).outcome =
        .returned ⟨p.eval (tapePoint n coins), tapeList n coins⟩ ↔
      Rounds.verify p claim (strategy send react n state) coins = true := by
  rw [source_outcome, verify_iff_final]
  cases h : finalClaim (strategy send react n state) claim coins <;> simp

end Examples.OpeningReduction.Execution
