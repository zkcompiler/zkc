import Zkc.Compiler.Role.Meaning
import Zkc.Source.Protocol.Role.Execution

/-! A resumable boundary for a finite role effect tree.

`advance` bounds exposed requests, not work inside an atomic local service or
initial denotation. It retains the exact pending request on missing ingress and
keeps budget yield distinct from terminal incomplete. Retrying a cursor runs no
already completed action. This is an executable reference cursor, not a native
serialized continuation/call-stack representation or a network progress theorem.
-/

set_option autoImplicit false

namespace Zkc.Compiler.Role

structure Cursor (I : PIR.Signature) (S E A : Type) where
  program : PIR.Proc I A
  state : S
  events : List E := []

inductive RunResult (I : PIR.Signature) (S E A : Type) where
  | finished (result : PIR.Execution S E A)
  | suspended (cursor : Cursor I S E A)
  | yielded (cursor : Cursor I S E A)

variable {I : PIR.Signature} {S E A : Type}

abbrev Poll (I : PIR.Signature) (S E : Type) :=
  (op : I.Op) → S → Option (PIR.Execution S E (I.Reply op))

def advance (poll : Poll I S E) : Nat → Cursor I S E A → RunResult I S E A
  | _, ⟨.done value, state, events⟩ => .finished ⟨.returned value, state, events⟩
  | _, ⟨.halt reason, state, events⟩ => .finished ⟨.stopped reason, state, events⟩
  | 0, ⟨.call op next, state, events⟩ => .yielded ⟨.call op next, state, events⟩
  | fuel + 1, ⟨.call op next, state, events⟩ =>
      match poll op state with
      | none => .suspended ⟨.call op next, state, events⟩
      | some result =>
          match result.outcome with
          | .stopped reason => .finished ⟨.stopped reason, result.state, events ++ result.events⟩
          | .returned reply => advance poll fuel ⟨next reply, result.state, events ++ result.events⟩

def RunResult.resume (result : RunResult I S E A) (poll : Poll I S E) (fuel : Nat) :
    RunResult I S E A :=
  match result with
  | .finished result => .finished result
  | .suspended cursor | .yielded cursor => advance poll fuel cursor

/-- Absence preserves state, events, the request and the full continuation exactly. -/
theorem advance_missing (poll : Poll I S E) (fuel : Nat) (op : I.Op)
    (next : I.Reply op → PIR.Proc I A) (state : S) (events : List E)
    (missing : poll op state = none) :
    advance poll (fuel + 1) ⟨.call op next, state, events⟩ =
      .suspended ⟨.call op next, state, events⟩ := by
  simp only [advance, missing]

/-- A completed strategy with a sufficient exposed-call bound agrees with Proc.run.
The equality includes earlier events, failed-action effects and residual state.
-/
theorem advance_complete (handler : PIR.Handler I S E) (fuel : Nat) (program : PIR.Proc I A)
    (bounded : PIR.Within fuel program) (state : S) (events : List E) :
    advance (fun op state => some (handler op state)) fuel ⟨program, state, events⟩ =
      .finished ⟨(program.run handler state).outcome, (program.run handler state).state,
        events ++ (program.run handler state).events⟩ := by
  induction fuel generalizing program state events with
  | zero =>
      cases program with
      | done value => simp [advance, PIR.Proc.run]
      | halt reason => simp [advance, PIR.Proc.run]
      | call op next => exact False.elim bounded
  | succ fuel ih =>
      cases program with
      | done value => simp [advance, PIR.Proc.run]
      | halt reason => simp [advance, PIR.Proc.run]
      | call op next =>
          cases result : handler op state with
          | mk outcome final emitted =>
              cases outcome with
              | stopped reason => simp [advance, PIR.Proc.run, result, PIR.Execution.follow]
              | returned value =>
                  simp only [advance, result]
                  rw [ih (next value) (bounded value)]
                  simp only [PIR.Proc.run, result, PIR.Execution.follow, List.append_assoc]

end Zkc.Compiler.Role
