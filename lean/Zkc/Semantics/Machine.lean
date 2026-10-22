module

public import Zkc.Semantics.Execution

/-! Open machines and finite observations of possibly unbounded execution.

The machine state holds program control; the handler state belongs to the
environment. Observation fuel bounds the observer, not the program: zero fuel
returns a running configuration. Protocol rejection and handler stops retain
their terminal outcomes, successor state and complete reached event prefix.

The runner below fixes a total handler. Waiting for an unavailable external
reply needs a partial driver; it must not be identified with silent divergence
of this total-handler machine.
-/

@[expose] public section

namespace PIR

inductive Transition (I : Signature) (Control Result : Type) where
  | returned (value : Result)
  | stopped (reason : Stop)
  | internal (next : Control)
  | request (operation : I.Op) (next : I.Reply operation → Control)

structure Machine (I : Signature) (Control Result : Type) where
  initial : Control
  step : Control → Transition I Control Result

inductive Progress (Control Result : Type) where
  | running (control : Control)
  | finished (outcome : Outcome Result)
  deriving Repr

structure Prefix (Control State Event Result : Type) where
  progress : Progress Control Result
  state : State
  events : List Event
  deriving Repr

variable {I : Signature} {C S E A : Type}

def Machine.advance (machine : Machine I C A) (handler : Handler I S E)
    (saved : Prefix C S E A) : Prefix C S E A :=
  match saved.progress with
  | .finished _ => saved
  | .running control =>
      match machine.step control with
      | .returned value => ⟨.finished (.returned value), saved.state, saved.events⟩
      | .stopped reason => ⟨.finished (.stopped reason), saved.state, saved.events⟩
      | .internal next => ⟨.running next, saved.state, saved.events⟩
      | .request operation next =>
          let reply := handler operation saved.state
          let progress := match reply.outcome with
            | .returned value => .running (next value)
            | .stopped reason => .finished (.stopped reason)
          ⟨progress, reply.state, saved.events ++ reply.events⟩

/-- Continue observing exactly the saved program and environment state. -/
def Machine.runFrom (machine : Machine I C A) (handler : Handler I S E) :
    Nat → Prefix C S E A → Prefix C S E A
  | 0, saved => saved
  | fuel + 1, saved => machine.runFrom handler fuel (machine.advance handler saved)

def Machine.run (machine : Machine I C A) (handler : Handler I S E)
    (fuel : Nat) (initial : S) : Prefix C S E A :=
  machine.runFrom handler fuel ⟨.running machine.initial, initial, []⟩

/-- Increasing an observation budget resumes the actual residual configuration. -/
theorem Machine.runFrom_add (machine : Machine I C A) (handler : Handler I S E)
    (first second : Nat) (saved : Prefix C S E A) :
    machine.runFrom handler (first + second) saved =
      machine.runFrom handler second (machine.runFrom handler first saved) := by
  induction first generalizing saved with
  | zero => simp only [Nat.zero_add, runFrom]
  | succ first ih =>
      simpa only [Nat.succ_add, runFrom] using ih (machine.advance handler saved)

/-- A terminated execution cannot execute a suffix or lose its stopped prefix. -/
theorem Machine.runFrom_finished (machine : Machine I C A) (handler : Handler I S E)
    (fuel : Nat) (outcome : Outcome A) (state : S) (events : List E) :
    machine.runFrom handler fuel ⟨.finished outcome, state, events⟩ =
      ⟨.finished outcome, state, events⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

/-- Resuming an explicit configuration depends only on the transition function;
the initial control is used solely when starting a new run. -/
theorem Machine.runFrom_eq_of_step_eq (first second : Machine I C A)
    (same : first.step = second.step) (handler : Handler I S E)
    (fuel : Nat) (saved : Prefix C S E A) :
    first.runFrom handler fuel saved = second.runFrom handler fuel saved := by
  have advance : ∀ saved, first.advance handler saved = second.advance handler saved := by
    intro saved
    simp only [Machine.advance, same]
  induction fuel generalizing saved with
  | zero => rfl
  | succ fuel ih => simp only [runFrom, advance, ih]

theorem Machine.advance_events (machine : Machine I C A) (handler : Handler I S E)
    (saved : Prefix C S E A) :
    ∃ suffix, (machine.advance handler saved).events = saved.events ++ suffix := by
  cases saved with
  | mk progress state events =>
      cases progress with
      | finished outcome => exact ⟨[], (List.append_nil _).symm⟩
      | running control =>
          cases h : machine.step control with
          | returned value => exact ⟨[], by simp [advance, h]⟩
          | stopped reason => exact ⟨[], by simp [advance, h]⟩
          | internal next => exact ⟨[], by simp [advance, h]⟩
          | request operation next => exact ⟨(handler operation state).events, by simp [advance, h]⟩

/-- Every later observation retains the whole earlier event prefix. -/
theorem Machine.runFrom_events (machine : Machine I C A) (handler : Handler I S E)
    (fuel : Nat) (saved : Prefix C S E A) :
    ∃ suffix, (machine.runFrom handler fuel saved).events = saved.events ++ suffix := by
  induction fuel generalizing saved with
  | zero => exact ⟨[], (List.append_nil _).symm⟩
  | succ fuel ih =>
      obtain ⟨first, hfirst⟩ := machine.advance_events handler saved
      obtain ⟨rest, hrest⟩ := ih (machine.advance handler saved)
      exact ⟨first ++ rest, by simpa only [runFrom, hfirst, List.append_assoc] using hrest⟩

/-- A finite effect tree supplies machine control without a second interpretation. -/
def Process.machine (process : Process I A) : Machine I (Process I A) A where
  initial := process
  step
    | .done value => .returned value
    | .halt reason => .stopped reason
    | .call operation next => .request operation next

/-- Continuing a finite process at the saved handler state gives its full result. -/
def Prefix.complete (handler : Handler I S E) (saved : Prefix (Process I A) S E A) :
    Execution S E A :=
  match saved.progress with
  | .finished outcome => ⟨outcome, saved.state, saved.events⟩
  | .running process =>
      let result := process.run handler saved.state
      ⟨result.outcome, result.state, saved.events ++ result.events⟩

/-- A machine step preserves the complete finite interpretation, including stops. -/
theorem Process.complete_advance (process : Process I A) (handler : Handler I S E)
    (saved : Prefix (Process I A) S E A) :
    (process.machine.advance handler saved).complete handler = saved.complete handler := by
  cases saved with
  | mk progress state events =>
      cases progress with
      | finished outcome => rfl
      | running current =>
          cases current with
          | done value => simp [Machine.advance, machine, Prefix.complete, run]
          | halt reason => simp [Machine.advance, machine, Prefix.complete, run]
          | call operation next =>
              cases h : handler operation state with
              | mk outcome nextState produced =>
                  cases outcome <;>
                    simp [Machine.advance, machine, Prefix.complete, run, h,
                      Execution.follow, List.append_assoc]

/-- Every finite observation is consistent with the original complete semantics. -/
theorem Process.complete_runFrom (process : Process I A) (handler : Handler I S E)
    (fuel : Nat) (saved : Prefix (Process I A) S E A) :
    (process.machine.runFrom handler fuel saved).complete handler = saved.complete handler := by
  induction fuel generalizing saved with
  | zero => rfl
  | succ fuel ih =>
      exact (ih (process.machine.advance handler saved)).trans
        (process.complete_advance handler saved)

theorem Process.complete_run (process : Process I A) (handler : Handler I S E)
    (fuel : Nat) (initial : S) :
    (process.machine.run handler fuel initial).complete handler = process.run handler initial := by
  simpa [Machine.run, Prefix.complete, machine] using
    process.complete_runFrom handler fuel ⟨.running process, initial, []⟩

/-- A finite process under a total handler eventually reaches its complete
execution result. The budget can depend on the actual replies; no uniform
bound over every possible environment is assumed. -/
theorem Process.eventually_finishes_from (process : Process I A) (handler : Handler I S E)
    (initial : S) (events : List E) :
    ∃ fuel, process.machine.runFrom handler fuel ⟨.running process, initial, events⟩ =
      ⟨.finished (process.run handler initial).outcome, (process.run handler initial).state,
        events ++ (process.run handler initial).events⟩ := by
  induction process generalizing initial events with
  | done value => exact ⟨1, by simp [Machine.runFrom, Machine.advance, machine, run]⟩
  | halt reason => exact ⟨1, by simp [Machine.runFrom, Machine.advance, machine, run]⟩
  | call operation next ih =>
      cases reply : handler operation initial with
      | mk outcome state produced =>
          cases outcome with
          | stopped reason =>
              exact ⟨1, by simp [Machine.runFrom, Machine.advance, machine, run, reply,
                Execution.follow]⟩
          | returned value =>
              obtain ⟨fuel, finishes⟩ := ih value state (events ++ produced)
              have moved := Machine.runFrom_eq_of_step_eq
                (Process.call operation next).machine (next value).machine rfl handler fuel
                ⟨.running (next value), state, events ++ produced⟩
              refine ⟨fuel + 1, ?_⟩
              simpa only [Machine.runFrom, Machine.advance, machine, run, reply,
                Execution.follow, List.append_assoc] using moved.trans finishes

theorem Process.eventually_finishes (process : Process I A) (handler : Handler I S E) (initial : S) :
    ∃ fuel, process.machine.run handler fuel initial =
      ⟨.finished (process.run handler initial).outcome, (process.run handler initial).state,
        (process.run handler initial).events⟩ := by
  simpa only [Machine.run, machine, List.nil_append] using
    process.eventually_finishes_from handler initial []

end PIR
