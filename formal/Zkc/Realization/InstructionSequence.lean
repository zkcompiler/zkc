import Zkc.Semantics.Execution

set_option autoImplicit false

namespace Zkc.Realization.InstructionSequence
-- Outcome classes remain distinct. Strings carry scoped reason identifiers.
-- incomplete is interpreter exhaustion, never a successful protocol return.
inductive Exit where
  | accept
  | reject : String → Exit
  | unavailable : String → Exit
  | incomplete
  deriving Repr, DecidableEq

structure Terminal (State Event : Type) where
  outcome : Exit
  state : State
  events : List Event

inductive Step (State Event : Type) where
  | next : State → List Event → Step State Event
  | halt : Exit → State → List Event → Step State Event

def run {Op State Event : Type} (step : Op → State → Step State Event) :
    List Op → State → Terminal State Event
  | [], s => ⟨.incomplete,s,[]⟩
  | op :: ops,s => match step op s with
    | .halt outcome t es => ⟨outcome,t,es⟩
    | .next t es =>
      let out := run step ops t
      ⟨out.outcome,out.state,es ++ out.events⟩

def ObservationEq {S T E F O : Type}
    (left : Terminal S E → O) (right : Terminal T F → O)
    (x : Terminal S E) (y : Terminal T F) : Prop := left x = right y

@[simp] theorem run_halt {Op S E : Type} (step : Op → S → Step S E)
    (op : Op) (s t : S) (outcome : Exit) (events : List E)
    (h : step op s = .halt outcome t events) (rest : List Op) :
    run step (op :: rest) s = ⟨outcome,t,events⟩ := by simp [run,h]

def signature (Op : Type) : PIR.Signature := ⟨Op, fun _ => Option Exit⟩

/-- The instruction machine's exact exit is result data in this embedding.
In particular, returning `.incomplete` does not assert protocol acceptance. -/
def source {Op : Type} : List Op → PIR.Proc (signature Op) Exit
  | [] => .done .incomplete
  | op :: rest => .call op fun
      | none => source rest
      | some exit => .done exit

def sourceHandler {Op S E : Type} (step : Op → S → Step S E) :
    PIR.Handler (signature Op) S E := fun op s =>
  match step op s with
  | .next t es => ⟨.returned none, t, es⟩
  | .halt exit t es => ⟨.returned (some exit), t, es⟩

def Terminal.toExecution {S E : Type} (t : Terminal S E) : PIR.Execution S E Exit :=
  ⟨.returned t.outcome, t.state, t.events⟩

theorem execution_exact {Op S E : Type} (step : Op → S → Step S E)
    (ops : List Op) (s : S) :
    (source ops).run (sourceHandler step) s = (run step ops s).toExecution := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    cases h : step op s with
    | next t es =>
      simp only [source, PIR.Proc.run, sourceHandler, h, PIR.Execution.follow]
      rw [ih]
      simp [run, h, Terminal.toExecution]
    | halt exit t es =>
      simp [source, PIR.Proc.run, sourceHandler, h, PIR.Execution.follow, run,
        Terminal.toExecution]


def stateOf {S E : Type} : Step S E → S
  | .next s _ => s
  | .halt _ s _ => s
def eventsOf {S E : Type} : Step S E → List E
  | .next _ es => es
  | .halt _ _ es => es
def exitOf {S E : Type} : Step S E → Option Exit
  | .next _ _ => none
  | .halt x _ _ => some x
def mapStep {S T E : Type} (f : S → T) : Step S E → Step T E
  | .next s es => .next (f s) es
  | .halt x s es => .halt x (f s) es


end Zkc.Realization.InstructionSequence
