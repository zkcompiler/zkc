module

public import Zkc.Realization.Execution

@[expose] public section

namespace ExecutionSimulationTests
open PIR Zkc.Realization

def keep (s : Bool) : Execution Bool Bool Bool := ⟨.returned true, s, []⟩
def reset (_ : Bool) : Execution Bool Bool Bool := ⟨.returned true, false, []⟩
def read (_ : Bool) (s : Bool) : Execution Bool Bool Bool := ⟨.returned s, s, []⟩

/-- Acceptance alone hides a mutation that the next cache/state reader sees. -/
example : (keep true).outcome = (reset true).outcome := rfl
example : ((keep true).follow read).outcome ≠ ((reset true).follow read).outcome := by decide

theorem reset_not_simulated : ¬ ExecutionSimulation (fun _ => True) (fun _ => True)
    Eq Eq (fun e => [e]) (fun e => [e]) keep reset := by
  intro simulation
  have impossible := (simulation.preserves true true trivial trivial rfl).state
  cases impossible

theorem empty_relation_does_not_cover :
    ¬ ExecutionSimulation (fun _ => True) (fun _ => True)
      (fun _ _ => False) Eq (fun e => [e]) (fun e => [e]) keep keep := by
  intro simulation
  obtain ⟨_, impossible⟩ := simulation.initial_exists true trivial
  exact impossible

def failKeep (s : Bool) : Execution Bool Bool Bool := ⟨.stopped .reject, s, [s]⟩
def failReset (_ : Bool) : Execution Bool Bool Bool := ⟨.stopped .reject, false, [true]⟩

/-- Stopping does not erase the provider's final state or the entered events. -/
theorem stopped_state_not_erased : ¬ Related Eq (fun e => [e]) (fun e => [e])
    (failKeep true) (failReset true) := by
  intro related
  cases related.state

theorem same : ExecutionSimulation (fun _ => True) (fun _ => True) Eq Eq
    (fun e => [e]) (fun e => [e]) failKeep failKeep where
  covers s _ := ⟨s, trivial, rfl⟩
  preserves s t _ _ inputs := by cases inputs; exact ⟨rfl, rfl, rfl⟩

/-- A concrete consumer may observe the post-state of a stopped computation. -/
example (s : Bool) : (failKeep s).events = [(failKeep s).state] :=
  same.transport id id (fun _ _ equal => equal)
    (fun _ state events => events = [state]) (fun _ _ => rfl) s trivial

end ExecutionSimulationTests
