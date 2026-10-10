import Zkc.Realization.Simulation
import Lean

namespace Tests.Simulation
open PIR

def view (event : Nat) : List Nat := [event]

def stored (value : Nat) (_ : Unit) (slot : Fin 1) (heap : List Nat) : Prop :=
  heap[slot.val]? = some value

/-- A handle denotes the allocated value in the returned heap, not the input heap. -/
theorem allocated_result (value : Nat) :
    Execution.Relates (fun (_ : Unit) (_ : List Nat) => True) stored view view
      ⟨.returned value, (), [1]⟩ ⟨.returned 0, [value], [1]⟩ := by
  exact ⟨by simp [Outcome.Relates, stored], trivial, rfl⟩

theorem stale_heap_rejected :
    ¬ Execution.Relates (fun (_ : Unit) (_ : List Nat) => True) stored view view
      ⟨.returned 7, (), [1]⟩ ⟨.returned 0, [8], [1]⟩ := by
  intro h
  have := h.outcome
  simp [Outcome.Relates, stored] at this

def loadNext (slot : Fin 1) (heap : List Nat) : Execution (List Nat) Nat Nat :=
  match heap[slot.val]? with
  | some value => ⟨.returned (value + 1), heap, [2]⟩
  | none => ⟨.stopped .refused, heap, [2]⟩

/-- Compose allocation with a consumer that dereferences the represented result. -/
theorem allocated_then_loaded (value : Nat) :
    Execution.Relates (fun (_ : Unit) (_ : List Nat) => True)
      (fun a (_ : Unit) b (_ : List Nat) => a = b) view view
      ((⟨.returned value, (), [1]⟩ : Execution Unit Nat Nat).follow
        (fun a s => ⟨.returned (a + 1), s, [2]⟩))
      ((⟨.returned 0, [value], [1]⟩ : Execution (List Nat) Nat (Fin 1)).follow
        loadNext) := by
  apply Execution.Relates.follow _ stored _ view view _ _ (allocated_result value)
  intro a s b t _ hv
  simp only [stored] at hv
  simp only [loadNext, hv]
  exact ⟨rfl, trivial, rfl⟩

/-- A failed write retains its post-state and ordered observation. -/
theorem failed_write :
    Execution.Relates (fun s t : Nat => s = t)
      (fun a (_ : Nat) b (_ : Nat) => a = b) view view
      (⟨.stopped .abort, 1, [1]⟩ : Execution Nat Nat Nat)
      (⟨.stopped .abort, 1, [1]⟩ : Execution Nat Nat Nat) :=
  ⟨rfl, rfl, rfl⟩

theorem rolled_back_failure_rejected :
    ¬ Execution.Relates (fun s t : Nat => s = t)
      (fun a (_ : Nat) b (_ : Nat) => a = b) view view
      (⟨.stopped .abort, 1, [1]⟩ : Execution Nat Nat Nat)
      (⟨.stopped .abort, 0, [1]⟩ : Execution Nat Nat Nat) := by
  intro h
  have := h.state
  contradiction

theorem missing_observation_rejected :
    ¬ Execution.Relates (fun s t : Nat => s = t)
      (fun a (_ : Nat) b (_ : Nat) => a = b) view view
      (⟨.stopped .abort, 1, [1]⟩ : Execution Nat Nat Nat)
      (⟨.stopped .abort, 1, []⟩ : Execution Nat Nat Nat) := by
  intro h
  have := h.events
  simp [observeEvents, view] at this

theorem different_stop_rejected :
    ¬ Outcome.Relates (fun a b : Nat => a = b) (.stopped .abort) (.stopped .reject) := by
  simp [Outcome.Relates]

end Tests.Simulation

open Lean Elab Command
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``PIR.Execution.Relates.follow, ``PIR.Execution.Relates.trans,
      ``PIR.Execution.Relates.of_related, ``Tests.Simulation.allocated_result,
      ``Tests.Simulation.stale_heap_rejected, ``Tests.Simulation.allocated_then_loaded,
      ``Tests.Simulation.failed_write,
      ``Tests.Simulation.rolled_back_failure_rejected,
      ``Tests.Simulation.missing_observation_rejected,
      ``Tests.Simulation.different_stop_rejected] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unexpected axiom: {name} depends on {ax}"
  logInfo "SIMULATION-AUDIT-PASS"
