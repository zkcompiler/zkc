import Zkc.Semantics.Machine

/-! Controls distinguish observation limits, rejection and a false return, and
exercise actual successor state and ordered events across resumed execution. -/

namespace MachineTests
open PIR

abbrev interaction : Signature := ⟨Unit, fun _ => Bool⟩

def verifier : Proc interaction Bool :=
  .call () fun accepted =>
    if accepted then .call () fun _ => .done false
    else .halt .reject

def replies : Handler interaction Nat Nat := fun _ state =>
  ⟨.returned (state == 0), state + 1, [state]⟩

example : (verifier.machine.run replies 0 0).progress = .running verifier := rfl
example : (verifier.machine.run replies 0 0).progress ≠ .finished (.stopped .reject) := by
  intro impossible
  cases impossible

example : (verifier.machine.run replies 1 0).state = 1 := rfl
example : (verifier.machine.run replies 1 0).events = [0] := rfl
example : (verifier.machine.run replies 3 0).progress = .finished (.returned false) := rfl
example : (verifier.machine.run replies 3 0).state = 2 := rfl
example : (verifier.machine.run replies 3 0).events = [0, 1] := rfl

example : (verifier.machine.run replies 2 1).progress = .finished (.stopped .reject) := rfl
example : (verifier.machine.run replies 2 1).state = 2 := rfl
example : (verifier.machine.run replies 2 1).events = [1] := rfl

example : verifier.machine.runFrom replies 2 (verifier.machine.run replies 1 0) =
    verifier.machine.run replies 3 0 := rfl

example (extra : Nat) :
    verifier.machine.runFrom replies extra (verifier.machine.run replies 2 1) =
      verifier.machine.run replies 2 1 :=
  verifier.machine.runFrom_finished replies extra (.stopped .reject) 2 [1]

/-- A genuinely nonterminating machine has a finite observation at every budget. -/
def spin : Machine interaction Unit Bool := ⟨(), fun _ => .internal ()⟩

theorem spin_running (fuel state : Nat) :
    spin.run replies fuel state = ⟨.running (), state, []⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

#print axioms PIR.Machine.runFrom_add
#print axioms PIR.Machine.runFrom_events
#print axioms PIR.Proc.complete_run
#print axioms spin_running

end MachineTests
