import Zkc.Semantics
import Tests.OuterEffects

/-! Controls for the migrated execution/observation specification.

These distinguish necessary premises from tempting weaker replacements.
They supplement the generic library laws; they are not a native runtime proof.
-/

set_option autoImplicit false

namespace Tests.SpecCore
open PIR

def first : Execution Nat Nat Unit := ⟨.returned (), 1, [7]⟩
def otherState : Execution Nat Nat Unit := ⟨.returned (), 2, [7]⟩
def readState (_ : Unit) (s : Nat) : Execution Nat Nat Nat := ⟨.returned s,s,[]⟩

/-- A later read distinguishes equal returned values and events. -/
theorem equal_visible_prefix_does_not_justify_suffix :
    first.outcome = otherState.outcome ∧ first.events = otherState.events ∧
    (first.follow readState).outcome ≠ (otherState.follow readState).outcome := by
  exact ⟨rfl,rfl,by decide⟩

/-- An unconstrained residual relation does not license a state observer. -/
theorem related_does_not_license_arbitrary_state_view :
    Related (fun _ _ : Nat => True) (fun e : Nat => [e]) (fun e : Nat => [e])
      first otherState ∧ first.state ≠ otherState.state := by
  exact ⟨⟨rfl,trivial,rfl⟩,by decide⟩

/-- Changing the observer changes the claim being established. -/
theorem erased_trace_agreement_does_not_imply_public_agreement :
    let a : Execution Unit Nat Unit := ⟨.returned (),(),[7]⟩
    let b : Execution Unit Nat Unit := ⟨.returned (),(),[8]⟩
    Related Eq (fun _ : Nat => ([] : List Nat)) (fun _ => []) a b ∧
    ¬ Related Eq (fun e : Nat => [e]) (fun e => [e]) a b := by
  refine ⟨⟨rfl,rfl,rfl⟩,?_⟩
  intro related
  have impossible := related.events
  simp [observeEvents] at impossible

abbrev interface : Signature := ⟨Unit, fun _ => Unit⟩
abbrev phases : Interaction interface :=
  ⟨Unit, Nat, fun _ => (), fun _ _ => True, fun phase _ _ => phase+1⟩
def twoCalls : Proc interface Unit := .call () (fun _ => .call () .done)
def stopAfterEvents (why : Stop) : Handler interface Nat Nat := fun _ state =>
  ⟨.stopped why, state+1, [7,8,9]⟩

/-- Terminal calls count once; their three events do not count as
    three calls, and the unreached suffix contributes no call. Every stop reason
    retains the stopping phase and actual mutation. -/
theorem stopping_invocation_counts_once (why : Stop) :
    twoCalls.run (ExecutionPath.handler phases (stopAfterEvents why)) (4,0) =
      ⟨.stopped why,(4,1),[.inl (4,()),.inr 7,.inr 8,.inr 9]⟩ := rfl

theorem public_bound_applies_to_stopping_invocation (why : Stop) :
    ((twoCalls.run (ExecutionPath.handler phases (stopAfterEvents why)) (4,0)).events.filterMap
      (fun | .inl call => some call | .inr _ => none)).length ≤ 2 := by
  exact ExecutionPath.calls_bounded phases (stopAfterEvents why) twoCalls 2 4 0
    (fun _ _ => trivial)

end Tests.SpecCore
