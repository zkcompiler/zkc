import Zkc
import Tests.Interaction

set_option autoImplicit false

namespace PIR.Tests

def writes : Signature := ⟨Nat, fun _ => Bool⟩

def recovering : Handler writes Nat Nat := fun value _ =>
  ⟨.returned false, value, [value]⟩

def stopping : Handler writes Nat Nat := fun value _ =>
  ⟨.stopped .reject, value, [value]⟩

def retry : Proc writes Bool := .call (1 : Nat) fun ok =>
  if (show Bool from ok) then .done true else .call (9 : Nat) Proc.done

theorem returned_error_runs_suffix :
    retry.run recovering 0 = ⟨.returned false, 9, [1,9]⟩ := rfl

theorem terminal_error_retains_prefix :
    retry.run stopping 0 = ⟨.stopped .reject, 1, [1]⟩ := rfl

theorem terminal_error_does_not_restore_state :
    (retry.run stopping 0).state ≠ 0 := by decide

def loose : Contract Nat Nat Bool := ⟨fun _ => True, fun _ _ => True⟩

theorem weak_contract_allows_recovery : Satisfies loose (retry.run recovering) :=
  fun _ _ => trivial

theorem weak_contract_allows_stop : Satisfies loose (retry.run stopping) :=
  fun _ _ => trivial

theorem shared_weak_contract_does_not_imply_replacement :
    retry.run recovering 0 ≠ retry.run stopping 0 := by
  intro same
  have impossible := congrArg Execution.outcome same
  change Outcome.returned false = Outcome.stopped Stop.reject at impossible
  cases impossible

def accepted : Execution Nat Nat Bool := ⟨.returned true, 1, [7]⟩

theorem acceptance_then_abort_is_outer_abort :
    accepted.follow (fun _ s => (⟨.stopped .abort, s+1, [8]⟩ : Execution Nat Nat Unit)) =
      ⟨.stopped .abort, 2, [7,8]⟩ := rfl

/-- A total reply-indexed tree need not have a uniform natural-number height. -/
def counts : Signature := ⟨Unit, fun _ => Nat⟩

def ticks : Nat → Proc counts Unit
  | 0 => .done ()
  | n+1 => .call () (fun _ => ticks n)

theorem ticks_bounded (n : Nat) : Within n (ticks n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact fun _ => ih

theorem ticks_exceed_bound (n : Nat) : ¬ Within n (ticks (n+1)) := by
  induction n with
  | zero => exact fun impossible => impossible
  | succ n ih => exact fun bound => ih (bound (0 : Nat))

def chooseLength : Proc counts Unit := .call () ticks

theorem well_founded_is_not_uniformly_bounded (n : Nat) : ¬ Within n chooseLength := by
  cases n with
  | zero => exact fun impossible => impossible
  | succ n => exact fun bound => ticks_exceed_bound n (bound (n+1))

end PIR.Tests
