import Std

/-! A shared pure work allowance for admission. Charges precede the operations
whose cost they account for. An exact residual equation is bookkeeping, not a
machine-time theorem; each consumer still owns its cost model and callbacks.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.AdmissionWork

variable {Error : Type}

abbrev Meter (Error : Type) := StateT Nat (Except Error)

def consume (exhausted : Error) (amount : Nat := 1) : Meter Error Unit :=
  fun available => if amount ≤ available then .ok ((), available - amount) else .error exhausted

@[simp] theorem consume_ok (exhausted : Error) {amount available : Nat} (fits : amount ≤ available) :
    consume exhausted amount available = .ok ((), available - amount) := by
  simp [consume, fits]

@[simp] theorem consume_error (exhausted : Error) {amount available : Nat} (exceeds : available < amount) :
    consume exhausted amount available = .error exhausted := by
  simp [consume, show ¬amount ≤ available by omega]

theorem consume_residual (exhausted : Error) {amount available remaining : Nat}
    (accepted : consume exhausted amount available = .ok ((), remaining)) :
    remaining + amount = available := by
  by_cases fits : amount ≤ available
  · rw [consume_ok exhausted fits] at accepted
    cases accepted
    omega
  · rw [consume_error exhausted (by omega)] at accepted
    contradiction

/-- The source-level computation checks the allowance before invoking the
action. Compiler hoisting of closed terms and callback runtime remain outside
this abstract accounting contract. -/
def before {Value : Type} (exhausted : Error) (amount : Nat) (action : Unit → Except Error Value) :
    Meter Error Value := do
  consume exhausted amount
  action ()

/-- Preserve the returned allowance across an error boundary and reject a
callback that increases it. Installed callbacks still own their internal cost
contract; checking the returned counter is not a bound on callback runtime. -/
def checked {SourceError Value : Type} (exhausted : Error) (mapError : SourceError → Error)
    (action : Meter SourceError Value) : Meter Error Value := fun available => do
  let (value, remaining) ← (action available).mapError mapError
  if remaining ≤ available then return (value, remaining)
  else throw exhausted

theorem checked_nonincreasing {SourceError Value : Type} (exhausted : Error)
    (mapError : SourceError → Error) (action : Meter SourceError Value)
    {available remaining : Nat} {value : Value}
    (accepted : checked exhausted mapError action available = .ok (value, remaining)) :
    remaining ≤ available := by
  unfold checked at accepted
  cases result : action available with
  | error error => simp [result, Except.mapError, bind, Except.bind] at accepted
  | ok pair =>
      obtain ⟨selected, residual⟩ := pair
      simp only [result, Except.mapError, bind, Except.bind] at accepted
      split at accepted
      · change Except.ok (selected, residual) = Except.ok (value, remaining) at accepted
        cases accepted
        assumption
      · simp [throw] at accepted

private def lengthFrom {Value : Type} (exhausted : Error) :
    Nat → List Value → Nat → Except Error (Nat × Nat)
  | seen, [], available => .ok (seen, available)
  | _, _ :: _, 0 => .error exhausted
  | seen, _ :: rest, available + 1 => lengthFrom exhausted (seen + 1) rest available

private theorem lengthFrom_residual {Value : Type} (exhausted : Error) (values : List Value)
    {seen available result remaining : Nat}
    (accepted : lengthFrom exhausted seen values available = .ok (result, remaining)) :
    result = seen + values.length ∧ remaining + values.length = available := by
  induction values generalizing seen available with
  | nil =>
      simp only [lengthFrom, Except.ok.injEq, Prod.mk.injEq] at accepted
      simp [← accepted.1, ← accepted.2]
  | cons first rest ih =>
      cases available with
      | zero => simp [lengthFrom] at accepted
      | succ available =>
          have previous := ih (seen := seen + 1) (available := available) accepted
          simp only [List.length_cons]
          omega

/-- Computing the length is itself charged. The tail-recursive scan stops on
exhaustion without traversing the rest just to calculate a later charge. -/
def length {Value : Type} (exhausted : Error) (values : List Value) : Meter Error Nat :=
  lengthFrom exhausted 0 values

theorem length_residual {Value : Type} (exhausted : Error) (values : List Value)
    {available result remaining : Nat}
    (accepted : length exhausted values available = .ok (result, remaining)) :
    result = values.length ∧ remaining + values.length = available := by
  simpa only [Nat.zero_add] using lengthFrom_residual exhausted values accepted

private theorem lengthFrom_complete {Value : Type} (exhausted : Error) (values : List Value)
    {seen available : Nat} (fits : values.length ≤ available) :
    lengthFrom exhausted seen values available = .ok (seen + values.length, available - values.length) := by
  induction values generalizing seen available with
  | nil => simp [lengthFrom]
  | cons first rest ih =>
      cases available with
      | zero => simp at fits
      | succ available =>
          simp only [List.length_cons] at fits
          simpa [lengthFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (seen := seen + 1) (available := available) (by omega)

theorem length_complete {Value : Type} (exhausted : Error) (values : List Value)
    {available : Nat} (fits : values.length ≤ available) :
    length exhausted values available = .ok (values.length, available - values.length) := by
  simpa only [length, Nat.zero_add] using lengthFrom_complete exhausted values (seen := 0) fits

end Zkc.Source.Mathematical.AdmissionWork
