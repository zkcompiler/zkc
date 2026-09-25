import Zkc.Semantics.MonadExecution

/-! Outer exceptions and inner stops have different retention behavior.
The first operation returns a mutation and event in both handlers. Only the
inner-stop execution retains that prefix in the final result.
-/

set_option autoImplicit false

namespace Tests.OuterEffects

open PIR

inductive Op where
  | first | fail | afterFailure

abbrev interface : Signature := ⟨Op, fun _ => Unit⟩

def firstCall : Proc interface Unit := .call .first .done

def program : Proc interface Unit :=
  firstCall.bind (fun _ => .call .fail (fun _ => .call .afterFailure .done))

def outerFailure : MonadHandler (Except Unit) interface Nat Nat
  | .first, state => .ok ⟨.returned (), state + 1, [7]⟩
  | .fail, _ => .error ()
  | .afterFailure, state => .ok ⟨.returned (), state + 100, [99]⟩

def innerStop : MonadHandler (Except Unit) interface Nat Nat
  | .first, state => .ok ⟨.returned (), state + 1, [7]⟩
  | .fail, state => .ok ⟨.stopped .abort, state + 1, [8]⟩
  | .afterFailure, state => .ok ⟨.returned (), state + 100, [99]⟩

/-- Both handlers first produce the same successful, mutated execution. -/
example (state : Nat) : firstCall.runM outerFailure state =
    .ok ⟨.returned (), state + 1, [7]⟩ := rfl

example (state : Nat) : firstCall.runM innerStop state =
    .ok ⟨.returned (), state + 1, [7]⟩ := rfl

/-- The outer failure carries no `Execution`, including no earlier prefix. -/
example (state : Nat) : program.runM outerFailure state = .error () := rfl

/-- An inner stop retains both mutations and both events and prevents the last call. -/
example (state : Nat) : program.runM innerStop state =
    .ok ⟨.stopped .abort, state + 1 + 1, [7, 8]⟩ := rfl

example (state : Nat) : program.runM outerFailure state ≠ program.runM innerStop state := by
  intro same
  cases same

/-- No record can be extracted merely by assuming the outer execution completed. -/
example (result : Execution Nat Nat Unit) : program.runM outerFailure 0 ≠ .ok result := by
  intro same
  cases same

end Tests.OuterEffects
