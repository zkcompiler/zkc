import Zkc.Semantics.Iteration

/-! Executable reference for the native controller differential corpus. -/
set_option autoImplicit false
namespace Examples.Iteration
open PIR
abbrev signature : Signature := ⟨Unit, fun _ => Nat⟩
def handler (fatal : Bool) : Handler signature Nat Nat := fun _ state =>
  ⟨if fatal then .stopped .reject else .returned state, state + 1, [state]⟩
def body (target : Nat) (_ : Unit) : Proc signature (Unit ⊕ Nat) :=
  .call () fun value => .done (if value < target then .inl () else .inr value)
def stopTag : Stop → String
  | .reject => "reject"
  | .abort => "abort"
  | .exhausted => "exhausted"
  | .incomplete => "incomplete"
  | .refused => "refused"
def resultTag : Outcome Nat → String
  | .returned value => s!"returned:{value}"
  | .stopped reason => stopTag reason
def prefixTag : Outcome (Nat ⊕ Nat) → String
  | .returned (.inl next) => s!"pending:{next}"
  | .returned (.inr value) => s!"returned:{value}"
  | .stopped reason => stopTag reason
def record {A : Type} (tag : Outcome A → String) (result : Execution Nat Nat A) : String :=
  let events := String.intercalate "," (result.events.map toString)
  s!"{tag result.outcome}|{result.state}|{events}"
def line (target fuel initial : Nat) (fatal : Bool) : String :=
  let result := PIR.Iteration.evaluate (body target) (handler fatal) fuel () initial
  let tag := match result.outcome with
    | .returned (.inl _) => "pending"
    | .returned (.inr value) => s!"returned:{value}"
    | .stopped reason => stopTag reason
  let events := String.intercalate "," (result.events.map toString)
  s!"{target}|{fuel}|{initial}|{fatal}|{tag}|{result.state}|{events}"

abbrev countdownSignature : Signature := ⟨Nat, fun _ => Nat⟩
def countdownHandler : Handler countdownSignature Nat Nat := fun left state =>
  ⟨.returned state, state + left, [left]⟩
def countdown (left : Nat) : Proc countdownSignature (Nat ⊕ Nat) :=
  .call left fun state => .done (if left = 0 then .inr state else .inl (left - 1))

/-- Stop after one successful continuation, retaining both calls' effects. -/
def stoppingHandler (reason : Stop) : Handler signature Nat Nat := fun _ state =>
  ⟨if state = 0 then .returned state else .stopped reason, state + 1, [state]⟩

def run : IO Unit := do
  -- Retain the original corpus verbatim and extend it with independent cases.
  for target in [:6] do
    for fuel in [:9] do
      for initial in [:4] do
        for fatal in [false, true] do
          IO.println (line target fuel initial fatal)
  for seed in [0, 1, 3] do
    for initial in [0, 4] do
      for first in [:6] do
        for second in [:6] do
          let whole := Iteration.evaluate countdown countdownHandler (first + second) seed initial
          let split := (Iteration.evaluate countdown countdownHandler first seed initial).follow
            (fun answer state => (Iteration.resume countdown second answer).run countdownHandler state)
          let key := s!"resume|{seed}|{initial}|{first}|{second}"
          IO.println s!"{key}|whole|{record prefixTag whole}"
          IO.println s!"{key}|split|{record prefixTag split}"
          IO.println s!"{key}|close-whole|{record resultTag (Iteration.close whole)}"
          IO.println s!"{key}|close-split|{record resultTag (Iteration.close split)}"
  for reason in [Stop.reject, .abort, .exhausted, .incomplete, .refused] do
    for fuel in [0, 1, 3] do
      let result := Iteration.evaluate (body 10) (stoppingHandler reason) fuel () 0
      let tag := match result.outcome with
        | .returned (.inl _) => "pending"
        | .returned (.inr value) => s!"returned:{value}"
        | .stopped why => stopTag why
      let key := s!"stop|{stopTag reason}|{fuel}"
      IO.println s!"{key}|prefix|{record (fun _ => tag) result}"
      IO.println s!"{key}|close|{record resultTag (Iteration.close result)}"

end Examples.Iteration
