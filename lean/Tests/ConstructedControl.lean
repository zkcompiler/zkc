import Zkc.Source.Constructed.Control

namespace Tests.ConstructedControl
open Zkc.Source Zkc.Source.Constructed Zkc.Source.Constructed.Control

set_option maxHeartbeats 2000000

def step : Primitive := ⟨"step", "{}", "", "body", ["ui64", "field", "field"], ["field"]⟩
def iteration : RawBody := .flat [.apply step [0, 1, 2]] [0]
def subject : RawBody := .loop 3 0 ["field"] [1] ["field"] [2] iteration (.flat [] [0])
def inputTypes := ["ui64", "field", "field"]
def outputTypes := ["field"]
def checked := subject.elaborate inputTypes outputTypes

example : checked.isOk = true := by decide +kernel
example : (subject.elaborate ["field", "field", "field"] outputTypes).isOk = false := by decide +kernel

/-- A malformed zero-trip body is rejected statically. -/
example : ((RawBody.loop 0 0 ["field"] [1] ["field"] [2]
    (.flat [.apply step [0, 1, 9]] [0]) (.flat [] [0])).elaborate inputTypes outputTypes).isOk = false := by
  decide +kernel

example : ((RawBody.loop 3 0 ["field"] [1] ["ui64"] [2]
    iteration (.flat [] [0])).elaborate inputTypes outputTypes).isOk = false := by decide +kernel

def interface : PIR.Signature where
  Op := Nat × Nat × Nat
  Reply _ := Nat

abbrev meaning : Control.Meaning interface where
  Value _ := Nat
  condition value := value != 0
  primitive op args := match op.arguments, op.results, args with
    | [_, _, _], [_], .cons index (.cons value (.cons captured .nil)) =>
        .call (index, value, captured) fun reply => .done (.cons reply .nil)
    | _, _, _ => .halt .refused
  index := id
  count := id

def handler : PIR.Handler interface Nat (Nat × Nat × Nat) := fun request state =>
  ⟨.returned (request.1 + request.2.1 + request.2.2), state + 1, [request]⟩

def values (count : Nat) : Values meaning.Value inputTypes := .cons count (.cons 10 (.cons 4 .nil))
def run (count : Nat) := (subject.denote meaning outputTypes (values count)).run handler 0

example : run 0 = ⟨.returned (.cons 10 .nil), 0, []⟩ := rfl
example : run 2 = ⟨.returned (.cons 19 .nil), 2, [(0, 10, 4), (1, 14, 4)]⟩ := rfl
example : run 4 = ⟨.stopped .refused, 0, []⟩ := rfl

def stopping : PIR.Handler interface Nat (Nat × Nat × Nat) := fun request state =>
  if request.1 = 1 then ⟨.stopped .abort, state + 1, [request]⟩ else handler request state

example : (subject.denote meaning outputTypes (values 3)).run stopping 0 =
    ⟨.stopped .abort, 2, [(0, 10, 4), (1, 14, 4)]⟩ := rfl

/-- Sequence preserves the returned value without replaying or resetting effects. -/
example : ((RawBody.sequence outputTypes subject (.flat [] [0])).denote
    meaning outputTypes (values 2)).run handler 0 = run 2 := rfl

def typed : Body inputTypes outputTypes := checked.toOption.get (by decide +kernel)
theorem admitted : checked = .ok typed := rfl

example (count : Nat) :
    subject.denote meaning outputTypes (values count) = typed.denote meaning (values count) :=
  RawBody.denote_elaborate meaning subject typed admitted _

/-- Both arms must form even when an input could choose only the valid arm. -/
example : ((RawBody.branch 0 (.flat [] [0]) (.flat [] [9])).elaborate ["i1"] ["i1"]).isOk = false := by
  decide +kernel

#print axioms Zkc.Source.Constructed.Control.RawBody.denote_elaborate
end Tests.ConstructedControl
