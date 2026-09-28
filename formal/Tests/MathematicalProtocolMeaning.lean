import Zkc.Source.Mathematical.DataBounds
import Tests.MathematicalProtocol
import Zkc.Source.Mathematical.ProtocolMeaning

set_option autoImplicit false
namespace Tests.MathematicalProtocolMeaning
open Zkc.Source Zkc.Source.Mathematical
open MathematicalGraph (Ty number publicPort privatePort)
open MathematicalProtocol (vocabulary capabilities)

abbrev meaning : Graph.Interpretation vocabulary.toAlgebra where
  Value := MathematicalGraph.meaning.Value
  count := id
  pure := MathematicalGraph.meaning.pure
  condition := MathematicalGraph.meaning.condition
  index := id
  tuple := Data.product
  project := Data.project
  vector := id
  element := id

structure Event where
  location : Location
  root : Option Nat
  deriving DecidableEq, Repr

abbrev State := Nat → Nat
abbrev Interface := Protocol.interface 0 vocabulary meaning.Value

def execute {A : Type} : Nat → PIR.Proc Interface A → State →
    Except String (A × State × List Event)
  | 0, _, _ => .error "fuel"
  | _ + 1, .done value, state => .ok (value, state, [])
  | _ + 1, .halt _, _ => .error "halt"
  | fuel + 1, .call action next, state => do
      match action, next with
      | .query location root _ _, next =>
          let (value, final, trace) ← execute fuel (next (state root))
            (fun queried => if queried = root then state root + 1 else state queried)
          return (value, final, ⟨location, some root⟩ :: trace)
      | .local location _ roots arguments, next =>
          let reply := roots.foldl (fun n root => n + state root) (arguments.get .here)
          let (value, final, trace) ← execute fuel (next reply) state
          return (value, final, ⟨location, none⟩ :: trace)
      | .send location _ _ _, next =>
          let (value, final, trace) ← execute fuel (next ()) state
          return (value, final, ⟨location, none⟩ :: trace)
      | .receive .., _ => throw "external reply required"
      | .stop .., _ => throw "stop"

def run (raw : Protocol.Raw Nat vocabulary) : Except String (Nat × Nat × List Event) := do
  let checked ← (Protocol.decode [0, 1] capabilities [] Data.capacity
    MathematicalGraph.countValid 64 [privatePort] [publicPort] 0 raw).mapError (fun _ => "admission")
  let inputs : Values (Component meaning.Value 0) [privatePort] := .cons (fun _ => 9) .nil
  let process := checked.program.openMeaning meaning 0 (fun v => inputs.get v)
  let (values, state, trace) ← execute 32 process (fun _ => 0)
  return (values.get .here (by decide), state 7, trace)

example : run (MathematicalProtocol.repeated 0) =
    .ok (9, 0, [⟨⟨[], 2⟩, none⟩]) := rfl

example : run (MathematicalProtocol.repeated 3) =
    .ok (2, 3,
      [⟨⟨[.iteration 0 0], 1⟩, some 7⟩,
       ⟨⟨[.iteration 0 1], 1⟩, some 7⟩,
       ⟨⟨[.iteration 0 2], 1⟩, some 7⟩,
       ⟨⟨[], 2⟩, none⟩]) := rfl

-- Distinct port names sharing root seven observe successive states.
example : run (.query 0 0 0 [0] (.query 1 0 1 [0]
    (.message 2 ⟨number, ()⟩ 0 1 0 (.ret [0])))) =
    .ok (1, 2, [⟨⟨[], 0⟩, some 7⟩, ⟨⟨[], 1⟩, some 7⟩, ⟨⟨[], 2⟩, none⟩]) := rfl

end Tests.MathematicalProtocolMeaning
