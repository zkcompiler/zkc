import Zkc.Source.MessageSchema

set_option autoImplicit false

namespace Tests.MessageSchema
open Zkc.Source.MessageSchema

-- This presentation deliberately does not identify nominal domains by cardinality.
def sample : Contract := ⟨10,20,30,97,2,0,3⟩
def badEndpoint : Raw := ⟨10,20,30,0,[1,3,0]⟩
def endpoint (xs : List Nat) : Nat :=
  (2 * xs[0]! + xs[1]! + xs[2]!) % 97

example : (check sample badEndpoint).isSome = true := by decide
example : endpoint badEndpoint.values ≠ 3 := by decide
example : check sample {badEndpoint with values := [1,3]} = none := by decide
example : check sample {badEndpoint with domainId := 21} = none := by decide
example : check sample {badEndpoint with fieldId := 11} = none := by decide
example : check sample {badEndpoint with instanceId := 31} = none := by decide
example : check sample {badEndpoint with round := 1} = none := by decide
example : check {sample with round := 2} {badEndpoint with round := 2} = none := by decide
example : check sample {badEndpoint with values := [97,3,0]} = none := by decide
example : Ix.eval [3] (some 0) (.hidden 0) = none := rfl
example : form ⟨10,20,30,97,.lit 2,.hidden 0⟩ [3] 0 = none := rfl
example : parse [10,20,30] = none := rfl
example : decode sample (encode badEndpoint ++ [0]) = none := by decide

-- What encode writes, decode reads: the only positive direction stated here,
-- beside the refusals above it.
#guard (decode sample (encode badEndpoint)).isSome
#guard endpoint badEndpoint.values = 5

end Tests.MessageSchema
