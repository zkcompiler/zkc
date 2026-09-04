import M0.Eval

open M0

namespace ZkcTermEvaluatorCorrespondenceProbe

def asFin3 (value : Nat) : Fin 3 :=
  ⟨value % 3, Nat.mod_lt value (by decide)⟩

def bit (value : Bool) : Nat := if value then 1 else 0

def guardDenotation (value : Bool) : Bool :=
  let environment : List TypedValue := [⟨abstractBool, .bool value⟩]
  match evalCore (natLtPrimitive abstractNatLt abstractBool) 64
      (.variable 0 abstractBool) environment with
  | .success ⟨_, .bool answer⟩ _ => answer
  | _ => false

def emitRows : IO Unit := do
  for statement in List.range 3 do
    for commitment in List.range 3 do
      for challenge in List.range 3 do
        for response in List.range 3 do
          let answer := schnorrDenotation (asFin3 statement) (asFin3 commitment)
            (asFin3 challenge) (asFin3 response)
          IO.println s!"TERM\t{statement}\t{commitment}\t{challenge}\t{response}\t{bit answer}"
  for value in [false, true] do
    IO.println s!"GUARD\t{bit value}\t{bit (guardDenotation value)}"

#eval emitRows

end ZkcTermEvaluatorCorrespondenceProbe
