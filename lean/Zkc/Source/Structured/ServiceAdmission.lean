module

public import Zkc.Source.Structured.RepeatAdmission

@[expose] public section

/-! Positive constant-u64 provenance for index service operands. This is a
source formation check, independent of any downstream provider restrictions.
Immutable repeat captures retain literal provenance; induction and mutable
state never acquire it. Arithmetic equalities cannot manufacture provenance. -/
set_option autoImplicit false
namespace Zkc.Source.Structured

abbrev ServiceConstants := List (Option Nat)

def serviceConstants (descriptor : Descriptor) (types : List Ty) : ServiceConstants :=
  match descriptor, types with
  | .indexConstant text, [.index] => [(Format.indexDecimal text).toOption]
  | _, _ => types.map fun _ => none

mutual
def checkServiceBlock (constants : ServiceConstants) : Block → Except String Unit
  | .block instructions _ => checkServiceInstructions constants instructions

def checkServiceInstructions : ServiceConstants → List Instruction → Except String Unit
  | _, [] => .ok ()
  | constants, .instruction descriptor operands types regions _ :: rest => do
    match descriptor with
    | .sampleIndex .. | .sampleIndices .. =>
      let arity := match descriptor with | .sampleIndex .. => 2 | _ => 3
      if operands.length != arity then throw "structured-index-service-signature"
      for operand in operands.drop 1 do
        let some (some value) := constants[operand]? |
          throw "structured-index-service-constant"
        if value = 0 ∨ indexLimit ≤ value then throw "structured-index-service-positive"
    | _ => pure ()
    match descriptor, regions with
    | .protocolRepeat carried _ _ _, [.region inputs _ body] =>
      let captures := (operands.drop (1 + carried)).map fun reference =>
        (constants[reference]?).getD none
      let nested := none :: (List.replicate carried none ++ captures)
      if nested.length != inputs.length then throw "structured-protocol-signature"
      checkServiceBlock nested body
    | _, _ => pure ()
    checkServiceInstructions (serviceConstants descriptor types ++ constants) rest
end

/-- A successful checked prefix cannot create a successful continuation. -/
theorem checkedServiceContinuation {A : Type} {check : Except String Unit}
    {action : Except String A} {value : A}
    (accepted : (do check; action) = .ok value) : action = .ok value := by
  cases check <;> simp_all [bind, Except.bind]

end Zkc.Source.Structured
