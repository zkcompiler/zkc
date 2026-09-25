import Tools.Interactive.Syntax

set_option autoImplicit false

namespace Tools.Artifact.Identity
open Lean (Json)
open Tools.Interactive

/-- The mathematical operation declaration retained by identity. Attributes and
ordered operands/results remain on each instruction, outside this declaration. -/
structure OperationContract where
  contract : String
  arguments : List String
  deriving DecidableEq

def OperationContract.ofBinding (binding : OperationBinding) : OperationContract :=
  ⟨binding.contract, binding.arguments⟩

def OperationContract.json (contract : OperationContract) : Json :=
  .arr #[.str "operation", .str contract.contract, .arr (contract.arguments.map Json.str).toArray]

theorem OperationContract.ofBinding_eq_iff (left right : OperationBinding) :
    ofBinding left = ofBinding right ↔
      left.contract = right.contract ∧ left.arguments = right.arguments := by
  simp [ofBinding, OperationContract.mk.injEq]

/-- Alias and physical choice are forgotten only at this representation
projection. Their original declarations must still pass formation. -/
theorem OperationContract.ofBinding_representations (binding : OperationBinding)
    (alias implementation : String) :
    ofBinding { binding with name := alias, implementation } = ofBinding binding := rfl

end Tools.Artifact.Identity
