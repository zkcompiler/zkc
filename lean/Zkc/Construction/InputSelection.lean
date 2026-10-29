module

public import Zkc.Construction.Structured

@[expose] public section

/-! Data selection for the scalar input adapter. This module defines only the
input mapping; complete source correspondence is a separate semantic obligation
in `ConnectionAdmission.Required`. -/
set_option autoImplicit false
namespace Zkc.Construction
open Zkc.Source.Structured

/-- What the projected role holds for one original component: nothing (the
component is absent at the role), the value at an exported reference, a present
value the exported program does not keep, or the replaced service. -/
inductive Slot where
  | absent
  | held (reference : Nat)
  | free
  | service
  | local (root : Nat)
  deriving DecidableEq, Repr

/-- The validator's input slots before masking: each published data input is held
at its exported position, the replaced service is the handle, and every other
input is absent. -/
def inputSlots (context : Context) (policy : Policy) (inputs : List Ty) : List Slot :=
  (List.range inputs.length).map fun index =>
    match policy.publicInputs.idxOf? index with
    | some position => .held position
    | none =>
        if some index = context.service then .service
        else match inputs[index]? with | some (.service _) => .local index | _ => .absent

end Zkc.Construction
