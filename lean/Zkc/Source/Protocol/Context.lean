import Zkc.Source.Context

/-! Typed ports retain both a domain sort and its participant location. -/

set_option autoImplicit false

namespace Zkc.Source.Protocol

abbrev Port (Role Ty : Type) := Role × Ty

abbrev PortValue {Role Ty : Type} (Value : Ty → Type) (port : Port Role Ty) := Value port.2

def owned {Role Ty : Type} (role : Role) (types : List Ty) : List (Port Role Ty) :=
  types.map fun ty => (role, ty)

/-- Remove location tags after the operand types have checked the owning role. -/
def localValues {Role Ty : Type} {Value : Ty → Type} (role : Role) :
    {types : List Ty} → Values (PortValue (Role := Role) Value) (owned role types) →
      Values Value types
  | [], .nil => .nil
  | _ :: _, .cons value rest => .cons value (localValues role rest)

end Zkc.Source.Protocol
