import Zkc.Source.Context

/-! Role components of mathematical values. Availability grants a read at a
role; it does not assert equality between roles. -/

set_option autoImplicit false
namespace Zkc.Source.Mathematical

structure Port (Role Ty : Type) where
  roles : List Role
  ty : Ty
  deriving DecidableEq, Repr

variable {Role Ty : Type}

abbrev Component (Value : Ty → Type) (self : Role) (port : Port Role Ty) :=
  self ∈ port.roles → Value port.ty

abbrev Environment (Value : Ty → Type) (self : Role) (Γ : List (Port Role Ty)) :=
  Source.Environment (Component Value self) Γ

/-- A typed operand with an explicit availability weakening. -/
structure Reference (Γ : List (Port Role Ty)) (required : Port Role Ty) where
  available : List Role
  operand : Var Γ ⟨available, required.ty⟩
  covers : ∀ role, role ∈ required.roles → role ∈ available

def Reference.exact {Γ : List (Port Role Ty)} {port : Port Role Ty}
    (operand : Var Γ port) : Reference Γ port :=
  ⟨port.roles, operand, fun _ h => h⟩

def Reference.read {Value : Ty → Type} {self : Role} {Γ : List (Port Role Ty)}
    {port : Port Role Ty} (ref : Reference Γ port) (env : Environment Value self Γ) :
    Component Value self port := fun h =>
      env (ty := ⟨ref.available, port.ty⟩) ref.operand (ref.covers self h)

abbrev Bindings (Γ ports : List (Port Role Ty)) := Values (Reference Γ) ports

def Bindings.read {Value : Ty → Type} {self : Role} {Γ ports : List (Port Role Ty)}
    (refs : Bindings Γ ports) (env : Environment Value self Γ) :
    Values (Component Value self) ports :=
  match refs with
  | .nil => .nil
  | .cons ref rest => .cons (ref.read env) (Bindings.read rest env)

/-- Each pure operand retains its actual availability set. -/
abbrev Input (Γ : List (Port Role Ty)) (ty : Ty) :=
  (roles : List Role) × Var Γ ⟨roles, ty⟩

abbrev Inputs (Γ : List (Port Role Ty)) (types : List Ty) := Values (Input Γ) types

def Inputs.available [DecidableEq Role] (parties : List Role)
    {Γ : List (Port Role Ty)} {types : List Ty} : Inputs Γ types → List Role
  | .nil => parties
  | .cons input rest => (Inputs.available parties rest).filter (fun role => role ∈ input.1)

def Inputs.read [DecidableEq Role] {Value : Ty → Type} {self : Role}
    (parties : List Role) {Γ : List (Port Role Ty)} {types : List Ty}
    (inputs : Inputs Γ types) (env : Environment Value self Γ)
    (present : self ∈ Inputs.available parties inputs) : Values Value types :=
  match inputs with
  | .nil => .nil
  | .cons input rest =>
      .cons (env input.2 (by simpa [Inputs.available] using (List.mem_filter.mp present).2))
        (Inputs.read parties rest env (List.mem_filter.mp present).1)

end Zkc.Source.Mathematical
