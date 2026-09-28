import Zkc.Source.Mathematical.Context
import Zkc.Semantics.Execution

/-! A closed-instance core of mathematical protocols. Pure nodes retain typed
references; protocol bodies retain indexed iteration and ordered effects.
Static admission, calls and transport encodings have separate profile contracts. -/

set_option autoImplicit false
namespace Zkc.Source.Mathematical

structure Language where
  Ty : Type
  Op : Type
  arguments : Op → List Ty
  result : Op → Ty
  index : Nat → Ty
  condition : Ty
  Wire : Ty → Type

structure Capability (Role Ty : Type) where
  permitted : List Role
  arguments : List Ty
  result : Ty

variable {Role : Type} [DecidableEq Role]

structure Signature (Role Ty : Type) where
  arguments : List (Port Role Ty)
  results : List (Port Role Ty)

/-- Ports may alias a root service. Distinct port names do not imply fresh state. -/
abbrev CapabilityBinding {Role Ty : Type} (capabilities : List (Capability Role Ty)) :=
  {signature : Capability Role Ty} → Var capabilities signature → Var capabilities signature

inductive Program (parties : List Role) (language : Language)
    (capabilities : List (Capability Role language.Ty))
    (scope : List (Signature Role language.Ty)) :
    List (Port Role language.Ty) → List (Port Role language.Ty) → Type where
  | ret {Γ results} (values : Bindings Γ results) :
      Program parties language capabilities scope Γ results
  | pure {Γ results roles} (op : language.Op) (args : Inputs Γ (language.arguments op))
      (availability : roles = Inputs.available parties args)
      (next : Program parties language capabilities scope
        (⟨roles, language.result op⟩ :: Γ) results) :
      Program parties language capabilities scope Γ results
  | message {Γ results ty} (site : Nat) (schema : language.Wire ty)
      (sender receiver : Role) (different : sender ≠ receiver)
      (value : Reference Γ ⟨[sender], ty⟩)
      (next : Program parties language capabilities scope (⟨[sender, receiver], ty⟩ :: Γ) results) :
      Program parties language capabilities scope Γ results
  | query {Γ results signature} (site : Nat) (owner : Role)
      (capability : Var capabilities signature) (permitted : owner ∈ signature.permitted)
      (args : Inputs Γ signature.arguments)
      (available : owner ∈ Inputs.available parties args)
      (next : Program parties language capabilities scope (⟨[owner], signature.result⟩ :: Γ) results) :
      Program parties language capabilities scope Γ results
  | repeat {Γ results ports} (site count : Nat) (initial : Bindings Γ ports)
      (body : Program parties language capabilities scope
        (⟨parties, language.index count⟩ :: (ports ++ Γ)) ports)
      (next : Program parties language capabilities scope (ports ++ Γ) results) :
      Program parties language capabilities scope Γ results
  | guard {Γ results} (site : Nat) (owner : Role)
      (condition : Reference Γ ⟨[owner], language.condition⟩)
      (next : Program parties language capabilities scope Γ results) :
      Program parties language capabilities scope Γ results
  | invoke {Γ results signature} (site : Nat) (callee : Var scope signature)
      (capabilityBinding : CapabilityBinding capabilities)
      (arguments : Bindings Γ signature.arguments)
      (next : Program parties language capabilities scope (signature.results ++ Γ) results) :
      Program parties language capabilities scope Γ results
  | stop {Γ results} (site : Nat) (owner : Role) (reason : PIR.Stop) :
      Program parties language capabilities scope Γ results

/-- Each stored callee sees only earlier definitions. Bodies share the module's
role and root-capability vocabulary; bindings resolve aliases explicitly. -/
inductive Definitions (parties : List Role) (language : Language)
    (capabilities : List (Capability Role language.Ty)) :
    List (Signature Role language.Ty) → Type where
  | nil : Definitions parties language capabilities []
  | snoc {scope} (previous : Definitions parties language capabilities scope)
      (signature : Signature Role language.Ty)
      (body : Program parties language capabilities scope signature.arguments signature.results) :
      Definitions parties language capabilities (signature :: scope)

end Zkc.Source.Mathematical
