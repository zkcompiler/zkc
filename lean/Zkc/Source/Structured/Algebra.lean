module

public import Zkc.Source.Structured.Table
public import Mathlib.Algebra.Module.Defs

@[expose] public section

/-! Uniform mathematical values and an independent site-observation hook.
Group values are independent of scalars and interpreted by lawful modules. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

def closedInterface : PIR.Signature := ⟨Empty, fun value => nomatch value⟩
abbrev Closed (A : Type) := PIR.Proc closedInterface A

/-- Nominal domain interpretation. Services retain their actual handle. -/
abbrev assignment (F G : Type) : Ty → Type
  | .boolean => Bool
  | .index => Nat
  | .field _ => F
  | .vector _ => List F
  | .group _ => G
  | .service _ => Nat

/-! Domain carriers. Domain identities are the native catalogue strings that
exported sorts name. Carriers interpret identities as types and nothing else, so
the value interpretation needs no instance arguments; the structures operations
use are added by domain models (`DomainModels`). -/

/-- A type for every field identity and every group identity. -/
structure Carriers where
  Field : String → Type
  Group : String → Type

/-- Every field identity interpreted by `F` and every group identity by `G`. -/
abbrev uniformCarriers (F G : Type) : Carriers where
  Field := fun _ => F
  Group := fun _ => G

/-- Values of each sort under the carriers. Services retain their actual handle.
The case analysis is the one of `assignment` in this module, so that the uniform
carriers have the same values by reducible definitional unfolding. -/
abbrev Carriers.Value (carriers : Carriers) : Ty → Type
  | .boolean => Bool
  | .index => Nat
  | .field domain => carriers.Field domain
  | .vector domain => List (carriers.Field domain)
  | .group domain => carriers.Group domain
  | .service _ => Nat

theorem assignment_eq_value (F G : Type) : assignment F G = (uniformCarriers F G).Value := by
  with_reducible rfl

/-- Site observations are the only configurable effects of mathematical bodies.
Group operations themselves use the lawful module instances directly. -/
structure SiteObservations (interface : PIR.Signature) where
  mark : String → PIR.Proc interface Unit

/-- Ignore site labels while retaining the chosen effect interface. -/
def SiteObservations.silent (interface : PIR.Signature) : SiteObservations interface where
  mark := fun _ => .done ()

abbrev SiteObservations.closed : SiteObservations closedInterface :=
  silent closedInterface

end Zkc.Source.Structured
