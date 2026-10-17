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
