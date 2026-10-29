module

public import Zkc.Construction.OriginalInputs
public import Zkc.Construction.ArtifactBinding

@[expose] public section

/-! Request-fixed checkpoint semantics for physical source inputs. This module
contains no alignment certificate or proof-producing implementation. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionRoot
open Zkc.Source Zkc.Source.Structured

/-- At every checkpoint retain the whole physical input and every component
that its actual ABI decodes. Malformed inputs still retain their physical row,
without fabricating a successful source input tuple. -/
def InputFrames {carriers : Carriers} {A : Type} (abi : Original.InputABI)
    (types : List Ty) (physical : Domain.Environment carriers)
    (_source : PIR.Process (Domain.effects carriers) A) (frame : Domain.Environment carriers) : Prop :=
  ArtifactBinding.Captures physical frame ∧
    ∀ values : Values (Component carriers.Value) types, abi.read physical types = some values →
      Original.ValuesHolds frame abi.locations values

end Zkc.Construction.ConnectionRoot
