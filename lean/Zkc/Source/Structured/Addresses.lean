module

public import Zkc.Source.RegionDecoding

@[expose] public section
namespace Zkc.Source.Structured

/-- Logical proof labels are separate from operational site names. Retained
repeat does not change ProtocolContext between iterations. Frames record checked
tree positions and explicitly chosen indices; they are not execution traces and
do not establish that a call or iteration was reached. -/
inductive InvocationFrame where
  | application (caller : Nat) (position : List Nat)
  | iteration (owner : Nat) (position : List Nat) (index : Nat)
  deriving DecidableEq, Repr

structure InvocationCoordinate where
  root : Nat
  frames : List InvocationFrame := []
  deriving DecidableEq, Repr

/-- A logical anchor names its actual construction occurrence. A port binds an
existing anchor at a call; only the selected root's input creates an input key.
The key contains neither table contents nor a native provider handle. -/
inductive OracleAnchorSite where
  | input (port : Nat)
  | construction (position : List Nat)
  deriving DecidableEq, Repr

structure OracleAnchor where
  invocation : InvocationCoordinate
  site : OracleAnchorSite
  deriving DecidableEq, Repr

end Zkc.Source.Structured
