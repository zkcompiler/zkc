module

meta import Lean.Elab.Command
meta import Lean.Meta.Eqns
public import Zkc.Executable.Execution

@[expose] public section

/-! Proof framing and the scalar decoder projection, independent of any
constructed execution semantics. -/
set_option autoImplicit false
namespace Zkc.Executable
open Zkc.Construction

/-- The typed proof a message byte string denotes for a sequence of receive
types: each length-framed message decoded at its type, up to the first message
that is missing or does not decode. Bytes left after the last receive become
one unread entry, so that a run which returns has read the whole proof exactly
when its ideal reading has. -/
def decodeProof {F G : Type} (decode : PhysicalType → List UInt8 → Option (Payload F G)) :
    List PhysicalType → List UInt8 → Proof F G
  | [], bytes => if bytes.isEmpty then [] else [.boolean false]
  | type :: types, bytes =>
      match readFrame bytes with
      | some (payload, rest) =>
          match decode type payload with
          | some value => value :: decodeProof decode types rest
          | none => []
      | none => []


end Zkc.Executable

run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? ``Zkc.Executable.decodeProof
