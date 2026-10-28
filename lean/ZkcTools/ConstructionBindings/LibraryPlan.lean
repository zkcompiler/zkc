module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Untrusted discovery of the source declarations needed by a connection.
The admitted declaration order is acyclic. Walking it backwards discovers
reachable roles; the result is returned in dependency order, with each role
once regardless of call multiplicity or symbolic repeat count. No protocol
names, target slots, layouts, or process equations are authored here.

This plan is not correspondence evidence. The source-template builder checks
its selected bodies and signatures, and the connection certificate checks every
application and its target placement. Missing or superfluous proposals cannot
establish a simulation by themselves. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.LibraryPlan
open Zkc.Source Zkc.Source.Structured

structure Selection where
  declaration : Nat
  role : Nat
  deriving DecidableEq, Repr

structure Call where
  signature : ProtocolSignature
  role : Nat
  deriving DecidableEq, Repr

mutual
  /-- Inspect only callbacks active for this participant. Role substitutions
  are local to the containing declaration, including below nested repeats. -/
  def calls (role roster : Nat) : RawRegion Ty ProtocolOp → Except String (List Call)
    | .ret _ | .stop _ => pure []
    | .bind _ body next => return (← calls role roster body) ++ (← calls role roster next)
    | .letOp op _ _ bodies next => do
      let here ← match op with
        | .protocolApply signature roles _ => do
          unless roles.length == signature.roles.length && roles.Nodup &&
              roles.all (· < roster) do throw "connection-library-call-roles"
          if roles.contains role then pure [⟨signature, roles.idxOf role⟩] else pure []
        | .repeat spec _ =>
          if spec.roles.contains role then bodyCalls role roster bodies else pure []
        | _ => pure []
      return here ++ (← calls role roster next)

  def bodyCalls (role roster : Nat) : RawRegions Ty ProtocolOp → Except String (List Call)
    | .nil => pure []
    | .cons _ _ body rest => return (← calls role roster body) ++ (← bodyCalls role roster rest)
end

/-- Discover a root's dependency closure, excluding the root itself. Exact
signatures resolve only in the strict earlier prefix. Refuse malformed orders
rather than introducing fuel or silently dropping an unresolved dependency. -/
def discover (declarations : List CheckedProtocol) (entry : Nat) (roles : List Nat) :
    Except String (List Selection) := do
  let some root := declarations[entry]? | throw "connection-library-root"
  unless roles.all (· < root.roles.length) do throw "connection-library-root-role"
  let roots := roles.eraseDups.map (Selection.mk entry)
  let mut pending := roots
  let mut ordered := []
  for (definition, index) in declarations.zipIdx.reverse do
    let selected := pending.filter (·.declaration == index)
    unless selected.all (·.role < definition.roles.length) do
      throw "connection-library-selected-role"
    -- Stable role order does not depend on which application mentioned it first.
    let selected := (List.range definition.roles.length).filterMap fun role =>
      if selected.contains ⟨index, role⟩ then some (Selection.mk index role) else none
    for selectedRole in selected do
      let dependencies ← calls selectedRole.role definition.roles.length definition.raw
      for call in dependencies do
        let earlier := declarations.take index
        let target := earlier.findIdx (·.signature == call.signature)
        unless target < earlier.length do throw "connection-library-missing-earlier-callee"
        let needed := Selection.mk target call.role
        unless pending.contains needed do pending := needed :: pending
    ordered := selected ++ ordered
    pending := pending.filter (·.declaration != index)
  unless pending.isEmpty do throw "connection-library-unresolved-selection"
  return ordered.filter (!roots.contains ·)

/-- The ordinary path derives its root and declaration table from admission. -/
def forPayload (payload : UnitPayload) (roles : List Nat) : Except String (List Selection) :=
  discover payload.protocols payload.entryIndex roles

end ZkcTools.ConstructionBindings.LibraryPlan
