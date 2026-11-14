module

public import Zkc.Core.Explain
public import Zkc.Frontend.Emit.Definitions
public import Zkc.Frontend.Typed.Find

@[expose] public section

set_option autoImplicit false

/-!
# The check of a definition

A refusal of facts is made per definition, as soon as its body has passed elaboration: the
definition is emitted alone and the core checks it. The functions it calls are headers: the
check of facts reads the signature of a callee and nothing of its body, so a body is checked
whatever became of its callees. The emission tolerates what a package does not have (a type
or an operation of specifications, an error node; `Emit.Named`), so that every body is
checked.

What the core does not justify comes back explained (`Zkc.Core.Explain`), each application at
the node it was emitted for. The package of this check is never written, run or admitted: the
package of a root is emitted with bodies and admitted whole.
-/

namespace Zkc.Frontend.Emit

open Static
open Typing (EmitM EmitFailure toTy rowNumber)

/-- An application that the core does not justify: the node it was emitted for, the role for
which it is a copy in a protocol body, and the core's explanation. -/
structure Finding where
  node : Option Typed.NodeId
  role : Option Nat
  explained : Zkc.Core.Explain.Explained
  deriving Inhabited

/-- What the core does not justify in the definitions of a checked package that satisfy
`own`, each at its node. -/
def findings (emitter : Typing.Emitter) (own : Zkc.Core.Refusal.Definition → Bool) :
    Except EmitFailure (List Finding) := do
  let named ← emitter.named
  let lowered ← match Zkc.Core.Named.lower named with
    | .ok lowered => pure lowered
    | .error (_, defect) =>
      throw (.defect s!"the lowering refuses the check of a definition at node {defect.tag}: {defect.message}")
  let typed ← match Zkc.Core.elaborate (Zkc.Core.fillMaxima lowered.package) with
    | .ok typed => pure typed
    | .error refusal => throw (.defect s!"the core refuses the check of a definition: {reprStr refusal}")
  return typed.explain.filterMap fun (definition, explained) =>
    if own definition then
      let origins := match definition with
        | .function number => lowered.functionOrigins.getD number []
        | .protocol number => lowered.protocolOrigins.getD number []
      let origin := origins.find? (·.path == explained.path)
      some { node := origin.map (·.tag), role := (origin.bind (·.role)).orElse fun _ => explained.role
             explained }
    else none

/-- The check of the body of a function instance: what the core does not justify in it.
`specification` says whether the function is one of specifications; `result` is its result
type. -/
def checkFunction (state : Compile.State) (callees : Typed.Callees) (specification : Bool)
    (body : Typed.FunctionBody) (result : ClosedType) : Except EmitFailure (List Finding) := do
  let emission : EmitM Unit := do
    modify fun emitter => { emitter with checking := true }
    let region ← Named.emitFunction { (← bodyContext) with callees } body
    let inputs ← body.parameters.toList.mapM fun binder => toTy binder.type
    let outputs := [← toTy result]
    modify fun emitter =>
      { emitter with functions := emitter.functions.push
                       { specificationOnly := specification, inputs, outputs, body := some region }
                     names := emitter.names.push "checked"
                     stops := emitter.stops.push true }
  let (_, emitter) ← (emission.run state).run {}
  let number := emitter.functions.size - 1
  findings emitter fun
    | .function found => found == number
    | .protocol _ => false

/-- What the check of a protocol definition gives: what the core does not justify in it, and
the keys of its sites in the order of their numbers. -/
structure ProtocolChecked where
  findings : List Finding
  keys : List Zkc.Core.SiteKey

/-- The check of the body of a protocol instance: the protocol alone, with the protocols it
applies before it and the functions that any of them calls as headers. -/
def checkProtocol (state : Compile.State) (inst : InstanceId) (checked : Typed.Checked) :
    Except EmitFailure ProtocolChecked := do
  let emission : EmitM Unit := do
    modify fun emitter => { emitter with checking := true }
    let protocol ← protocolOfChecked inst checked
    modify fun emitter =>
      { emitter with protocols := emitter.protocols.push protocol
                     protocolNames := emitter.protocolNames.push "checked"
                     protocolRoles := emitter.protocolRoles.push
                       (match checked.definition.body with
                         | .protocol body => body.roster.toList
                         | _ => []) }
  let (_, emitter) ← (emission.run state).run {}
  let number := emitter.protocols.size - 1
  let found ← findings emitter fun
    | .protocol found => found == number
    | .function _ => false
  -- the keys of the sites, in the order of their numbers
  let named ← emitter.named
  let keys ← match Zkc.Core.Named.lower named with
    | .ok lowered => pure (lowered.keys.getD number [])
    | .error (_, refused) =>
      throw (.defect s!"the lowering refuses the check of a definition at node {refused.tag}: {refused.message}")
  return { findings := found, keys }

end Zkc.Frontend.Emit
