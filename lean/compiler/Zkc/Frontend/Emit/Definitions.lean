module

public import Zkc.Frontend.Emit.NamedProtocol
public import Zkc.Frontend.Passes.Events
public import Zkc.Frontend.Typed.Checked

@[expose] public section

set_option autoImplicit false

/-!
# The definitions of a package, from their trees

A package is emitted per root: the function and protocol instances the root reaches. A
function is numbered when its emission is complete, after every function it calls, and a
protocol after the functions and protocols it reaches, so that a definition names only
definitions before it (`docs/spec/core/package.md`).

A function instance is emitted from its typed tree, and a protocol instance from its checked
tree: the tree and the tables of the passes. In the check of a definition
(`Emitter.checking`) a function that a body calls is a header, entered at the types of the
call: the check of facts reads the signature of a callee and nothing of its body.
-/

namespace Zkc.Frontend.Emit

open Static
open Typing (EmitM EmitFailure toTy rowNumber defect)

/-- The header of a function instance in the check of a definition, entered at the types of a
call when it is new: its number. -/
def headerNumber (inst : InstanceId) (inputs : Array ClosedType) (output : ClosedType) : EmitM Nat := do
  if let some index := (← get).functionIndex[inst]? then return index
  let specificationOnly := match (← read).results.body? inst with
    | some (.done code) => code.specificationOnly
    | _ => false
  let header : Zkc.Core.Named.Function :=
    { specificationOnly, inputs := ← inputs.toList.mapM toTy, outputs := [← toTy output], body := none }
  let emitter ← get
  let index := emitter.functions.size
  set { emitter with functions := emitter.functions.push header
                     functionIndex := emitter.functionIndex.insert inst index
                     names := emitter.names.push s!"callee {inst}"
                     stops := emitter.stops.push true }
  return index

mutual
  /-- What the emission of a typed tree asks of the package: whether a function instance can
  stop or is bound to a restricted row, and the operation that applies it. -/
  partial def bodyContext : EmitM Named.Context := do
    let results := (← read).results
    let checking := (← get).checking
    let stops (inst : InstanceId) : Bool := match results.body? inst with
      | some (.done code) => code.canStop
      | _ => false
    let restricted (inst : InstanceId) : Bool := match results.body? inst with
      | some (.row row) =>
        (match (results.rows[row]?).map fun (entry : Typing.Row) => entry.kind with
          | some (Typing.RowKind.restricted _) => true
          | _ => false)
      | _ => false
    let apply (inst : InstanceId) (inputs : Array ClosedType) (output : ClosedType)
        (operands : List Zkc.Core.Named.ValueName) : EmitM Zkc.Core.Named.LocalOp := do
      match results.body? inst with
      | some (.row row) => return .op (← rowNumber row) operands
      | _ =>
        if checking then return .call (← headerNumber inst inputs output) operands
        return .call (← functionOf inst) operands
    return { callees := { stops, restricted }, apply, checking }

  /-- The number of a function instance, emitted from its tree after the functions it calls. -/
  partial def functionOf (inst : InstanceId) : EmitM Nat := do
    if let some index := (← get).functionIndex[inst]? then return index
    let code ← match (← read).results.body? inst with
      | some (.done code) => pure code
      | some (.waiting reason) => throw (.waiting reason)
      | _ => defect s!"the function instance {inst} has no body"
    if let some reason := code.waiting then throw (.waiting reason)
    let inputs ← code.inputs.toList.mapM toTy
    let outputs ← code.outputs.toList.mapM toTy
    -- a function bound to the formal library is a header
    let body ← match code.external with
      | some _ => pure none
      | none =>
        match (← read).results.trees.result? inst with
        | some { body := .function tree, .. } => some <$> Named.emitFunction (← bodyContext) tree
        | _ => defect s!"the tree of the function instance {inst} is not kept"
    let name := match code.external with
      | some external => s!"{code.name} = external(\"{external}\")"
      | none => code.name
    let emitter ← get
    let index := emitter.functions.size
    set { emitter with functions := emitter.functions.push
                         { specificationOnly := code.specificationOnly, inputs, outputs, body }
                       functionIndex := emitter.functionIndex.insert inst index
                       names := emitter.names.push name
                       -- a function known by its header can stop: its meaning is the model's
                       stops := emitter.stops.push (code.external.isSome || code.canStop) }
    return index

  /-- The protocol of the named program for a checked protocol body, with the protocols it
  applies emitted before it. -/
  partial def protocolOfChecked (inst : InstanceId) (checked : Typed.Checked) :
      EmitM Zkc.Core.Named.Protocol := do
    let state ← read
    let .protocol body := checked.definition.body
      | defect s!"the protocol instance {inst} has no body"
    let some entry := state.table.entries[inst]? | defect s!"the instance {inst} is not in the table"
    let events := match (state.env.modules.lowered? entry.key.declaration).map (·.content) with
      | some (.protocol head _ _) => head.events
      | _ => #[]
    let loops := match (state.program.declarations[entry.key.declaration]?).map (·.node) with
      | some (.protocol node) => Passes.writtenLoops node.body
      | _ => #[]
    let callee (applied : InstanceId) : EmitM (Nat × Zkc.Core.Named.Protocol) := do
      let number ← protocolOf applied
      let some target := (← get).protocols[number]?
        | defect s!"the protocol instance {applied} is applied before it is emitted"
      return (number, target)
    Named.emitProtocol (← bodyContext)
      { roster := body.roster, roles := checked.roles, occurrences := checked.occurrences, events
        loops, callee } checked.definition.specificationOnly body

  /-- The number of a protocol instance, emitted from its checked tree after the functions and
  protocols it reaches. -/
  partial def protocolOf (inst : InstanceId) : EmitM Nat := do
    if let some index := (← get).protocolIndex[inst]? then return index
    let state ← read
    let some checked := state.results.checked.result? inst
      | match state.results.body? inst with
        | some (.waiting reason) => throw (.waiting reason)
        | _ => throw (.waiting "a protocol whose body is not checked")
    if let some reason := checked.definition.waiting then throw (.waiting reason)
    let protocol ← protocolOfChecked inst checked
    let name := match state.results.body? inst with
      | some (.protocol code) => code.name
      | _ => s!"protocol {inst}"
    let roster := match checked.definition.body with
      | .protocol body => body.roster.toList
      | _ => []
    let emitter ← get
    let index := emitter.protocols.size
    set { emitter with
      protocols := emitter.protocols.push protocol
      protocolIndex := emitter.protocolIndex.insert inst index
      protocolNames := emitter.protocolNames.push name
      protocolRoles := emitter.protocolRoles.push roster }
    return index
end

end Zkc.Frontend.Emit
