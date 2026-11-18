module

public import Zkc.Frontend.Emit.Definitions

@[expose] public section
set_option autoImplicit false
namespace Zkc.Frontend.Emit
open Static
open Typing (EmitM EmitFailure)

inductive ReachableBody where
  | fn (body : Typed.FunctionBody) (result : ClosedType)
  | protocol (body : Typed.ProtocolBody) (roles : Typed.Roles)
  deriving Inhabited

structure Reachable where
  bindings : Bindings := {}
  bodies : Array (InstanceId × ReachableBody) := #[]
  visited : Std.HashSet InstanceId := {}

/-- The root currently undergoing its per-definition check already has a numbered
protocol tree. A waiting dependency cannot enter an executable package. -/
def runtimeBody (inst : InstanceId) : EmitM ReachableBody := do
  let results := (← read).results
  match results.body? inst with
  | some (.waiting reason) => throw (.waiting reason)
  | some (.exhausted e) => throw (.waiting e.describe)
  | some .failed => throw (.waiting s!"rejected source instance {inst}")
  | some (.done fn) =>
    if let some why := fn.waiting then throw (.waiting why)
    if fn.external.isSome then throw (.noCoreForm s!"external function {fn.name}")
    let some tree := results.trees.result? inst | Typing.defect s!"missing function tree {inst}"
    let .function body := tree.body | Typing.defect s!"expected function {inst}"
    let #[result] := fn.outputs | Typing.defect s!"function {inst} needs one result"
    return .fn body result
  | bodyState =>
    if let some (.protocol code) := bodyState then
      if let some why := code.waiting then throw (.waiting why)
    let some checked := results.checked? inst | throw (.waiting s!"no checked protocol {inst}")
    let .protocol body := checked.definition.body | Typing.defect s!"expected protocol {inst}"
    return .protocol body checked.roles

partial def visit (inst : InstanceId) (active : List InstanceId) (found : Reachable) : EmitM Reachable := do
  if found.visited.contains inst then return found
  if active.contains inst then Typing.defect s!"cyclic dependency of instance {inst}"
  let source ← runtimeBody inst
  let (calls, protocols) := match source with
    | .fn fn _ => (calledIn fn, #[])
    | .protocol body _ => (protocolFunctions body, appliedIn #[] body.statements)
  let bindings ← bindCalls found.bindings calls
  let mut next := {found with bindings}
  let results := (← read).results
  for callee in calls do
    if let some (.row _) := results.body? callee then continue
    next ← visit callee (inst :: active) next
  for callee in protocols do next ← visit callee (inst :: active) next
  return { next with bodies := next.bodies.push (inst, source), visited := next.visited.insert inst }

structure DefinitionOrigin where
  definition : Core.Key
  nodes : Array Typed.NodeId
  specification : Array Named.ApplicationArguments
  dynamicLoops : Array (Core.Key × List Core.Role)

/-- The emitted definitions and their source-level attachments share the concrete keys.
Admission is given its explicit specification association by the consumer. -/
structure RootEmission where
  bindings : Bindings
  named : Core.NamedProgram bindings.vocabulary
  origins : Array DefinitionOrigin

def RootEmission.package (e : RootEmission) (association : Core.Association) : SourcePackage :=
  ⟨e.bindings,e.named,association⟩

def emitReachable (root : InstanceId) : EmitM RootEmission := do
  let found ← visit root [] {}
  let context ← bodyContext found.bindings
  let mut definitions := #[]
  let mut origins := #[]
  for (inst, source) in found.bodies do
    let key : Core.Key := ⟨inst⟩
    let (definition, nodes, specification, dynamicLoops) ← match source with
      | .fn body out => do
        let (definition, nodes) ← Named.functionDefinition context key out body
        pure (definition, nodes, #[], #[])
      | .protocol body roles => do
        let result ← Named.emitProtocol context ⟨roles,body.roster⟩ key body
        pure (result.definition, result.sourceNodes, result.specification, result.dynamicLoops)
    definitions := definitions.push definition
    origins := origins.push ⟨key,nodes,specification,dynamicLoops⟩
  return ⟨found.bindings,⟨definitions.toList⟩,origins⟩

end Zkc.Frontend.Emit

namespace Zkc.Frontend.Typing

def emitRoot (state : Compile.State) (root : InstanceId) : Except EmitFailure Emit.RootEmission :=
  (Emit.emitReachable root).run state

end Zkc.Frontend.Typing
