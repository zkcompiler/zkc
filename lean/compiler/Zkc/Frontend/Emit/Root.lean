module

public import Zkc.Frontend.Emit.Definitions
public import Zkc.Core.Evidence.ProtocolReadback

@[expose] public section
set_option autoImplicit false
namespace Zkc.Frontend.Emit

open Zkc.Vocabulary.Project
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
  | some (.exhausted exhaustion) => throw (.exhausted exhaustion)
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

/-- The definitions that roots reach, in one package: what the first root reaches in the order
of its own package, then what each later root adds. A definition that two roots reach is there
once, and the bindings are those that any of them links. -/
def emitReachableFrom (roots : List InstanceId) : EmitM RootEmission := do
  let found ← roots.foldlM (fun found root => visit root [] found) {}
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

def emitReachable (root : InstanceId) : EmitM RootEmission := emitReachableFrom [root]

/-- Physical block paths from one typed definition. The source records static iteration
numbers and an instruction key. Two candidates at that coordinate make resolution fail. -/
structure SiteAddresses where
  paths : Std.HashMap (List Nat × Nat) (Option (List (Core.Key × Nat))) := {}

def SiteAddresses.ofAddresses (addresses : List (List (Core.Key × Nat) × Core.Key)) : SiteAddresses := Id.run do
  let mut found : SiteAddresses := {}
  for (blocks, key) in addresses do
    let coordinate := (blocks.map Prod.snd, key.number)
    found := ⟨found.paths.insert coordinate (if found.paths.contains coordinate then none else some blocks)⟩
  return found

def SiteAddresses.forProtocol {V : Core.Vocabulary} (p : Core.Typed V) (key : Core.Key) : Option SiteAddresses := do
  let ⟨_, member⟩ ← p.findProtocol key
  let entry := p.defs.protocolEntry p.distinct member
  return ofAddresses (entry.body.addresses [])

def SiteAddresses.resolve (index : SiteAddresses) (entry : Typing.SiteEntry) :
    Option (List (Core.Key × Nat) × Core.Key) := do
  let key ← entry.instruction
  let blocks ← (index.paths[(entry.iteration.toList, key)]?).join
  return (blocks, ⟨key⟩)

end Zkc.Frontend.Emit

namespace Zkc.Frontend.Typing

def emitRoot (state : Compile.State) (root : InstanceId) : Except EmitFailure Emit.RootEmission :=
  (Emit.emitReachable root).run state

/-- The package of several roots of one state (`Emit.emitReachableFrom`). -/
def emitRoots (state : Compile.State) (roots : List InstanceId) :
    Except EmitFailure Emit.RootEmission :=
  (Emit.emitReachableFrom roots).run state

end Zkc.Frontend.Typing
