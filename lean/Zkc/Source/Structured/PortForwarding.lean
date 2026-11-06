module

public import Zkc.Source.Structured.ComponentDeclarations
public import Zkc.Source.ContextOperations

@[expose] public section

/-! Derive a typed return tuple from a companion's correspondence on named
source fields. Layout, receiver versus holder leaves, and role scopes come
from the same declaration traversal used at admission. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.PortForwarding
open SourceDeclarations

inductive Origin where
  | input (path : List String)
  | parameter (index : Nat)

inductive Term (inputs parameters : List Ty) (type : Ty) where
  | input (ref : Var inputs type)
  | parameter (ref : Var parameters type)

abbrev Plan (inputs parameters outputs : List Ty) := Values (Term inputs parameters) outputs

def Plan.apply {V : Ty → Type} {inputs parameters outputs : List Ty}
    (plan : Plan inputs parameters outputs) (arguments : Values V inputs) (supplied : Values V parameters) :
    Values V outputs :=
  Environment.toValues (fun ref ↦ match plan.get ref with
    | .input ref => arguments.get ref
    | .parameter ref => supplied.get ref)

def portLeaves (source : SourceDeclarations) (signature : ProtocolSignature) (ports : List SourcePort) :
    Option (List PlacedLeaf) := do
  let rows ← ports.mapM fun port ↦ (source.placedLeaves signature.roles port).toOption
  return rows.flatten

/-- Resolve one named output from its checked declaration, retaining the
distinction between the holder's private data and the receiver's handle. -/
def outputField (source : SourceDeclarations) (signature : ProtocolSignature) (path : List String)
    (kind : LeafKind) (type : Ty) : Option (Var signature.outputs type) := do
  let [declaration] := source.protocols.filter (·.name == signature.name) | none
  let _ ← (source.checkPorts signature declaration.outputs signature.outputs signature.outputScopes false).toOption
  let [(_, index)] := (← portLeaves source signature declaration.outputs).zipIdx.filter
    (fun entry ↦ entry.1.leaf.path == path && entry.1.leaf.kind == kind) | none
  Var.decode signature.outputs type index

def resolve {inputs parameters : List Ty} (available : List PlacedLeaf)
    (type : Ty) (leaf : PlacedLeaf) : Origin → Option (Term inputs parameters type)
  | .input path => do
    let [(_, index)] := available.zipIdx.filter (fun entry ↦ entry.1.leaf.path == path &&
      entry.1.leaf.kind == leaf.leaf.kind && entry.1.roles == leaf.roles) | none
    return .input (← Var.decode inputs type index)
  | .parameter index => do
    guard (leaf.leaf.kind == .data type)
    return .parameter (← Var.decode parameters type index)

def collect {inputs parameters : List Ty} (available : List PlacedLeaf)
    (origin : List String → Option Origin) :
    (outputs : List Ty) → List PlacedLeaf → Option (Plan inputs parameters outputs)
  | [], [] => some .nil
  | type :: rest, leaf :: tail => do
    let term ← resolve available type leaf (← origin leaf.leaf.path)
    return .cons term (← collect available origin rest tail)
  | _, _ => none

/-- Every output coordinate must resolve. Forwarding requires a unique
input of the same leaf kind, type and placement. Explicit parameters have
their own typed telescope. Hidden service arguments are never named. -/
def compile (source : SourceDeclarations) (signature : ProtocolSignature) (parameters : List Ty)
    (origin : List String → Option Origin) :
    Option (Plan signature.inputs parameters signature.outputs) := do
  let [declaration] := source.protocols.filter (·.name == signature.name) | none
  let _ ← (source.checkPorts signature declaration.inputs signature.inputs signature.inputScopes true).toOption
  let _ ← (source.checkPorts signature declaration.outputs signature.outputs signature.outputScopes false).toOption
  collect (← portLeaves source signature declaration.inputs) origin signature.outputs
    (← portLeaves source signature declaration.outputs)

end Zkc.Source.Structured.PortForwarding
