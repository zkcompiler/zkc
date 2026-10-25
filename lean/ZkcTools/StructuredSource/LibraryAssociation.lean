module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Template lookup for installed source libraries. These records are selection
data, never body certificates. Exact body equations must be checked separately.
An association has no site or dynamic coordinates: occurrences belong to calls. -/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.LibraryAssociation
open Zkc.Source Zkc.Source.Structured

structure Template where
  path : String
  parameters : List String

structure Installed (α : Type) where
  template : Template
  instantiate : List (String × OriginTerm) → Except String α

structure Association (α : Type) where
  index : Nat
  signature : ProtocolSignature
  origin : ProtocolOrigin
  selected : α
  /-- Indices in the earlier admitted prefix, retaining repeated call edges. -/
  callees : List Nat

/-- Parameter order and names are part of the installed template contract.
Typed values are passed intact to its decoder; no display type is an identity. -/
def select {α : Type} (installed : List (Installed α)) (origin : ProtocolOrigin) :
    Except String α := do
  unless origin.valid do throw "library-origin-malformed"
  let candidates := installed.filter (fun entry => entry.template.path == origin.path)
  let entry ← match candidates with
    | [] => throw "library-template-missing"
    | [entry] => pure entry
    | _ => throw "library-template-ambiguous"
  unless origin.arguments.map Prod.fst == entry.template.parameters do
    throw "library-static-parameters"
  entry.instantiate origin.arguments

/-- Join the actual admitted definition to its retained raw metadata. The
caller supplies an admitted program; generated proofs retain its Imported link. -/
def originFor (snapshot : Snapshot) (definition : CheckedProtocol) : Except String ProtocolOrigin := do
  let candidates := snapshot.definitions.filterMap fun
    | .function function => if function.name == definition.name then some function else none
    | _ => none
  let function ← match candidates with
    | [] => throw "library-origin-missing"
    | [function] => pure function
    | _ => throw "library-origin-ambiguous"
  let origin ← match function.origin with
    | none => throw "library-origin-missing"
    | some (.protocol origin) => pure origin
    | _ => throw "library-origin-malformed"
  unless function.kind == .protocol && (Definition.function function).headerValid do
    throw "library-origin-malformed"
  unless (snapshot.protocolFunctions.filter (fun function =>
      function.origin == some (.protocol origin))).length == 1 do
    throw "library-origin-ambiguous"
  return origin

/-- Full nominal signatures resolve only against already associated callees.
Matching origins cannot repair a changed signature or a forward reference. -/
def calleeIndex {α : Type} (associated : List (Association α)) (signature : ProtocolSignature) :
    Except String Nat := do
  let [entry] := associated.filter (fun entry => entry.signature == signature)
    | throw "library-callee-association"
  return entry.index

/-- Process the actual admitted dependency order, not raw declaration order.
Each candidate is selected only after every callee has an earlier association.
The resulting data still grants no right to replace any body. -/
def bottomUp {α : Type} (snapshot : Snapshot) (installed : List (Installed α))
    (definitions : List CheckedProtocol) : Except String (List (Association α)) := do
  let mut associated := []
  for (definition, index) in definitions.zipIdx do
    let origin ← originFor snapshot definition
    if associated.any (fun entry => entry.origin == origin) then
      throw "library-origin-ambiguous"
    let callees ← definition.protocols.mapM (calleeIndex associated)
    let selected ← select installed origin
    associated := associated ++ [⟨index, definition.signature, origin, selected, callees⟩]
  return associated

end ZkcTools.StructuredSource.LibraryAssociation
