module

public import Zkc.Core.Program.NamedProgram
public import Zkc.Frontend.Emit.Bindings
public import Zkc.Frontend.Static.Types

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Typing

open Zkc.Vocabulary.Project

open Static Emit

inductive EmitFailure where
  | waiting (reason : WaitReason)
  | defect (message : String)
  | noCoreForm (reason : String)
  deriving Inhabited, Repr

abbrev EmitM := ReaderT Compile.State (Except EmitFailure)

def defect {α : Type} (message : String) : EmitM α := throw (.defect message)

/-- Resolve each aggregate against its actual source declaration. A recursive aggregate
would have an infinite Core type. Only the current expansion path counts as a cycle. -/
partial def toTy (type : ClosedType) (active : List InstanceId := []) : EmitM LinkedType := do
  let fields (ts : Array ClosedType) (path : List InstanceId) := do
    return (← ts.toList.mapM fun t => toTy t path).foldr Core.Tys.cons .nil
  match type with
  | .bool => return .bool
  | .nat => return .nat
  | .index n => return .fin n
  | .seq item n => return .seq (← toTy item active) n
  | .tuple items _ => return .tuple (← fields items active)
  | .record i | .variant i =>
    if active.contains i then throw (.noCoreForm s!"recursive aggregate at instance {i}")
    match type, (← read).table.content? i with
    | .record _, some (.record linear members) =>
      return .record ⟨i⟩ linear (← fields (members.map (·.2)) (i :: active))
    | .variant _, some (.variant variants) =>
      return .variant ⟨i⟩ (← fields (variants.map fun (_, ts) => payloadType ts) (i :: active))
    | _, _ => defect s!"missing aggregate declaration for instance {i}"
  | .nonzero _ | .nominal .. =>
    if let some t := StandardNames.typeOf? type then return t.mapNominal Sum.inl
    return .nominal (.inr (parameterOfType type))
  | .rational | .specification _ => throw (.noCoreForm "specification type in executable code")
  | .opaque .. => throw (.waiting "an unresolved module member in executable code")

def primitiveSignature (row : Row) : EmitM PrimitiveSignature := do
  return ⟨← row.inputs.toList.mapM (toTy ·), ← row.outputs.toList.mapM (toTy ·)⟩

/-- Check the declared source ABI before choosing the owner of an executable row. -/
def standardKey? (row : Row) : EmitM (Option Zkc.Vocabulary.RowKey) := do
  let request : RowRequest := ⟨row.key.name, row.key.statics⟩
  if let some expected := rowOf? request then
    unless sameRowSignature row expected do defect s!"conflicting signature of {request.name}"
    if let some key := StandardRow.resolve request then
      if (Zkc.Vocabulary.row key).isSome then return some key
  else if reservedRow request.name then
    defect s!"invalid static arguments of {request.name}"
  match row.kind with
  | .pure => return none
  | .sampling => throw (.noCoreForm s!"sampling law {request.name} in local code")
  | .restricted _ => throw (.noCoreForm s!"unresolved domain of {request.name}")

def linkRow (b : Bindings) (row : Row) : EmitM Bindings := do
  if (← standardKey? row).isSome then return b
  match b.insert (primitiveName row.key) (← primitiveSignature row) with
  | .ok next => return next
  | .error k => defect s!"conflicting primitive declarations for {k.name}"

def rowKey (b : Bindings) (row : Row) : EmitM b.vocabulary.RowKey := do
  if let some k ← standardKey? row then return .inl k
  let key := primitiveName row.key
  unless b.signature key = some (← primitiveSignature row) do
    defect s!"missing or incompatible primitive binding for {key.name}"
  return .inr key

end Zkc.Frontend.Typing
