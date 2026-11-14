module

public import Zkc.Core.Elaborate
public import Zkc.Core.Lower
public import Zkc.Core.Admission
public import Zkc.Frontend.Static.Types
public import Zkc.Frontend.Semantics.Rows

@[expose] public section

set_option autoImplicit false

/-!
# The tables of a package under emission

A package is emitted per root: the function and protocol instances the root reaches, with the
records, variants, nominal types and rows they reach. Types, records, variants and rows are
numbered in the order of first reach. The types of the vocabulary and `nonzero<F>` are nominal
rows: the row of a type of the vocabulary is named as the vocabulary names it, at its static
arguments; the row of `nonzero<F>` is `nonzero` at the type `F`. A `linear struct` is used
exactly once; any other record is copied freely.
-/

namespace Zkc.Frontend.Typing

open Static

/-- Why a package is not emitted. -/
inductive EmitFailure where
  /-- A form not typed yet. -/
  | waiting (reason : String)
  /-- A defect of the frontend. -/
  | defect (message : String)
  /-- A specification item whose types or operations have no form in the core: it is typed
  only. -/
  | noCoreForm (reason : String)
  deriving Inhabited

structure Emitter where
  types : Array Zkc.Core.CatalogueRow := #[]
  typeIndex : Std.HashMap ClosedType Nat := {}
  records : Array Zkc.Core.RecordDeclaration := #[]
  recordIndex : Std.HashMap InstanceId Nat := {}
  variants : Array Zkc.Core.VariantDeclaration := #[]
  variantIndex : Std.HashMap InstanceId Nat := {}
  operations : Array Zkc.Core.Operation := #[]
  rowIndex : Std.HashMap RowKey Nat := {}
  functions : Array Zkc.Core.Named.Function := #[]
  functionIndex : Std.HashMap InstanceId Nat := {}
  names : Array String := #[]
  /-- Whether each function can stop (FN2), in the order of the functions. -/
  stops : Array Bool := #[]
  protocols : Array Zkc.Core.Named.Protocol := #[]
  protocolIndex : Std.HashMap InstanceId Nat := {}
  protocolNames : Array String := #[]
  protocolRoles : Array (List String) := #[]
  /-- The emission is for the check of a definition and not for a package: a type without a
  form in the core is a nominal row of its name, so that a body over it can be checked. -/
  checking : Bool := false
  deriving Inhabited

abbrev EmitM := ReaderT Compile.State (StateT Emitter (Except EmitFailure))

def defect {α : Type} (message : String) : EmitM α := throw (.defect message)

mutual
  /-- The type of the core of a closed type. -/
  partial def toTy (type : ClosedType) : EmitM Zkc.Core.Ty := do
    match type with
    | .bool => return .bool
    | .nat => return .nat
    | .index bound => return .fin bound
    | .seq element size => return .seq (← toTy element) size
    | .tuple components _ => return .tuple (← components.toList.mapM toTy)
    | .nominal row arguments =>
      let mut statics := #[]
      for argument in arguments do
        match argument with
        | .natural value => statics := statics.push (Zkc.Core.Static.nat value)
        | .type inner => statics := statics.push (.type (← toTy inner))
        | .«module» inst =>
          -- a package has no form for a module argument yet (a later layer); in the check of
          -- a definition the instance stands for it, so that the body is checked
          unless (← get).checking do
            throw (.waiting "a type of the vocabulary at a module argument")
          statics := statics.push (Zkc.Core.Static.nat inst)
      return .nominal (← nominalRow type row statics)
    | .nonzero field =>
      let inner ← toTy field
      return .nominal (← nominalRow type "nonzero" #[.type inner])
    | .record inst => return .record (← recordNumber inst) .free []
    | .«variant» inst => return .variant (← variantNumber inst) []
    | .rational =>
      unless (← get).checking do throw (.noCoreForm "`rational` has no form in the core")
      return .nominal (← nominalRow type "rational" #[])
    | .specification inst =>
      unless (← get).checking do throw (.noCoreForm "a `spec type` has no form in the core")
      return .nominal (← nominalRow type "specification" #[.nat inst])
    | .«opaque» «module» member _ _ =>
      unless (← get).checking do throw (.waiting "an opaque type member (SP12)")
      return .nominal (← nominalRow type s!"opaque.{member}" #[.nat «module»])

  /-- The number of a nominal row, entered after the rows its static arguments name. -/
  partial def nominalRow (key : ClosedType) (name : String) (statics : Array Zkc.Core.Static) :
      EmitM Nat := do
    if let some index := (← get).typeIndex[key]? then return index
    let emitter ← get
    let index := emitter.types.size
    set { emitter with types := emitter.types.push { name := Zkc.Core.Name.ofString name, statics := statics.toList }
                       typeIndex := emitter.typeIndex.insert key index }
    return index

  partial def recordNumber (inst : InstanceId) : EmitM Nat := do
    if let some index := (← get).recordIndex[inst]? then return index
    let some (.record linear fields) := (← read).table.content? inst
      | defect s!"the record instance {inst} has no fields"
    let index := (← get).records.size
    modify fun emitter => { emitter with records := emitter.records.push default
                                         recordIndex := emitter.recordIndex.insert inst index }
    let types ← fields.toList.mapM fun (_, type) => toTy type
    let use := if linear then Zkc.Core.Use.exactlyOnce else .free
    modify fun emitter => { emitter with records := emitter.records.set! index { use, fields := types } }
    return index

  partial def variantNumber (inst : InstanceId) : EmitM Nat := do
    if let some index := (← get).variantIndex[inst]? then return index
    let some (.«variant» alternatives) := (← read).table.content? inst
      | defect s!"the variant instance {inst} has no alternatives"
    let index := (← get).variants.size
    modify fun emitter => { emitter with variants := emitter.variants.push default
                                         variantIndex := emitter.variantIndex.insert inst index }
    let types ← alternatives.toList.mapM fun (_, payload) => toTy (payloadType payload)
    modify fun emitter => { emitter with variants := emitter.variants.set! index { alternatives := types } }
    return index

  partial def rowNumber (row : RowId) : EmitM Nat := do
    let some entry := (← read).results.rows[row]? | defect s!"the row {row} is not in the table"
    rowNumberOf entry

  /-- The number of a row, entered after the rows its types and its domain row need. -/
  partial def rowNumberOf (entry : Row) : EmitM Nat := do
    if let some index := (← get).rowIndex[entry.key]? then return index
    let mut statics := #[]
    for static in entry.key.statics do
      match static with
      | .nat value => statics := statics.push (Zkc.Core.Static.nat value)
      | .type type => statics := statics.push (.type (← toTy type))
    let inputs ← entry.inputs.toList.mapM toTy
    let outputs ← entry.outputs.toList.mapM toTy
    let kind : Zkc.Core.OperationKind ← match entry.kind with
      | .pure => pure .pure
      | .sampling => pure .sampling
      | .restricted none => pure (.restricted none)
      | .restricted (some domain) =>
        -- the domain row: pure, with the same inputs and one `bool`, earlier in the table
        let domainRow : Row := match rowOf? { name := domain.name, statics := domain.statics } with
          | some found => found
          | none => { key := domain, kind := .pure, inputs := entry.inputs, outputs := #[.bool] }
        pure (.restricted (some (← rowNumberOf domainRow)))
    let operation : Zkc.Core.Operation :=
      { identity := { name := Zkc.Core.Name.ofString entry.key.name, statics := statics.toList }
        signature := { inputs, outputs, kind } }
    let emitter ← get
    let index := emitter.operations.size
    set { emitter with operations := emitter.operations.push operation
                       rowIndex := emitter.rowIndex.insert entry.key index }
    return index
end

/-- The named package of what an emission reached, with the declarations carrying their
shapes. -/
def Emitter.named (emitter : Emitter) : Except EmitFailure Zkc.Core.Named.Package := do
  let (records, variants) ← match Zkc.Core.Raw.declaredTables emitter.records.toList emitter.variants.toList with
    | .ok tables => pure tables
    | .error message => throw (.defect message)
  return { types := emitter.types.toList, records, variants, operations := emitter.operations.toList
           functions := emitter.functions.toList, protocols := emitter.protocols.toList
           functionNames := emitter.names.toList, protocolNames := emitter.protocolNames.toList
           roleNames := emitter.protocolRoles.toList }

end Zkc.Frontend.Typing
