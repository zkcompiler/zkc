module

public import Zkc.Realization.RecordAllocator

@[expose] public section

/-! The immutable record append used by query continuation arenas. The checked
length is obtained before insertion and is the new record's exact slot. This
physical rule neither selects a parent query nor interprets a saved answer. -/
set_option autoImplicit false
namespace Zkc.Realization.RecordAppend
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Layout where
  identity : String
  fields : ProductFields

def Layout.type (layout : Layout) : Ty := .product layout.identity "Record" layout.fields

structure Placement where
  start : Nat
  store : Nat
  fields : List Nat

def instructions (layout : Layout) (placement : Placement) : List Construction.Instruction :=
  [⟨.execute (.sequenceLength layout.type), [placement.store], [.data .index], []⟩,
   ⟨.calculate (.makeProduct layout.identity "Record" layout.fields), placement.fields,
     [.data layout.type], []⟩,
   ⟨.execute (.sequenceAppend layout.type), [placement.store, placement.start + 1],
     [.data (.sequence layout.type)], []⟩]

structure Recognized (body : List Construction.Instruction) where
  layout : Layout
  placement : Placement
  exactBody : body = instructions layout placement

def recognizeAt (start : Nat) (body : List Construction.Instruction) : Option (Recognized body) := do
  let [length, record, _] := body | none
  let [store] := length.operands | none
  let .calculate (.makeProduct identity "Record" fields) := record.operation | none
  let layout : Layout := ⟨identity, fields⟩
  let placement : Placement := ⟨start, store, record.operands⟩
  if matched : body = instructions layout placement then some ⟨layout, placement, matched⟩ else none

def spine (layout : Layout) (placement : Placement) : ConnectionTargetPrefix.Prefix :=
  .step (fun model ↦ Domain.View.execute model (.sequenceLength layout.type) [placement.store] [.data .index])
  (.step (fun model ↦ Domain.View.calculation model (.makeProduct layout.identity "Record" layout.fields)
    placement.fields [.data layout.type])
  (.step (fun model ↦ Domain.View.execute model (.sequenceAppend layout.type)
    [placement.store, placement.start + 1] [.data (.sequence layout.type)]) .empty))

theorem correspondence (model : DomainModel) (program : Program) (context : Context)
    (layout : Layout) (placement : Placement) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (instructions layout placement) ((spine layout placement).block model) :=
  Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
    (Domain.Correspondence.sequence (Domain.Correspondence.calculation _ _ _)
      (Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
        Domain.Correspondence.empty))

theorem Recognized.correspondence {body : List Construction.Instruction}
    (checked : Recognized body) (model : DomainModel) (program : Program) (context : Context) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      body ((spine checked.layout checked.placement).block model) := by
  rcases checked with ⟨layout, placement, rfl⟩
  exact RecordAppend.correspondence model program context layout placement

def result (model : DomainModel) (layout : Layout) (data : layout.type.isHandle = false)
    (environment : Domain.Environment model.toCarriers) (records : List (model.Value layout.type))
    (record : model.Value layout.type) : Domain.Environment model.toCarriers :=
  environment ++ [.data (.index records.length), .data ⟨layout.type, data, record⟩,
    .data ⟨.sequence layout.type, data, records ++ [record]⟩]

set_option backward.isDefEq.respectTransparency false in
/-- No premise about record contents or a protocol-specific formula is needed.
The bounded length justifies the checked machine-index result. -/
noncomputable def simulation (model : DomainModel) (layout : Layout)
    (data : layout.type.isHandle = false)
    (fieldData : layout.fields.toList.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers) (store : Nat) (fields : List Nat)
    (records : List (model.Value layout.type)) (record : model.Value layout.type)
    (readStore : environment[store]? = some (.data ⟨.sequence layout.type, data, records⟩))
    (readFields : Domain.read environment fields = Domain.encodeValues (layout.fields.unpack record))
    (bounded : records.length < indexLimit) :
    Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (result model layout data environment records record))
      ((spine layout ⟨environment.length, store, fields⟩).block model environment) := by
  let length : Domain.Value model.toCarriers := .data (.index records.length)
  let packed : Domain.Value model.toCarriers := .data ⟨layout.type, data, record⟩
  let extended : Domain.Value model.toCarriers := .data ⟨.sequence layout.type, data, records ++ [record]⟩
  have fieldsPlain : layout.fields.hasHandle = false := data
  have recordLocal : Domain.localType layout.type = true := by simp [Domain.localType, Domain.dataType, data]
  have sequenceLocal : Domain.localType (.sequence layout.type) = true := by
    simp [Domain.localType, Domain.dataType, Ty.isHandle, Ty.isCustody, data]
  have lengthRead : Domain.read environment [store] =
      Domain.encodeValues (tys := [.sequence layout.type]) (.cons records .nil) := by
    simp [Domain.read, readStore, Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, data]
  have lengthStep : Domain.View.execute model (.sequenceLength layout.type) [store] [.data .index]
      environment = .done (environment ++ [length]) := by
    have law := ConnectionPrimitives.view_execute model (.sequenceLength layout.type) (.cons records .nil)
      (by simpa [Primitive.arguments] using sequenceLocal) rfl _ _ lengthRead
    simpa [Primitive.results, Primitive.evaluateOn, bounded, primitiveOutcome, length, Original.encodeHelperResult,
      Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue,
      Ty.isHandle, PIR.Process.bind] using law
  have fieldsRead : Domain.read (environment ++ [length]) fields =
      Domain.encodeValues (layout.fields.unpack record) := by
    rw [Original.encodeHelperResult_eq fieldData] at readFields ⊢
    exact RecordAllocator.read_extended environment [length] fields _ readFields
  have packStep : Domain.View.calculation model (.makeProduct layout.identity "Record" layout.fields)
      fields [.data layout.type] (environment ++ [length]) = .done (environment ++ [length, packed]) := by
    have law := ConnectionCalculations.view_calculation model (.makeProduct layout.identity "Record" layout.fields)
      (layout.fields.unpack record) fieldData (by simpa [Calculation.op, Op.results, Layout.type] using recordLocal) _ _ fieldsRead
    simpa [ConnectionCalculations.closedCalculation, ConnectionCalculations.calculationRegions,
      Calculation.op, Op.results, Evaluation.operationOn, ProductFields.pack_unpack, PIR.Process.interpret, closedLift,
      PIR.Process.bind, Original.encodeHelperResult, Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
      Domain.Payload.ofValue, Ty.isHandle, fieldsPlain, packed, Layout.type, List.append_assoc] using law
  have appendRead : Domain.read (environment ++ [length, packed]) [store, environment.length + 1] =
      Domain.encodeValues (tys := [.sequence layout.type, layout.type]) (.cons records (.cons record .nil)) := by
    have selected := Domain.View.read_cons (environment ++ [length, packed]) store
      [environment.length + 1] (.data ⟨.sequence layout.type, data, records⟩) [packed]
      (Original.read_append readStore [length, packed])
      (Domain.View.read_cons _ _ [] packed [] (by simp) rfl)
    rw [selected]
    simp [Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
      Domain.Payload.ofValue, Ty.isHandle, fieldsPlain, packed, Layout.type]
  have appendStep : Domain.View.execute model (.sequenceAppend layout.type) [store, environment.length + 1]
      [.data (.sequence layout.type)] (environment ++ [length, packed]) =
        .done (environment ++ [length, packed, extended]) := by
    have law := ConnectionPrimitives.view_execute model (.sequenceAppend layout.type) (.cons records (.cons record .nil))
      (by simp [Primitive.arguments, sequenceLocal, recordLocal])
      (by simpa [Primitive.results] using sequenceLocal) _ _ appendRead
    simpa [Primitive.results, Primitive.evaluateOn, primitiveOutcome, Original.encodeHelperResult,
      Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue,
      Ty.isHandle, data, PIR.Process.bind, List.append_assoc, extended] using law
  apply RecordAllocator.silent_sequence lengthStep (List.prefix_refl _) (by simp)
  apply RecordAllocator.silent_sequence packStep (by simp) (by simp)
  apply RecordAllocator.silent_sequence appendStep (by simp) (by simp)
  exact .done rfl

/-- Capacity failure occurs before packing or appending. The existing frame
and the checkpoint before the checked length operation are retained. -/
noncomputable def exhausted (model : DomainModel) (layout : Layout)
    (placement : Placement) (data : layout.type.isHandle = false)
    (environment : Domain.Environment model.toCarriers) (records : List (model.Value layout.type))
    (readStore : environment[placement.store]? =
      some (.data ⟨.sequence layout.type, data, records⟩))
    (full : ¬ records.length < indexLimit) :
    Original.Simulation (Eq (α := Domain.Environment model.toCarriers))
      (fun _ frame ↦ environment <+: frame) (.halt .exhausted)
      ((spine layout placement).block model environment) := by
  have sequenceLocal : Domain.localType (.sequence layout.type) = true := by
    simp [Domain.localType, Domain.dataType, Ty.isHandle, Ty.isCustody, data]
  have read : Domain.read environment [placement.store] =
      Domain.encodeValues (tys := [.sequence layout.type]) (.cons records .nil) := by
    simp [Domain.read, readStore, Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, data]
  have stopped : Domain.View.execute model (.sequenceLength layout.type) [placement.store] [.data .index]
      environment = .halt .exhausted := by
    have law := ConnectionPrimitives.view_execute model (.sequenceLength layout.type) (.cons records .nil)
      (by simpa [Primitive.arguments] using sequenceLocal) rfl _ _ read
    simpa [Primitive.results, Primitive.evaluateOn, full, primitiveOutcome, PIR.Process.bind] using law
  change Original.Simulation _ _ _ (Domain.View.sequence _ _ environment)
  rw [Domain.View.sequence_stop _ _ _ .exhausted stopped]
  exact .checkpoint environment (List.prefix_refl _) (.halt .exhausted)

/-- The same rule applies to the exact body recognized in a checked program.
The caller supplies the reached operands, never a substituted record. -/
noncomputable def Recognized.simulation {body : List Construction.Instruction}
    (checked : Recognized body) (model : DomainModel) (program : Program) (context : Context)
    (data : checked.layout.type.isHandle = false)
    (fieldData : checked.layout.fields.toList.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers)
    (records : List (model.Value checked.layout.type))
    (record : model.Value checked.layout.type)
    (start : checked.placement.start = environment.length)
    (readStore : environment[checked.placement.store]? =
      some (.data ⟨.sequence checked.layout.type, data, records⟩))
    (readFields : Domain.read environment checked.placement.fields =
      Domain.encodeValues (checked.layout.fields.unpack record))
    (lengthBound : records.length < indexLimit) :
    Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (result model checked.layout data environment records record))
      (Domain.evaluate model program context body environment) := by
  rw [checked.correspondence model program context]
  rcases checked with ⟨layout, ⟨position, store, fields⟩, matched⟩
  dsimp only at start ⊢
  subst position
  exact RecordAppend.simulation model layout data fieldData environment store fields records
    record readStore readFields lengthBound

end Zkc.Realization.RecordAppend
