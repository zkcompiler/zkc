module

public import Zkc.Construction.ConnectionPrimitives
public import Zkc.Construction.ConnectionTargetPrefix
public import Zkc.Construction.ConnectionTranscript

@[expose] public section

/-! The existing five-instruction immutable record allocator, at arbitrary SSA
positions. The record fields may contain base data or virtual-view parameters.
Its proof retains every checkpoint and all intermediate cells. Source-anchor
meaning and actual candidate placement are separate from this physical rule. -/

set_option autoImplicit false
namespace Zkc.Realization.RecordAllocator
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Layout where
  constructor : Nat
  recordIdentity : String
  referenceIdentity : String
  fields : ProductFields

def Layout.recordType (layout : Layout) : Ty := .product layout.recordIdentity "Record" layout.fields

def referenceFields : ProductFields := .cons .index (.cons .index .nil)

def Layout.referenceType (layout : Layout) : Ty := .product layout.referenceIdentity "Record" referenceFields

/-- All positions belong to the actual flattened target frame. -/
structure Placement where
  start : Nat
  store : Nat
  fields : List Nat

def instructions (layout : Layout) (placement : Placement) : List Construction.Instruction :=
  [⟨.execute (.indexConstant layout.constructor), [], [.data .index], []⟩,
   ⟨.execute (.sequenceLength layout.recordType), [placement.store], [.data .index], []⟩,
   ⟨.calculate (.makeProduct layout.recordIdentity "Record" layout.fields), placement.fields,
     [.data layout.recordType], []⟩,
   ⟨.execute (.sequenceAppend layout.recordType), [placement.store, placement.start + 2],
     [.data (.sequence layout.recordType)], []⟩,
   ⟨.calculate (.makeProduct layout.referenceIdentity "Record" referenceFields), [placement.start, placement.start + 1],
     [.data layout.referenceType], []⟩]

/-- Placement is extracted from the instructions, and checked against all five
operations. A nominal name or a matching operand type alone is not authority. -/
structure Recognized (body : List Construction.Instruction) where
  layout : Layout
  placement : Placement
  exactBody : body = instructions layout placement

/-- Recognition returns evidence about the original fragment. In particular it
checks result sorts, region absence, and the order of the reference fields. -/
def recognize (body : List Construction.Instruction) : Option (Recognized body) := do
  let [tag, length, record, _, reference] := body | none
  let .execute (.indexConstant constructor) := tag.operation | none
  let [store] := length.operands | none
  let .calculate (.makeProduct recordIdentity "Record" fields) := record.operation | none
  let .calculate (.makeProduct referenceIdentity "Record" _) := reference.operation | none
  let [start, _] := reference.operands | none
  let layout : Layout := ⟨constructor, recordIdentity, referenceIdentity, fields⟩
  let placement : Placement := ⟨start, store, record.operands⟩
  if matched : body = instructions layout placement then
    some ⟨layout, placement, matched⟩
  else none

def spine (layout : Layout) (placement : Placement) : ConnectionTargetPrefix.Prefix :=
  .step (fun model ↦ Domain.View.execute model (.indexConstant layout.constructor) [] [.data .index])
  (.step (fun model ↦ Domain.View.execute model (.sequenceLength layout.recordType) [placement.store] [.data .index])
  (.step (fun model ↦ Domain.View.calculation model (.makeProduct layout.recordIdentity "Record" layout.fields)
    placement.fields [.data layout.recordType])
  (.step (fun model ↦ Domain.View.execute model (.sequenceAppend layout.recordType) [placement.store, placement.start + 2]
    [.data (.sequence layout.recordType)])
  (.step (fun model ↦ Domain.View.calculation model (.makeProduct layout.referenceIdentity "Record" referenceFields)
    [placement.start, placement.start + 1] [.data layout.referenceType]) .empty))))

/-- Formation of the view checks the actual instructions, including ordered
operand references, nominal identities and the checked primitive variants. -/
theorem correspondence (model : DomainModel) (program : Program) (context : Context)
    (layout : Layout) (placement : Placement) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (instructions layout placement) ((spine layout placement).block model) :=
  Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
    (Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation _ _ _)
        (Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
          (Domain.Correspondence.sequence (Domain.Correspondence.calculation _ _ _)
            Domain.Correspondence.empty))))

/-- Recognition specializes the same semantic rule at the actual fragment. -/
theorem Recognized.correspondence {body : List Construction.Instruction}
    (checked : Recognized body) (model : DomainModel) (program : Program) (context : Context) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      body ((spine checked.layout checked.placement).block model) := by
  rcases checked with ⟨layout, placement, rfl⟩
  exact RecordAllocator.correspondence model program context layout placement

theorem read_extended {carriers : Carriers} (environment suffix : Domain.Environment carriers)
    (references : List Nat) (values : Domain.Environment carriers)
    (read : Domain.read environment references = some values) :
    Domain.read (environment ++ suffix) references = some values := by
  induction references generalizing values with
  | nil => simpa only [Domain.read, List.mapM_nil, Option.pure_def] using read
  | cons reference rest ih =>
    cases found : environment[reference]? with
    | none => simp [Domain.read, found] at read
    | some value =>
      cases remaining : Domain.read environment rest with
      | none =>
        simp only [Domain.read] at remaining
        simp [Domain.read, found, remaining] at read
      | some tail =>
        have splitRead := Domain.View.read_cons environment reference rest value tail found remaining
        cases Option.some.inj (splitRead.symm.trans read)
        exact Domain.View.read_cons _ _ _ _ _ (Original.read_append found suffix) (ih tail remaining)

theorem read_appended {carriers : Carriers} (environment : Domain.Environment carriers) :
    ∀ values : Domain.Environment carriers,
      Domain.read (environment ++ values) (List.range' environment.length values.length) =
        some values
  | [] => rfl
  | value :: values => by
      simp only [Domain.read, List.length_cons, List.range'_succ, List.mapM_cons]
      have tail := read_appended (environment ++ [value]) values
      simp only [Domain.read, List.length_append, List.length_cons, List.length_nil,
        List.append_assoc, List.singleton_append] at tail
      rw [tail]
      simp

def silent_sequence {carriers : Carriers} {captured environment next final : Domain.Environment carriers}
    {first rest : Domain.View.Block carriers}
    (step : first environment = .done next)
    (before : captured <+: environment) (after : captured <+: next)
    (tail : Original.Simulation Eq (fun _ frame ↦ captured <+: frame) (.done final) (rest next)) :
    Original.Simulation Eq (fun _ frame ↦ captured <+: frame) (.done final)
      (Domain.View.sequence first rest environment) := by
  rw [Domain.View.sequence_return first rest environment next step]
  exact .checkpoint environment before (.checkpoint next after tail)

/-- Every intermediate value is retained in the target frame. The final two
cells are the extended store and its nominal (constructor, old length) handle. -/
def result (model : DomainModel) (layout : Layout) (data : layout.recordType.isHandle = false)
    (environment : Domain.Environment model.toCarriers) (records : List (model.Value layout.recordType))
    (record : model.Value layout.recordType) : Domain.Environment model.toCarriers :=
  environment ++ [.data (.index layout.constructor), .data (.index records.length),
    .data ⟨layout.recordType, data, record⟩,
    .data ⟨.sequence layout.recordType, data, records ++ [record]⟩,
    .data ⟨layout.referenceType, rfl, (layout.constructor, records.length, ())⟩]

set_option backward.isDefEq.respectTransparency false in
/-- The source-free allocation rule has only representation and bounded-index
premises. It quantifies all record contents and caller prefixes. -/
noncomputable def simulation (model : DomainModel) (layout : Layout)
    (data : layout.recordType.isHandle = false)
    (fieldData : layout.fields.toList.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers) (store : Nat) (fields : List Nat)
    (records : List (model.Value layout.recordType)) (record : model.Value layout.recordType)
    (readStore : environment[store]? = some (.data ⟨.sequence layout.recordType, data, records⟩))
    (readFields : Domain.read environment fields = Domain.encodeValues (layout.fields.unpack record))
    (tagBound : layout.constructor < indexLimit) (lengthBound : records.length < indexLimit) :
    Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (result model layout data environment records record))
      ((spine layout ⟨environment.length, store, fields⟩).block model environment) := by
  let tag : Domain.Value model.toCarriers := .data (.index layout.constructor)
  let length : Domain.Value model.toCarriers := .data (.index records.length)
  let packed : Domain.Value model.toCarriers := .data ⟨layout.recordType, data, record⟩
  let extended : Domain.Value model.toCarriers := .data ⟨.sequence layout.recordType, data, records ++ [record]⟩
  let reference : Domain.Value model.toCarriers := .data ⟨layout.referenceType, rfl, (layout.constructor, records.length, ())⟩
  have fieldsPlain : layout.fields.hasHandle = false := data
  have recordLocal : Domain.localType layout.recordType = true := by simp [Domain.localType, Domain.dataType, data]
  have sequenceLocal : Domain.localType (.sequence layout.recordType) = true := by
    simp [Domain.localType, Domain.dataType, Ty.isHandle, Ty.isCustody, data]
  have tagStep : Domain.View.execute model (.indexConstant layout.constructor) [] [.data .index] environment =
      .done (environment ++ [tag]) := by
    have law := ConnectionPrimitives.view_execute model (.indexConstant layout.constructor) .nil rfl rfl environment [] rfl
    simpa [Primitive.results, Primitive.evaluateOn, tagBound, primitiveOutcome, tag, Original.encodeHelperResult,
      Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, PIR.Process.bind] using law
  have lengthRead : Domain.read (environment ++ [tag]) [store] =
      Domain.encodeValues (tys := [.sequence layout.recordType]) (.cons records .nil) := by
    simp [Domain.read, Original.read_append readStore [tag], Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, data]
  have lengthStep : Domain.View.execute model (.sequenceLength layout.recordType) [store] [.data .index]
      (environment ++ [tag]) = .done (environment ++ [tag, length]) := by
    have law := ConnectionPrimitives.view_execute model (.sequenceLength layout.recordType) (.cons records .nil)
      (by simpa [Primitive.arguments] using sequenceLocal) rfl _ _ lengthRead
    simpa [Primitive.results, Primitive.evaluateOn, lengthBound, primitiveOutcome, length, Original.encodeHelperResult,
      Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, PIR.Process.bind, List.append_assoc] using law
  have fieldsRead : Domain.read (environment ++ [tag, length]) fields =
      Domain.encodeValues (layout.fields.unpack record) := by
    rw [Original.encodeHelperResult_eq fieldData] at readFields ⊢
    exact read_extended environment [tag, length] fields _ readFields
  have packStep : Domain.View.calculation model (.makeProduct layout.recordIdentity "Record" layout.fields)
      fields [.data layout.recordType] (environment ++ [tag, length]) =
        .done (environment ++ [tag, length, packed]) := by
    have law := ConnectionCalculations.view_calculation model (.makeProduct layout.recordIdentity "Record" layout.fields)
      (layout.fields.unpack record) fieldData (by simpa [Calculation.op, Op.results, Layout.recordType] using recordLocal) _ _ fieldsRead
    simpa [ConnectionCalculations.closedCalculation, ConnectionCalculations.calculationRegions,
      Calculation.op, Op.results, Evaluation.operationOn, ProductFields.pack_unpack, PIR.Process.interpret, closedLift,
      PIR.Process.bind, Original.encodeHelperResult, Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
      Domain.Payload.ofValue, Ty.isHandle, fieldsPlain, packed, Layout.recordType, List.append_assoc] using law
  have appendRead : Domain.read (environment ++ [tag, length, packed]) [store, environment.length + 2] =
      Domain.encodeValues (tys := [.sequence layout.recordType, layout.recordType]) (.cons records (.cons record .nil)) := by
    have selected := Domain.View.read_cons (environment ++ [tag, length, packed]) store
      [environment.length + 2] (.data ⟨.sequence layout.recordType, data, records⟩) [packed]
      (Original.read_append readStore [tag, length, packed])
      (Domain.View.read_cons _ _ [] packed [] (by simp) rfl)
    rw [selected]
    simp [Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, fieldsPlain, packed, Layout.recordType]
  have appendStep : Domain.View.execute model (.sequenceAppend layout.recordType) [store, environment.length + 2]
      [.data (.sequence layout.recordType)] (environment ++ [tag, length, packed]) =
        .done (environment ++ [tag, length, packed, extended]) := by
    have law := ConnectionPrimitives.view_execute model (.sequenceAppend layout.recordType) (.cons records (.cons record .nil))
      (by simp [Primitive.arguments, sequenceLocal, recordLocal])
      (by simpa [Primitive.results] using sequenceLocal) _ _ appendRead
    simpa [Primitive.results, Primitive.evaluateOn, primitiveOutcome, Original.encodeHelperResult,
      Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, data,
      PIR.Process.bind, List.append_assoc, extended] using law
  have referenceRead : Domain.read (environment ++ [tag, length, packed, extended])
      [environment.length, environment.length + 1] =
      Domain.encodeValues (tys := referenceFields.toList) (.cons layout.constructor (.cons records.length .nil)) := by
    change Domain.read (environment ++ [tag, length, packed, extended])
      [environment.length, environment.length + 1] = some [tag, length]
    simp [Domain.read]
  have referenceStep : Domain.View.calculation model (.makeProduct layout.referenceIdentity "Record" referenceFields)
      [environment.length, environment.length + 1] [.data layout.referenceType]
      (environment ++ [tag, length, packed, extended]) =
        .done (environment ++ [tag, length, packed, extended, reference]) := by
    have law := ConnectionCalculations.view_calculation model (.makeProduct layout.referenceIdentity "Record" referenceFields)
      (.cons layout.constructor (.cons records.length .nil)) rfl rfl _ _ referenceRead
    simpa [ConnectionCalculations.closedCalculation, ConnectionCalculations.calculationRegions,
      Calculation.op, Op.results, Evaluation.operationOn, PIR.Process.interpret, closedLift,
      PIR.Process.bind, Original.encodeHelperResult, Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
      Domain.Payload.ofValue, reference, Layout.referenceType, referenceFields, ProductFields.pack, Ty.isHandle, ProductFields.hasHandle, List.append_assoc] using law
  apply silent_sequence tagStep (List.prefix_refl _) (by simp)
  apply silent_sequence lengthStep (by simp) (by simp)
  apply silent_sequence packStep (by simp) (by simp)
  apply silent_sequence appendStep (by simp) (by simp)
  apply silent_sequence referenceStep (by simp) (by simp)
  exact .done rfl

/-- An invalid constructor refuses before looking up the record store. The
checkpoint preceding that instruction remains part of the actual execution. -/
noncomputable def refused_constructor (model : DomainModel) (layout : Layout)
    (placement : Placement) (environment : Domain.Environment model.toCarriers)
    (invalid : ¬ layout.constructor < indexLimit) :
    Original.Simulation (Eq (α := Domain.Environment model.toCarriers))
      (fun _ frame ↦ environment <+: frame) (.halt .refused)
      ((spine layout placement).block model environment) := by
  have stopped : Domain.View.execute model (.indexConstant layout.constructor) [] [.data .index]
      environment = .halt .refused := by
    have law := ConnectionPrimitives.view_execute model (.indexConstant layout.constructor)
      .nil rfl rfl environment [] rfl
    simpa [Primitive.results, Primitive.evaluateOn, invalid, primitiveOutcome, PIR.Process.bind]
      using law
  change Original.Simulation _ _ _ (Domain.View.sequence _ _ environment)
  rw [Domain.View.sequence_stop _ _ _ .refused stopped]
  exact .checkpoint environment (List.prefix_refl _) (.halt .refused)

/-- Execute a recognized fragment in its actual caller frame. The only offset
premise connects its checked result references with the current frame length. -/
noncomputable def Recognized.simulation {body : List Construction.Instruction}
    (checked : Recognized body) (model : DomainModel) (program : Program) (context : Context)
    (data : checked.layout.recordType.isHandle = false)
    (fieldData : checked.layout.fields.toList.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers)
    (records : List (model.Value checked.layout.recordType))
    (record : model.Value checked.layout.recordType)
    (start : checked.placement.start = environment.length)
    (readStore : environment[checked.placement.store]? =
      some (.data ⟨.sequence checked.layout.recordType, data, records⟩))
    (readFields : Domain.read environment checked.placement.fields =
      Domain.encodeValues (checked.layout.fields.unpack record))
    (tagBound : checked.layout.constructor < indexLimit)
    (lengthBound : records.length < indexLimit) :
    Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (result model checked.layout data environment records record))
      (Domain.evaluate model program context body environment) := by
  rw [checked.correspondence model program context]
  rcases checked with ⟨layout, ⟨position, store, fields⟩, matched⟩
  dsimp only at start ⊢
  subst position
  exact RecordAllocator.simulation model layout data fieldData environment store fields records
    record readStore readFields tagBound lengthBound

end Zkc.Realization.RecordAllocator
