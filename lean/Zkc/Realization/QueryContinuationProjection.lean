module

public import Zkc.Realization.QueryContinuation

@[expose] public section

/-! Complete ordered projection of an actually saved continuation. The same
nominal unpacking used by the generated return arm recovers the outer frame,
parent instance, parent position and every preceding answer index. -/
set_option autoImplicit false
namespace Zkc.Realization.QueryContinuation
open Zkc.Source Zkc.Source.Structured Zkc.Construction

def projection (identity : String) (count : Nat) : RecordProjection.Layout :=
  ⟨identity, "Record", fields count⟩

def Frame.values (frame : Frame) : List Nat :=
  [frame.outer, frame.outerInstance, frame.parentInstance, frame.position] ++ frame.answers

theorem indexFields_local (count : Nat) :
    (ClearStorage.indexFields count .nil).toList.all Domain.localType = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [ClearStorage.indexFields, ProductFields.toList, List.all_cons,
        Bool.and_eq_true] using And.intro (show Domain.localType .index = true from rfl) ih

theorem fields_local (count : Nat) : (fields count).toList.all Domain.localType = true := by
  simpa only [fields, ProductFields.toList, List.all_cons, Domain.localType,
    Domain.dataType, Ty.isHandle, Ty.isCustody, Bool.false_or, Bool.not_false,
    Bool.true_and] using indexFields_local count

theorem frameData (identity : String) (count : Nat) :
    (layout identity count).type.isHandle = false := by
  have indices : (ClearStorage.indexFields count .nil).hasHandle = false := by
    induction count with
    | zero => rfl
    | succ count ih => simpa [ClearStorage.indexFields, ProductFields.hasHandle, Ty.isHandle] using ih
  simpa [layout, RecordAppend.Layout.type, fields, Ty.isHandle, ProductFields.hasHandle] using indices

/-- The coordinate packer is exact in both width and order. Its successful
record encodes the original index list, rather than a type-compatible list. -/
theorem packed_indices {carriers : Carriers} (count : Nat) {indices : List Nat}
    {record : carriers.ProductValue (ClearStorage.indexFields count .nil)}
    (packed : ClearStorage.packCoordinates count indices () = some record) :
    Domain.encodeValues ((ClearStorage.indexFields count .nil).unpack record) =
      some (indices.map (fun value ↦ Domain.Value.data (.index value))) := by
  induction count generalizing indices with
  | zero =>
      cases indices with
      | nil => cases Option.some.inj packed; rfl
      | cons => simp [ClearStorage.packCoordinates] at packed
  | succ count ih =>
      cases indices with
      | nil => simp [ClearStorage.packCoordinates] at packed
      | cons index rest =>
          obtain ⟨saved, found, equal⟩ := Option.map_eq_some_iff.mp packed
          cases equal
          change Domain.encodeValues (.cons (ty := .index) index
            ((ClearStorage.indexFields count .nil).unpack saved)) = _
          simp only [Domain.encodeValues_cons, ih found, List.map_cons]
          rfl

set_option backward.isDefEq.respectTransparency false in
/-- Unpacking derives every header and prior-answer operand from the saved
record. This law is independent of the protocol's mathematical answer rule. -/
theorem Encodes.projected {model : DomainModel} {identity : String} {count : Nat}
    {frame : Frame} {record : model.Value (layout identity count).type}
    (encoding : Encodes identity count frame record) :
    RecordProjection.results model (projection identity count) record
      (RecordProjection.allFields (fields count)) =
        frame.values.map (fun value ↦ Domain.Value.data (.index value)) := by
  have whole : RecordProjection.results model (projection identity count) record
      (RecordProjection.allFields (fields count)) =
        Original.encodeHelperResult ((fields count).unpack record) :=
    RecordProjection.results_all model identity "Record" (fields count) record (fields_local count)
  rw [whole]
  obtain ⟨saved, packed, rfl⟩ := encoding
  have tail := packed_indices count packed
  change (Domain.encodeValues (.cons (ty := .index) frame.outer (.cons (ty := .index) frame.outerInstance
    (.cons (ty := .index) frame.parentInstance (.cons (ty := .index) frame.position
      ((ClearStorage.indexFields count .nil).unpack saved)))))).getD [] = _
  simp only [Domain.encodeValues_cons, tail, Frame.values, List.map_append,
    List.map_cons, List.map_nil]
  rfl

/-- The physical field tuple is the exact saved coordinate and answer list. -/
theorem Encodes.values_encoded {model : DomainModel} {identity : String} {count : Nat}
    {frame : Frame} {record : model.Value (layout identity count).type}
    (encoding : Encodes identity count frame record) :
    Domain.encodeValues ((fields count).unpack record) =
      some (frame.values.map (fun value ↦ Domain.Value.data (.index value))) := by
  have all := RecordProjection.results_all model identity "Record" (fields count) record
    (fields_local count)
  have encoded := Original.encodeHelperResult_eq (carriers := model.toCarriers)
    (fields_local count) ((fields count).unpack record)
  exact encoded.trans (congrArg some (all.symm.trans encoding.projected))

set_option backward.isDefEq.respectTransparency false in
/-- The physical projection uses the complete field list in its declared
order. Its result is the saved frame, even after unrelated caller extension. -/
theorem Encodes.project {model : DomainModel} {identity : String} {count : Nat}
    {frame : Frame} {record : model.Value (layout identity count).type}
    (encoding : Encodes identity count frame record)
    (environment captured : Domain.Environment model.toCarriers)
    (preserved : captured <+: environment) (reference : Nat)
    (read : environment[reference]? =
      some (.data ⟨(layout identity count).type, frameData identity count, record⟩))
    (program : Program) (context : Context) :
    Nonempty (Original.Simulation Eq (fun _ live ↦ captured <+: live)
      (.done (environment ++ frame.values.map (fun value ↦ Domain.Value.data (.index value))))
      (Domain.evaluate model program context
        (RecordProjection.instructions (projection identity count) reference
          (RecordProjection.allFields (fields count))) environment)) := by
  let checked : RecordProjection.Recognized
      (RecordProjection.instructions (projection identity count) reference
        (RecordProjection.allFields (fields count))) :=
    ⟨projection identity count, reference, RecordProjection.allFields (fields count), rfl⟩
  have connected := checked.simulation model program context (frameData identity count)
    (RecordProjection.allFields_local _ (fields_local count))
    environment captured preserved record read
  simpa only [checked, encoding.projected] using connected

def loadInstructions (identity : String) (count start store slot : Nat) :
    List Construction.Instruction :=
  ⟨.execute (.sequenceAt (layout identity count).type), [store, slot],
    [.data (layout identity count).type], []⟩ ::
    RecordProjection.instructions (projection identity count) start
      (RecordProjection.allFields (fields count))

structure Loaded (body : List Construction.Instruction) where
  identity : String
  count : Nat
  start : Nat
  store : Nat
  slot : Nat
  exactBody : body = loadInstructions identity count start store slot

/-- Recognize the entire load/unpack, retaining its nominal identity and all
field ordinals. Static continuation/source ownership is a separate relation. -/
def recognizeLoad (start : Nat) (body : List Construction.Instruction) : Option (Loaded body) := do
  let first :: _ := body | none
  let .execute (.sequenceAt (.product identity "Record" fields)) := first.operation | none
  let [store, slot] := first.operands | none
  let count := fields.toList.length - 4
  if exactBody : body = loadInstructions identity count start store slot then
    some ⟨identity, count, start, store, slot, exactBody⟩
  else none

set_option backward.isDefEq.respectTransparency false in
/-- Load and unpack are connected as one actual fragment. The immutable saved
slot supplies the record and the projection supplies every returned operand.
No separately chosen parent coordinates or ordered answer list are assumed. -/
theorem Stored.load_project {model : DomainModel} {identity : String} {count slot : Nat}
    {frame : Frame} {records : List (model.Value (layout identity count).type)}
    (stored : Stored identity count records slot frame)
    (environment : Domain.Environment model.toCarriers) (storeReference slotReference : Nat)
    (read : Domain.read environment [storeReference, slotReference] = Domain.encodeValues
      (tys := [.sequence (layout identity count).type, .index]) (.cons records (.cons slot .nil)))
    (program : Program) (context : Context) :
    ∃ record, Encodes identity count frame record ∧
      Nonempty (Original.Simulation Eq (fun _ live ↦ environment <+: live)
        (.done (environment ++
          [.data ⟨(layout identity count).type, frameData identity count, record⟩] ++
          frame.values.map (fun value ↦ Domain.Value.data (.index value))))
        (Domain.evaluate model program context
          (loadInstructions identity count environment.length storeReference slotReference)
          environment)) := by
  have inputData : (Primitive.sequenceAt (layout identity count).type).arguments.all
      Domain.localType = true := by
    simp [Primitive.arguments, Domain.localType, Domain.dataType, Ty.isHandle, Ty.isCustody,
      frameData]
  have outputData : (Primitive.sequenceAt (layout identity count).type).results.all
      Domain.localType = true := by
    simp [Primitive.results, Domain.localType, Domain.dataType, Ty.isCustody, frameData]
  obtain ⟨record, encoding, loaded⟩ := stored.load inputData outputData environment _ read
  let entry : Domain.Value model.toCarriers :=
    .data ⟨(layout identity count).type, frameData identity count, record⟩
  have single : Domain.Value.encode (layout identity count).type record = some entry :=
    Domain.Value.encode_ofPayload (by simp [Domain.Payload.ofValue, frameData])
  have encoded : Original.encodeHelperResult (.cons record .nil) = [entry] := by
    simp [Original.encodeHelperResult, Domain.encodeValues_cons, Domain.encodeValues_nil,
      single]
  rw [encoded] at loaded
  obtain ⟨unpacked⟩ := RecordProjection.simulation model (projection identity count)
    (frameData identity count) (RecordProjection.allFields (fields count))
    (RecordProjection.allFields_local _ (fields_local count))
    (environment ++ [entry]) environment (List.prefix_append _ _) environment.length record
    (by simp; rfl)
  refine ⟨record, encoding, ⟨?_⟩⟩
  have correspondence := Domain.Correspondence.sequence
    (Domain.Correspondence.execute (model := model) (program := program) (context := context)
      (.sequenceAt (layout identity count).type) [storeReference, slotReference]
      [.data (layout identity count).type])
    (RecordProjection.correspondence model program context (projection identity count)
      environment.length (RecordProjection.allFields (fields count)))
  change Domain.Correspondence.Block
    (loadInstructions identity count environment.length storeReference slotReference)
    (Domain.View.sequence
      (Domain.View.execute model (.sequenceAt (layout identity count).type)
        [storeReference, slotReference] [.data (layout identity count).type])
      ((RecordProjection.spine (projection identity count) environment.length
        (RecordProjection.allFields (fields count))).block model)) at correspondence
  rw [correspondence]
  apply RecordAllocator.silent_sequence loaded (List.prefix_refl _) (List.prefix_append _ _)
  simpa only [encoding.projected] using unpacked

theorem Loaded.simulation {body : List Construction.Instruction} (checked : Loaded body)
    (model : DomainModel) (program : Program) (context : Context)
    (records : List (model.Value (layout checked.identity checked.count).type))
    (slot : Nat) (frame : Frame)
    (stored : Stored checked.identity checked.count records slot frame)
    (environment : Domain.Environment model.toCarriers)
    (start : checked.start = environment.length)
    (read : Domain.read environment [checked.store, checked.slot] = Domain.encodeValues
      (tys := [.sequence (layout checked.identity checked.count).type, .index])
      (.cons records (.cons slot .nil))) :
    ∃ record, Encodes checked.identity checked.count frame record ∧
      Nonempty (Original.Simulation Eq (fun _ live ↦ environment <+: live)
        (.done (environment ++
          [.data ⟨(layout checked.identity checked.count).type,
            frameData checked.identity checked.count, record⟩] ++
          frame.values.map (fun value ↦ Domain.Value.data (.index value))))
        (Domain.evaluate model program context body environment)) := by
  rcases checked with ⟨identity, count, offset, store, reference, rfl⟩
  dsimp only at start
  rw [start]
  exact stored.load_project environment store reference read program context

end Zkc.Realization.QueryContinuation
