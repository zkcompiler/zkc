module

public import Zkc.Realization.ClearStorageCalculations
public import Zkc.Realization.CaptureLayout
public import Zkc.Realization.RecordAllocator

@[expose] public section

/-! Immutable records for retained virtual-oracle closures. The source already
owns the checked body and its captures. This layer changes their representation
without selecting a new body, parent handle, mathematical parameter or location.
-/

set_option autoImplicit false
namespace Zkc.Realization.VirtualStorage
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Layout (inputs : List Ty) where
  constructor : Nat
  recordIdentity : String
  referenceIdentity : String
  location : OracleLocation
  fields : ProductFields
  captures : CaptureLayout.Layout inputs fields.toList

variable {inputs : List Ty}

def Layout.depth (layout : Layout inputs) := (ClearStorage.coordinates layout.location.invocation.frames).length

def Layout.recordFields (layout : Layout inputs) : ProductFields :=
  ClearStorage.indexFields layout.depth (.cons .index (.cons .index layout.fields))

def Layout.recordType (layout : Layout inputs) : Ty :=
  .product layout.recordIdentity "Record" layout.recordFields

def Layout.allocator (layout : Layout inputs) : RecordAllocator.Layout :=
  ⟨layout.constructor, layout.recordIdentity, layout.referenceIdentity, layout.recordFields⟩

variable {model : DomainModel}

/-- The layout fixes the static construction; the record fixes its actual
iteration coordinates and the ordered physical captures. Leaf accounting is a
separate invariant of the query controller, not a theorem of record encoding. -/
structure Encodes (references : CaptureLayout.References) (layout : Layout inputs)
    (location : OracleLocation) (rows leaves : Nat) (captures : Values model.Value inputs)
    (record : model.Value layout.recordType) : Prop where
  location_eq : ClearStorage.staticLocation location = ClearStorage.staticLocation layout.location
  captured : ∃ physical : Values model.Value layout.fields.toList,
    CaptureLayout.Related references layout.captures captures physical ∧
    ClearStorage.packCoordinates layout.depth (ClearStorage.coordinates location.invocation.frames)
      (rows, leaves, layout.fields.pack physical) = some record

/-- The original closure's captured values determine a record once their
physical reference association is available. No mathematical fold law is used. -/
theorem encoding_exists (references : CaptureLayout.References) (layout : Layout inputs)
    (location : OracleLocation)
    (same : ClearStorage.staticLocation location = ClearStorage.staticLocation layout.location)
    (rows leaves : Nat) (captures : Values model.Value inputs)
    (physical : Values model.Value layout.fields.toList)
    (related : CaptureLayout.Related references layout.captures captures physical) :
    ∃ record, Encodes references layout location rows leaves captures record := by
  have frames := congrArg (fun value ↦ value.invocation.frames) same
  obtain ⟨record, packed⟩ := ClearStorage.packCoordinates_exists (carriers := model.toCarriers)
    (tail := .cons .index (.cons .index layout.fields))
    layout.depth (ClearStorage.coordinates location.invocation.frames)
    (rows, leaves, layout.fields.pack physical)
    (ClearStorage.coordinates_length_of_static frames)
  exact ⟨record, same, physical, related, packed⟩

theorem Encodes.transport {before after : CaptureLayout.References}
    (kept : ∀ kind identity anchor physical,
      before kind identity anchor physical → after kind identity anchor physical)
    {layout : Layout inputs} {location : OracleLocation} {rows leaves : Nat}
    {captures : Values model.Value inputs} {record : model.Value layout.recordType}
    (encoded : Encodes before layout location rows leaves captures record) :
    Encodes after layout location rows leaves captures record := by
  obtain ⟨physical, related, packed⟩ := encoded.captured
  exact ⟨encoded.location_eq, physical, related.transport kept, packed⟩

/-- A record cannot stand for a closure created at a different dynamic source
occurrence, even if both closures have identical parameters and parents. -/
theorem Encodes.location_unique {references : CaptureLayout.References} {layout : Layout inputs}
    {first second : OracleLocation} {rows otherRows leaves otherLeaves : Nat}
    {captures others : Values model.Value inputs} {record : model.Value layout.recordType}
    (left : Encodes references layout first rows leaves captures record)
    (right : Encodes references layout second otherRows otherLeaves others record) : first = second := by
  obtain ⟨_, _, leftPacked⟩ := left.captured
  obtain ⟨_, _, rightPacked⟩ := right.captured
  exact ClearStorage.location_unique (left.location_eq.trans right.location_eq.symm)
    (ClearStorage.packCoordinates_unique layout.depth leftPacked rightPacked).1

/-- The exact original capture tuple, not just its type or number of fields,
is recoverable from a record with an unambiguous physical reference view. -/
theorem Encodes.captures_unique {references : CaptureLayout.References}
    (unique : CaptureLayout.Unambiguous references) {layout : Layout inputs}
    {first second : OracleLocation} {rows otherRows leaves otherLeaves : Nat}
    {captures others : Values model.Value inputs} {record : model.Value layout.recordType}
    (left : Encodes references layout first rows leaves captures record)
    (right : Encodes references layout second otherRows otherLeaves others record) : captures = others := by
  obtain ⟨physical, related, packed⟩ := left.captured
  obtain ⟨other, otherRelated, otherPacked⟩ := right.captured
  have payload := (ClearStorage.packCoordinates_unique layout.depth packed otherPacked).2
  have same := congrArg (fun value ↦ layout.fields.unpack value.2.2) payload
  simp only [ProductFields.unpack_pack] at same
  cases same
  exact related.source_unique unique otherRelated

/-- Actual nominal record projection recovers the corresponding physical
capture. `CaptureLayout.Related.get` then supplies its source value or parent
association without a separately authored field-order proof. -/
theorem Encodes.capture_read {references : CaptureLayout.References} {layout : Layout inputs}
    {location : OracleLocation} {rows leaves : Nat} {captures : Values model.Value inputs}
    {record : model.Value layout.recordType}
    (encoded : Encodes references layout location rows leaves captures record)
    {type : Ty} (slot : Var layout.fields.toList type) :
    ∃ physical, CaptureLayout.Related references layout.captures captures physical ∧
      ConnectionCalculations.closedCalculation model
        (.getProduct layout.recordIdentity "Record" layout.recordFields type
          (ClearStorage.afterCoordinates layout.depth (.there (.there slot)))) (.cons record .nil) =
        .done (.cons (physical.get slot) .nil) := by
  obtain ⟨physical, related, packed⟩ := encoded.captured
  refine ⟨physical, related, ?_⟩
  have selected := ClearStorage.packed_projection layout.depth packed (.there (.there slot))
  simp only [ProductFields.unpack, ProductFields.unpack_pack] at selected
  exact congrArg (fun value : model.Value type ↦
    (PIR.Process.done (.cons value .nil) : Closed (Values model.Value [type]))) selected

/-- A complete closure record is allocated by the same physical rule as a
published base word. The appended record retains its original capture relation. -/
theorem Encodes.allocate {references : CaptureLayout.References} {layout : Layout inputs}
    {location : OracleLocation} {rows leaves : Nat} {captures : Values model.Value inputs}
    {record : model.Value layout.recordType}
    (encoded : Encodes references layout location rows leaves captures record)
    (records : List (model.Value layout.recordType)) (program : Program) (context : Context)
    (data : layout.recordType.isHandle = false)
    (fieldData : layout.recordFields.toList.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers) (store : Nat) (fields : List Nat)
    (readStore : environment[store]? = some (.data ⟨.sequence layout.recordType, data, records⟩))
    (readFields : Domain.read environment fields = Domain.encodeValues (layout.recordFields.unpack record))
    (tagBound : layout.constructor < indexLimit) (lengthBound : records.length < indexLimit) :
    (∃ stored, (records ++ [record])[records.length]? = some stored ∧
      Encodes references layout location rows leaves captures stored) ∧
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (RecordAllocator.result model layout.allocator data environment records record))
      (Domain.evaluate model program context
        (RecordAllocator.instructions layout.allocator ⟨environment.length, store, fields⟩) environment)) := by
  refine ⟨⟨record, by simp, encoded⟩, ?_⟩
  rw [RecordAllocator.correspondence]
  exact ⟨RecordAllocator.simulation model layout.allocator data fieldData environment store fields
    records record readStore readFields tagBound lengthBound⟩

end Zkc.Realization.VirtualStorage
