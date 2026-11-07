module

public import Zkc.Realization.ClearStorageCalculations
public import Zkc.Realization.RecordAllocator

@[expose] public section

/-! Clear publication representation and the actual immutable allocator share
one boundary: the record just encoded from the published word. The physical
rule knows no protocol mathematics; the representation retains source identity.
-/

set_option autoImplicit false
namespace Zkc.Realization.ClearStorage
open Zkc.Source Zkc.Source.Structured Zkc.Construction

variable {kind : OracleKind} {model : DomainModel}

/-- Use the same nominal types and ordered fields as the selected base layout. -/
def Layout.allocator (layout : Layout kind) : RecordAllocator.Layout :=
  ⟨layout.constructor, layout.recordIdentity, layout.referenceIdentity, layout.fields⟩

/-- Allocating an encoded publication establishes the stored association in the
actual instruction semantics. The caller supplies checked reads and finite
index bounds, not a proof that a chosen evaluator computes the allocation. -/
theorem Encodes.allocate {layout : Layout kind}
    {word : PublishedWords.Word model kind.answer} {record : model.Value layout.recordType}
    (encoding : Encodes layout word record)
    (words : PublishedWords.Table model) (records : List (model.Value layout.recordType))
    (program : Program) (context : Context)
    (data : layout.recordType.isHandle = false)
    (fieldData : layout.fields.toList.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers) (store : Nat) (fields : List Nat)
    (readStore : environment[store]? = some (.data ⟨.sequence layout.recordType, data, records⟩))
    (readFields : Domain.read environment fields = Domain.encodeValues (layout.fields.unpack record))
    (tagBound : layout.constructor < indexLimit) (lengthBound : records.length < indexLimit) :
    Stored layout (⟨kind.answer, word⟩ :: words) (records ++ [record])
      (layout.constructor, records.length) word ∧
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (RecordAllocator.result model layout.allocator data environment records record))
      (Domain.evaluate model program context
        (RecordAllocator.instructions layout.allocator ⟨environment.length, store, fields⟩)
        environment)) := by
  refine ⟨stored_append layout words records word record encoding, ?_⟩
  rw [RecordAllocator.correspondence]
  exact ⟨RecordAllocator.simulation model layout.allocator data fieldData environment store fields
    records record readStore readFields tagBound lengthBound⟩

end Zkc.Realization.ClearStorage
