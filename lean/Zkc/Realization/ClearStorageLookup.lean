module

public import Zkc.Realization.ClearStorageCalculations
public import Zkc.Realization.RecordLookup

@[expose] public section

/-! The immutable lookup returns precisely the record associated with the
published anchor. Record projections then recover its source coordinates, shape
and payload. A matching length or data type is not an alternative association.
-/

set_option autoImplicit false
namespace Zkc.Realization.ClearStorage
open Zkc.Source Zkc.Source.Structured Zkc.Construction
variable {kind : OracleKind} {model : DomainModel}

def Layout.lookup (layout : Layout kind) : RecordLookup.Layout :=
  ⟨layout.constructor, layout.recordType⟩

/-- Constructor checking and slot lookup preserve the provider-selected record.
The semantic execution is the actual generated four-instruction helper. -/
theorem Stored.lookup {layout : Layout kind} {words : PublishedWords.Table model}
    {records : List (model.Value layout.recordType)} {reference : Nat × Nat}
    {word : PublishedWords.Word model kind.answer}
    (stored : Stored layout words records reference word)
    (program : Program) (context : Context) (data : layout.recordType.isHandle = false)
    (environment : Domain.Environment model.toCarriers) (constructor slot store : Nat)
    (site : String)
    (readTag : environment[constructor]? = some (.data (.index reference.1)))
    (readSlot : environment[slot]? = some (.data (.index reference.2)))
    (readStore : environment[store]? = some (.data ⟨.sequence layout.recordType, data, records⟩))
    (tagBound : layout.constructor < indexLimit) :
    ∃ record, Encodes layout word record ∧
      Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
        (.done (environment ++ [.data (.index layout.constructor), .data (.boolean true),
          .data ⟨layout.recordType, data, record⟩]))
        (Domain.evaluate model program context
          (RecordLookup.instructions layout.lookup
            ⟨environment.length, constructor, slot, store, site⟩) environment)) := by
  obtain ⟨record, tag, found, _, encoding⟩ := stored
  refine ⟨record, encoding, ?_⟩
  rw [RecordLookup.correspondence]
  exact ⟨RecordLookup.simulation model layout.lookup data environment constructor slot store site
    reference.2 records record (by simpa only [Layout.lookup, tag] using readTag)
    readSlot readStore found tagBound⟩

end Zkc.Realization.ClearStorage
