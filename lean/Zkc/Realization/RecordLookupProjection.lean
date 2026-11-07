module

public import Zkc.Realization.RecordLookup
public import Zkc.Realization.RecordProjection
public import Zkc.Construction.ConnectionClosedSimulation

@[expose] public section

/-! Compose a checked constructor lookup with its actual nominal projections.
The provider supplies immutable-storage membership. The common rule derives the
record's SSA position, field routing and checkpoint preservation. -/
set_option autoImplicit false
namespace Zkc.Realization.RecordLookupProjection
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Recognized (body : List Construction.Instruction) where
  lookupBody : List Construction.Instruction
  projectionBody : List Construction.Instruction
  lookup : RecordLookup.Recognized lookupBody
  projection : RecordProjection.Recognized projectionBody
  sameType : lookup.layout.element = projection.layout.type
  recordPosition : projection.reference = lookup.placement.start + 2
  exactBody : body = lookupBody ++ projectionBody

def recognize (body : List Construction.Instruction) : Option (Recognized body) := do
  let lookupBody := body.take 4
  let projectionBody := body.drop 4
  let lookup ← RecordLookup.recognize lookupBody
  let projection ← RecordProjection.recognize projectionBody
  if sameType : lookup.layout.element = projection.layout.type then
    if recordPosition : projection.reference = lookup.placement.start + 2 then
      some ⟨lookupBody, projectionBody, lookup, projection, sameType, recordPosition,
        (List.take_append_drop 4 body).symm⟩
    else none
  else none

/-- The projection refers to the record actually selected by the lookup.
No separate field equation or successful projection premise is supplied. -/
theorem Recognized.simulation {body : List Construction.Instruction} (checked : Recognized body)
    (model : DomainModel) (program : Program) (context : Context)
    (data : checked.projection.layout.type.isHandle = false)
    (localFields : ∀ selection ∈ checked.projection.selections,
      Domain.localType selection.type = true)
    (environment : Domain.Environment model.toCarriers) (position : Nat)
    (records : List (model.Value checked.projection.layout.type))
    (record : model.Value checked.projection.layout.type)
    (start : checked.lookup.placement.start = environment.length)
    (readTag : environment[checked.lookup.placement.constructor]? =
      some (.data (.index checked.lookup.layout.constructor)))
    (readSlot : environment[checked.lookup.placement.slot]? = some (.data (.index position)))
    (readStore : environment[checked.lookup.placement.store]? =
      some (.data ⟨.sequence checked.projection.layout.type, data, records⟩))
    (found : records[position]? = some record)
    (tagBound : checked.lookup.layout.constructor < indexLimit) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (environment ++
        [.data (.index checked.lookup.layout.constructor), .data (.boolean true),
          .data ⟨checked.projection.layout.type, data, record⟩] ++
        RecordProjection.results model checked.projection.layout record
          checked.projection.selections))
      (Domain.evaluate model program context body environment)) := by
  rcases checked with ⟨first, rest, lookup, projection, sameType, recordPosition, rfl⟩
  rcases lookup with ⟨⟨constructor, element⟩, placement, firstBody⟩
  dsimp only at sameType
  subst element
  let checkedLookup : RecordLookup.Recognized first :=
    ⟨⟨constructor, projection.layout.type⟩, placement, firstBody⟩
  have head := checkedLookup.simulation model program context data environment position
    records record
    start readTag readSlot readStore found tagBound
  let added : Domain.Environment model.toCarriers :=
    [.data (.index constructor), .data (.boolean true),
      .data ⟨projection.layout.type, data, record⟩]
  have selected : (environment ++ added)[projection.reference]? =
      some (.data ⟨projection.layout.type, data, record⟩) := by
    dsimp only at recordPosition start
    simp [recordPosition, start, added]
  obtain ⟨tail⟩ := projection.simulation model program context data localFields
    (environment ++ added) environment (List.prefix_append _ _) record selected
  rw [Domain.evaluate_append]
  exact ⟨head.continueDone (fun _ held ↦ held) tail⟩

end Zkc.Realization.RecordLookupProjection
