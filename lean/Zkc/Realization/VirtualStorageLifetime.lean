module

public import Zkc.Realization.VirtualStorageInstallation
public import Zkc.Source.Structured.RegisteredLifetime

@[expose] public section

/-! Virtual closure identity survives fresh source-registry insertions and
append-only physical storage. These are the existing source lifetime laws;
no FRI fold relation or alternative provider state machine is introduced. -/

set_option autoImplicit false
namespace Zkc.Realization.VirtualStorage
open Zkc.Source Zkc.Source.Structured
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment}

/-- Source freshness, physical append and preservation of captured references
retain the exact checked body and captures selected at installation. -/
theorem Stored.transport {checked : CheckedOracle snapshot domains math}
    {layout : Layout checked.declaration.inputs.dropLast}
    {beforeReferences afterReferences : CaptureLayout.References}
    {before after : OracleEntries model snapshot domains math}
    {records later : List (model.Value layout.recordType)} {reference : Nat × Nat}
    {location : OracleLocation} {rows leaves holder : Nat} {receivers : List Nat}
    {captures : Values model.Value checked.declaration.inputs.dropLast}
    (stored : Stored checked layout beforeReferences before records reference
      location rows leaves holder receivers captures)
    (registry : OracleStore.FreshExtension before after) (physical : records <+: later)
    (kept : ∀ kind identity anchor physical,
      beforeReferences kind identity anchor physical → afterReferences kind identity anchor physical) :
    Stored checked layout afterReferences after later reference
      location rows leaves holder receivers captures := by
  obtain ⟨tag, found, record, atSlot, encoded⟩ := stored
  obtain ⟨newer, rfl, fresh⟩ := registry
  obtain ⟨suffix, rfl⟩ := physical
  refine ⟨tag, ?_, record, ?_, encoded.transport kept⟩
  · rw [OracleStore.findSkipNewer newer before _ _
      (fresh location.anchor (OracleStore.hasAnchor_of_find found))]
    exact found
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp atSlot).1).trans atSlot

/-- A virtual physical reference denotes its installed construction anchor.
Its body and captures come from the original checked registry entry. -/
def references (checked : CheckedOracle snapshot domains math)
    (layout : Layout checked.declaration.inputs.dropLast)
    (parents : CaptureLayout.References) (entries : OracleEntries model snapshot domains math)
    (records : List (model.Value layout.recordType)) : CaptureLayout.References :=
  fun kind identity anchor physical ↦ kind = checked.declaration.kind ∧
    identity = layout.referenceIdentity ∧
    ∃ location rows leaves holder receivers captures,
      location.anchor = anchor ∧
      Stored checked layout parents entries records physical
        location rows leaves holder receivers captures

/-- Equal physical slots cannot name two distinct closure occurrences. This
requires neither equal child answers nor an equation for the virtual body. -/
theorem references_unambiguous (checked : CheckedOracle snapshot domains math)
    (layout : Layout checked.declaration.inputs.dropLast) (parents : CaptureLayout.References)
    (entries : OracleEntries model snapshot domains math)
    (records : List (model.Value layout.recordType)) :
    CaptureLayout.Unambiguous (references checked layout parents entries records) := by
  rintro _ _ _ _ physical
    ⟨_, _, first, rows, leaves, holder, receivers, captures, rfl, left⟩
    ⟨_, _, second, otherRows, otherLeaves, otherHolder, otherReceivers, otherCaptures, rfl, right⟩
  obtain ⟨_, _, record, atSlot, encoded⟩ := left
  obtain ⟨_, _, other, otherSlot, otherEncoded⟩ := right
  have same := Option.some.inj (atSlot.symm.trans otherSlot)
  subst other
  exact congrArg OracleLocation.anchor (encoded.location_unique otherEncoded)

theorem references_transport (checked : CheckedOracle snapshot domains math)
    (layout : Layout checked.declaration.inputs.dropLast)
    {beforeReferences afterReferences : CaptureLayout.References}
    {before after : OracleEntries model snapshot domains math}
    {records later : List (model.Value layout.recordType)}
    (registry : OracleStore.FreshExtension before after) (physical : records <+: later)
    (kept : ∀ kind identity anchor physical,
      beforeReferences kind identity anchor physical → afterReferences kind identity anchor physical)
    (kind : OracleKind) (identity : String) (anchor : OracleAnchor) (reference : Nat × Nat)
    (stored : references checked layout beforeReferences before records kind identity anchor reference) :
    references checked layout afterReferences after later kind identity anchor reference := by
  obtain ⟨kindEq, identityEq, location, rows, leaves, holder, receivers, captures, anchorEq, found⟩ := stored
  exact ⟨kindEq, identityEq, location, rows, leaves, holder, receivers, captures, anchorEq,
    found.transport registry physical kept⟩

end Zkc.Realization.VirtualStorage
