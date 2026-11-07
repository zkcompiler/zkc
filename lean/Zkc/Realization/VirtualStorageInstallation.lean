module

public import Zkc.Realization.VirtualStorage
public import Zkc.Realization.RecordLookup
public import Zkc.Source.Structured.OracleVirtualInstallation

@[expose] public section

/-! The original virtual construction and the physical record share the same
checked closure. A returning source instruction supplies the logical registry
entry; actual allocation supplies the immutable physical slot. -/

set_option autoImplicit false
namespace Zkc.Realization.VirtualStorage
open Zkc.Source Zkc.Source.Structured
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment}

/-- This is the existing logical table, retaining the exact checked declaration
and capture tuple rather than an independently chosen virtual evaluator. -/
def table (checked : CheckedOracle snapshot domains math) (location : OracleLocation)
    (rows holder : Nat) (receivers : List Nat)
    (captures : Values model.Value checked.declaration.inputs.dropLast) :
    OracleStoredTable model snapshot domains math checked.declaration.kind.answer :=
  ⟨location.anchor, rows, holder, receivers, .virtual checked rfl captures⟩

def Stored (checked : CheckedOracle snapshot domains math)
    (layout : Layout checked.declaration.inputs.dropLast) (references : CaptureLayout.References)
    (entries : OracleEntries model snapshot domains math)
    (records : List (model.Value layout.recordType)) (reference : Nat × Nat)
    (location : OracleLocation) (rows leaves holder : Nat) (receivers : List Nat)
    (captures : Values model.Value checked.declaration.inputs.dropLast) : Prop :=
  reference.1 = layout.constructor ∧
    OracleStore.find entries checked.declaration.kind.answer location.anchor =
      some (table checked location rows holder receivers captures) ∧
    ∃ record, records[reference.2]? = some record ∧
      Encodes references layout location rows leaves captures record

theorem stored_append (checked : CheckedOracle snapshot domains math)
    (layout : Layout checked.declaration.inputs.dropLast) (references : CaptureLayout.References)
    (entries : OracleEntries model snapshot domains math)
    (records : List (model.Value layout.recordType))
    (location : OracleLocation) (rows leaves holder : Nat) (receivers : List Nat)
    (captures : Values model.Value checked.declaration.inputs.dropLast)
    (record : model.Value layout.recordType)
    (encoded : Encodes references layout location rows leaves captures record) :
    Stored checked layout references
      (⟨checked.declaration.kind.answer, table checked location rows holder receivers captures⟩ :: entries)
      (records ++ [record]) (layout.constructor, records.length) location rows leaves holder receivers captures := by
  refine ⟨rfl, ?_, record, by simp, encoded⟩
  simp [OracleStore.find, table]

/-- A physical lookup of a registered virtual handle returns a record with the
same original captures. Constructor checking remains part of actual execution. -/
theorem Stored.lookup {checked : CheckedOracle snapshot domains math}
    {layout : Layout checked.declaration.inputs.dropLast} {references : CaptureLayout.References}
    {entries : OracleEntries model snapshot domains math}
    {records : List (model.Value layout.recordType)} {reference : Nat × Nat}
    {location : OracleLocation} {rows leaves holder : Nat} {receivers : List Nat}
    {captures : Values model.Value checked.declaration.inputs.dropLast}
    (stored : Stored checked layout references entries records reference location rows leaves holder receivers captures)
    (program : Program) (context : Construction.Context) (data : layout.recordType.isHandle = false)
    (environment : Construction.Domain.Environment model.toCarriers) (constructor slot store : Nat)
    (site : String)
    (readTag : environment[constructor]? = some (.data (.index reference.1)))
    (readSlot : environment[slot]? = some (.data (.index reference.2)))
    (readStore : environment[store]? = some (.data ⟨.sequence layout.recordType, data, records⟩))
    (tagBound : layout.constructor < indexLimit) :
    ∃ record, Encodes references layout location rows leaves captures record ∧
      Nonempty (Construction.Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
        (.done (environment ++ [.data (.index layout.constructor), .data (.boolean true),
          .data ⟨layout.recordType, data, record⟩]))
        (Construction.Domain.evaluate model program context
          (RecordLookup.instructions ⟨layout.constructor, layout.recordType⟩
            ⟨environment.length, constructor, slot, store, site⟩) environment)) := by
  obtain ⟨tag, _, record, found, encoded⟩ := stored
  refine ⟨record, encoded, ?_⟩
  rw [RecordLookup.correspondence]
  exact ⟨RecordLookup.simulation model ⟨layout.constructor, layout.recordType⟩ data environment
    constructor slot store site reference.2 records record
    (by simpa only [tag] using readTag) readSlot readStore found tagBound⟩

/-- Actual source success fixes the table installed at this occurrence. The
returned handle, captured values and poststate all come from that execution.
The caller's encoding premise relates only the physical capture fields. -/
theorem source_returned {S E : Type}
    (oracles : List (CheckedOracle snapshot domains math))
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (checked : CheckedOracle snapshot domains math)
    (selected : oracles.find? (fun entry ↦ entry.declaration.signature == checked.declaration.signature) = some checked)
    (layout : Layout checked.declaration.inputs.dropLast) (references : CaptureLayout.References)
    (records : List (model.Value layout.recordType)) (record : model.Value layout.recordType)
    (location : OracleLocation) (roles : Nat → Nat) (holder : Nat) (receivers : List Nat)
    (captures : Values model.Value checked.declaration.inputs.dropLast) (rows leaves : Nat)
    (declared : OracleExecution.declaredRows checked.declaration.signature captures = some rows)
    (before : OracleRuntimeState model snapshot domains math S)
    (visible : OracleStore.visible before.self (roles holder) (receivers.map roles) = true)
    (encoded : Encodes references layout location rows leaves captures record) :
    let result := OracleExecution.operation model oracles base location before.self roles
      (.virtual checked.declaration.signature holder receivers)
      (ProtocolValue.embedComponents captures.present) before
    ∀ reply, result.outcome = .returned reply →
      reply = .cons (some (ProtocolValue.ofConcrete (.oracle checked.declaration.kind) location.anchor)) .nil ∧
      Stored checked layout references result.state.entries (records ++ [record])
        (layout.constructor, records.length) location rows leaves (roles holder) (receivers.map roles) captures := by
  dsimp only
  intro reply returned
  obtain ⟨sameReply, poststate⟩ := OracleExecution.virtual_returned oracles base checked
    checked.declaration.signature selected rfl location roles holder receivers captures rows declared
    before before.self rfl visible reply returned
  refine ⟨sameReply, ?_⟩
  exact (congrArg (fun state ↦ state.entries) poststate).symm ▸
    stored_append checked layout references before.entries records location rows leaves
      (roles holder) (receivers.map roles) captures record encoded

end Zkc.Realization.VirtualStorage
