module

public import Zkc.Realization.VirtualStorageInstallation
public import Zkc.Realization.ClearStorageCaptures
public import Tests.OracleProcessData

@[expose] public section

namespace Tests.VirtualStorageInstallation
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Realization
open OracleProcessData

abbrev parentLayout : ClearStorage.Layout kind :=
  ⟨7, "parent-record", "parent-reference", location 0, 0, [1]⟩

def word : PublishedWords.Word model kind.answer :=
  ⟨kind, anchor 0, 2, 0, [1], location 0, ([10, 20] : List Nat)⟩

def parentRecord : model.Value parentLayout.recordType := (4, 2, 1, [10, 20], ())
def words : PublishedWords.Table model := [⟨kind.answer, word⟩]

def references : CaptureLayout.References := ClearStorage.references parentLayout words [parentRecord]

theorem parent_stored : ClearStorage.Stored parentLayout words [parentRecord] (7, 0) word :=
  ClearStorage.stored_append parentLayout [] [] word parentRecord ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

abbrev fields : ProductFields := .cons (CaptureLayout.referenceType parentLayout.referenceIdentity) .nil

def layout : VirtualStorage.Layout checked.declaration.inputs.dropLast :=
  ⟨8, "virtual-record", "virtual-reference", location 9, fields,
    .handle kind parentLayout.referenceIdentity .nil⟩

def captures : Values model.Value checked.declaration.inputs.dropLast := .cons (anchor 0) .nil
def record : model.Value layout.recordType := (4, 2, 2, (7, 0, ()), ())

theorem encoded : VirtualStorage.Encodes references layout (location 9) 2 2 captures record :=
  ⟨rfl, .cons (7, 0, ()) .nil, ⟨⟨rfl, rfl, word, rfl, parent_stored⟩, trivial⟩, rfl⟩

def before : OracleRuntimeState model snapshot [] math Provider :=
  ⟨1, [⟨.index, baseTable⟩], {}, 0⟩

def result := OracleExecution.operation model [checked] (base none) (location 9) before.self id
  (.virtual checked.declaration.signature 0 [1]) (ProtocolValue.embedComponents captures.present) before

set_option backward.isDefEq.respectTransparency false in
/-- The actual checked source instruction, not a supplied success predicate,
returns the handle for this exact construction occurrence. -/
theorem returned : result.outcome = .returned
    (.cons (some (ProtocolValue.ofConcrete (.oracle kind) (anchor 9))) .nil) := by
  simp [result, OracleExecution.operation, before, OracleStore.visible,
    OracleExecution.capturesPresent_embed (model := model) captures]
  rfl

/-- The common source-return rule connects the actual registry insertion and
captured parent to the appended physical record. -/
theorem installed : VirtualStorage.Stored checked layout references result.state.entries [record]
    (8, 0) (location 9) 2 2 0 [1] captures := by
  have connected := VirtualStorage.source_returned [checked] (base none) checked
    (by kernel_rfl) layout references [] record (location 9) id 0 [1] captures 2 2
    (by kernel_rfl) before (by kernel_rfl) encoded _ returned
  exact connected.2

/-- The installed source closure is the one recovered by the actual lookup. -/
theorem lookup (program : Program) (context : Construction.Context) :
    let environment : Construction.Domain.Environment model.toCarriers :=
      [.data (.index 8), .data (.index 0), .data ⟨.sequence layout.recordType, rfl, [record]⟩]
    ∃ stored, VirtualStorage.Encodes references layout (location 9) 2 2 captures stored ∧
      Nonempty (Construction.Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
        (.done (environment ++ [.data (.index 8), .data (.boolean true),
          .data ⟨layout.recordType, rfl, stored⟩]))
        (Construction.Domain.evaluate model program context
          (RecordLookup.instructions ⟨8, layout.recordType⟩ ⟨3, 0, 1, 2, "record"⟩) environment)) :=
  installed.lookup program context rfl _ 0 1 2 "record" rfl rfl rfl (by decide)

theorem poststate : result.state = {before with entries :=
    ⟨kind.answer, VirtualStorage.table checked (location 9) 2 0 [1] captures⟩ :: before.entries} :=
  (OracleExecution.virtual_returned [checked] (base none) checked checked.declaration.signature
    (by kernel_rfl) rfl (location 9) id 0 [1] captures 2 (by kernel_rfl)
    before before.self rfl (by kernel_rfl) _ returned).2

set_option backward.isDefEq.respectTransparency false in
/-- The same construction cannot run twice at the same dynamic location. -/
theorem duplicate_refused :
    (OracleExecution.operation model [checked] (base none) (location 9) before.self id
      (.virtual checked.declaration.signature 0 [1]) (ProtocolValue.embedComponents captures.present)
      result.state).outcome = .stopped .refused := by
  rw [poststate]
  simp [OracleExecution.operation, before, OracleStore.visible,
    OracleExecution.capturesPresent_embed (model := model) captures]
  rfl

#print axioms installed
#print axioms lookup
#print axioms duplicate_refused
#print axioms VirtualStorage.source_returned
end Tests.VirtualStorageInstallation
