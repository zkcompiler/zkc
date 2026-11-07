module

public import Zkc.Realization.VirtualStorageLifetime
public import Zkc.Realization.ClearStorageCaptures
public import Tests.OracleProcessData

@[expose] public section

set_option backward.isDefEq.respectTransparency false
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

/-- A second actual construction may have the same body and captures, but it
has a distinct anchor. It cannot change the earlier physical reference. -/
def later := OracleExecution.operation model [checked] (base none) (location 10) result.state.self id
  (.virtual checked.declaration.signature 0 [1]) (ProtocolValue.embedComponents captures.present) result.state

set_option backward.isDefEq.respectTransparency false in
theorem later_returned : later.outcome = .returned
    (.cons (some (ProtocolValue.ofConcrete (.oracle kind) (anchor 10))) .nil) := by
  unfold later
  rw [poststate]
  simp [OracleExecution.operation, before, OracleStore.visible,
    OracleExecution.capturesPresent_embed (model := model) captures]
  rfl

/-- Registry preservation comes from the actual operation law, including
its stopped executions, rather than an extra protocol-author premise. -/
theorem retained : VirtualStorage.Stored checked layout references later.state.entries [record]
    (8, 0) (location 9) 2 2 0 [1] captures :=
  installed.transport
    (OracleExecution.operation_extension model [checked] (base none) (location 10)
      result.state.self id (.virtual checked.declaration.signature 0 [1])
      (ProtocolValue.embedComponents captures.present) result.state).fresh
    (List.prefix_refl _) (fun _ _ _ _ found ↦ found)

def virtualReferences := VirtualStorage.references checked layout references later.state.entries [record]

theorem earlier_reference : virtualReferences kind layout.referenceIdentity (anchor 9) (8, 0) :=
  ⟨rfl, rfl, location 9, 2, 2, 0, [1], captures, rfl, retained⟩

/-- The later source closure is real and has equal captures; that still
cannot reassociate the first physical slot with its anchor. -/
theorem wrong_closure_refused :
    ¬ virtualReferences kind layout.referenceIdentity (anchor 10) (8, 0) := by
  intro wrong
  have equal := VirtualStorage.references_unambiguous checked layout references
    later.state.entries [record] kind layout.referenceIdentity (anchor 9) (anchor 10) (8, 0)
    earlier_reference wrong
  have different : anchor 9 ≠ anchor 10 := by decide +kernel
  exact different equal

theorem before_reachable : OracleStore.Reachable before.self before.entries :=
  .inserted baseTable .empty rfl trivial

theorem result_reachable : OracleStore.Reachable before.self result.state.entries :=
  (OracleExecution.operation_extension model [checked] (base none) (location 9)
    before.self id (.virtual checked.declaration.signature 0 [1])
    (ProtocolValue.embedComponents captures.present) before).reachable before_reachable

theorem later_reachable : OracleStore.Reachable result.state.self later.state.entries :=
  (OracleExecution.operation_extension model [checked] (base none) (location 10)
    result.state.self id (.virtual checked.declaration.signature 0 [1])
    (ProtocolValue.embedComponents captures.present) result.state).reachable
      (by simpa only [poststate] using result_reachable)

/-- The general rule derives a valid source context from reached storage.
No protocol author provides a virtual dependency graph. -/
theorem recovered_context :
    ∃ older, OracleStore.Located later.state.entries
        (VirtualStorage.table checked (location 9) 2 0 [1] captures) older ∧
      OracleStore.Reachable result.state.self older ∧
      OracleStore.PayloadBefore result.state.self older
        (VirtualStorage.table checked (location 9) 2 0 [1] captures) ∧
      older.length < later.state.entries.length :=
  retained.source_context later_reachable

/-- The retained context is the exact registry from before the first
construction, even after a second real construction has succeeded. -/
theorem retained_context : OracleStore.Located later.state.entries
    (VirtualStorage.table checked (location 9) 2 0 [1] captures) before.entries := by
  have first : OracleStore.Located result.state.entries
      (VirtualStorage.table checked (location 9) 2 0 [1] captures) before.entries := by
    rw [poststate]
    exact .head _ _
  exact first.transport
    (OracleExecution.operation_extension model [checked] (base none) (location 10)
      result.state.self id (.virtual checked.declaration.signature 0 [1])
      (ProtocolValue.embedComponents captures.present) result.state).fresh

def parentQuery : OracleRead := ⟨kind, anchor 9, 0, location 20, []⟩

/-- The same reached installation exposes its open computation before any
provider is selected. A later real construction cannot replace the older
registry used by the two child continuations. -/
theorem read_process_expands {E : Type} (state : Provider × Nat) :
    OracleProcess.answer (E := E) model 1 later.state.entries parentQuery state =
      let args : Values model.Value checked.declaration.inputs :=
        (show checked.declaration.inputs = checked.declaration.inputs.dropLast ++ [.index]
          by kernel_rfl).symm ▸ captures.append (.cons parentQuery.position .nil)
      OracleProcess.mapResult (fun result ↦
        ⟨match result.outcome with
          | .stopped reason => .stopped reason
          | .returned values => match values.get .here with
            | none => .stopped .incomplete
            | some value => .returned value,
          result.state, .query parentQuery :: result.events⟩)
        (OracleProcess.present (fun child current ↦
            OracleProcess.answer model 1 before.entries (parentQuery.expand child) current)
          (checked.denote model args.present) (state.1, state.2 + 1)) := by
  refine (OracleProcess.answer_virtual checked parentQuery rfl 2 0 [1] captures retained_context
    (by kernel_rfl) 1 (by decide) (by decide) (by decide) state).trans ?_
  dsimp only
  congr 1
  funext result
  split <;> simp_all
  split <;> simp_all

def readRetained (failure : Option (Nat × PIR.Stop)) :
    PIR.Execution (Provider × Nat) (OracleEvent ProviderEvent) Nat :=
  OracleStore.answer model (base failure) 1 later.state.entries parentQuery (({} : Provider), 0)

/-- The library exposes all outcomes of the actual checked body on the
retained prefix. This equation is independent of the provider's answers. -/
theorem read_expands (failure : Option (Nat × PIR.Stop)) :
    readRetained failure =
      let args : Values model.Value checked.declaration.inputs :=
        (show checked.declaration.inputs = checked.declaration.inputs.dropLast ++ [.index]
          by kernel_rfl).symm ▸ captures.append (.cons parentQuery.position .nil)
      let body := (checked.denote model args.present).run
        (fun child current ↦ OracleStore.answer model (base failure) 1 before.entries
          (parentQuery.expand child) current) (({} : Provider), 1)
      ⟨match body.outcome with
        | .stopped reason => .stopped reason
        | .returned values => match values.get .here with
          | none => .stopped .incomplete
          | some value => .returned value,
        body.state, .query parentQuery :: body.events⟩ := by
  refine (retained_context.virtual_answer checked parentQuery rfl 2 0 [1] captures
    (by kernel_rfl) (base failure) 1 (by decide) (by decide) (by decide)
    (({} : Provider), 0)).trans ?_
  dsimp only
  congr 1
  split <;> simp_all
  split <;> simp_all

theorem retained_read : (readRetained none).outcome = .returned 10 ∧
    (readRetained none).state.1.calls = 2 ∧ (readRetained none).state.1.hits = 1 ∧
    (readRetained none).state.2 = 3 := by
  rw [read_expands]
  decide +kernel

/-- A stopped first child prevents the second read. Any provider work and
its reached query charge remain in the stopped record. -/
theorem first_child_stop (reason : PIR.Stop) :
    (readRetained (some (1, reason))).outcome = .stopped reason ∧
    (readRetained (some (1, reason))).state.1.calls = 1 ∧
    (readRetained (some (1, reason))).state.2 = 2 := by
  rw [read_expands]
  cases reason <;> decide +kernel

/-- The second child's stop retains the first child's work and repeated-read
cache hit. It cannot be mistaken for successful refusal of a mutation. -/
theorem second_child_stop (reason : PIR.Stop) :
    (readRetained (some (2, reason))).outcome = .stopped reason ∧
    (readRetained (some (2, reason))).state.1.calls = 2 ∧
    (readRetained (some (2, reason))).state.1.hits = 1 ∧
    (readRetained (some (2, reason))).state.2 = 3 := by
  rw [read_expands]
  cases reason <;> decide +kernel

#print axioms recovered_context
#print axioms read_process_expands
#print axioms VirtualStorage.Stored.source_process
#print axioms read_expands
#print axioms retained_read
#print axioms first_child_stop
#print axioms second_child_stop

#print axioms retained
#print axioms later_returned
#print axioms wrong_closure_refused

#print axioms installed
#print axioms lookup
#print axioms duplicate_refused
#print axioms VirtualStorage.source_returned
end Tests.VirtualStorageInstallation
