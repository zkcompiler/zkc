module

public import Zkc.Realization.QuerySourceSuspension
public import Tests.QuerySourceContext

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.QueryNestedSource
open Zkc.Source Zkc.Source.Structured Zkc.Realization
open Zkc.Realization.QuerySavedSource OracleProcessData VirtualStorageInstallation

def innerReferences :=
  VirtualStorage.references checked layout references result.state.entries [record]

def outerLayout : VirtualStorage.Layout checked.declaration.inputs.dropLast :=
  ⟨9, "outer-record", "outer-reference", location 10,
    .cons (CaptureLayout.referenceType layout.referenceIdentity) .nil,
    .handle kind layout.referenceIdentity .nil⟩

def outerCaptures : Values model.Value checked.declaration.inputs.dropLast := .cons (anchor 9) .nil
def outerRecord : model.Value outerLayout.recordType := (4, 2, 4, (8, 0, ()), ())

theorem outer_encoded :
    VirtualStorage.Encodes innerReferences outerLayout
      (location 10) 2 4 outerCaptures outerRecord :=
  ⟨rfl, .cons (8, 0, ()) .nil,
    ⟨⟨rfl, rfl, location 9, 2, 2, 0, [1], captures, rfl, installed⟩, trivial⟩, rfl⟩

/-- A second real source construction captures the first virtual handle.
Both levels use the original checked body; only their installed captures differ. -/
def outerResult := OracleExecution.operation model [checked] (base none) (location 10)
  result.state.self id (.virtual checked.declaration.signature 0 [1])
  (ProtocolValue.embedComponents outerCaptures.present) result.state

theorem outer_returned : outerResult.outcome = .returned
    (.cons (some (ProtocolValue.ofConcrete (.oracle kind) (anchor 10))) .nil) := by
  unfold outerResult
  rw [poststate]
  simp [OracleExecution.operation, before, OracleStore.visible,
    OracleExecution.capturesPresent_embed (model := model) outerCaptures]
  rfl

theorem outer_poststate : outerResult.state = {result.state with entries :=
    ⟨kind.answer, VirtualStorage.table checked (location 10) 2 0 [1] outerCaptures⟩ ::
      result.state.entries} :=
  (OracleExecution.virtual_returned [checked] (base none) checked checked.declaration.signature
    (by kernel_rfl) rfl (location 10) id 0 [1] outerCaptures 2 (by kernel_rfl)
    result.state result.state.self rfl (by rw [poststate]; decide) _ outer_returned).2

def outerFrame : QueryContinuation.Frame := ⟨0, 0, 0, 0, []⟩

def outerParent : Parent outerLayout innerReferences outerResult.state.entries
    [outerRecord] outerFrame :=
  ⟨location 10, 2, 4, 0, [1], outerCaptures, by kernel_rfl,
    (VirtualStorage.source_returned [checked] (base none) checked (by kernel_rfl)
      outerLayout innerReferences [] outerRecord (location 10) id 0 [1] outerCaptures 2 4
      (by kernel_rfl) result.state (by rw [poststate]; decide) outer_encoded _ outer_returned).2⟩

def outerContext : SourceContext outerParent 1 where
  older := result.state.entries
  located := by
    change OracleStore.Located outerResult.state.entries
      (VirtualStorage.table checked (location 10) 2 0 [1] outerCaptures) result.state.entries
    rw [outer_poststate]
    exact .head _ _
  reachable := result_reachable
  smaller := by rw [outer_poststate]; simp

abbrev calls := QuerySourceContext.calls
abbrev innerParent := QuerySourceContext.parent
abbrev innerContext := QuerySourceContext.context
abbrev root := outerParent.request (location 20) []
abbrev child (ordinal : Nat) := QuerySourceContinuation.child (anchor 9) 0 ordinal
abbrev innerRoot (ordinal : Nat) := root.expand (child ordinal)
abbrev leaf (outer inner : Nat) :=
  (innerRoot outer).expand (QuerySourceContext.child inner)

/-- Each leaf still reaches the existing base operation, with both enclosing
source occurrences in its expansion path. No provider is fixed by this law. -/
theorem leaf_return (outer inner provider after count phase answer event : Nat) :
    PIR.Reaches calls
      (innerContext.operations (innerRoot outer).location (innerRoot outer).expansion
        (QuerySourceContext.child inner) (provider, count)) phase
      (.done ⟨.returned answer, (after, count + 1),
        [.query (leaf outer inner), .provider event]⟩) (phase + 1) := by
  change PIR.Reaches calls
    (.call (I := OracleProcess.Interface model Nat Nat) (.inr (leaf outer inner), provider)
      (fun reply ↦ .done (⟨reply.outcome, (reply.state, count + 1),
        .query (leaf outer inner) :: reply.events.map OracleEvent.provider⟩ :
          PIR.Execution (Nat × Nat) (OracleEvent Nat) Nat))) phase _ (phase + 1)
  exact .step (P := calls) (.inr (leaf outer inner), provider) _ phase
    ⟨.returned answer, after, [event]⟩ _ _ (.refl _ _)

/-- The one installed inner body is reused at two distinct actual outer calls.
Its execution includes both leaves even though it returns only the second. -/
theorem inner_return (ordinal provider first after count phase event : Nat) :
    PIR.Reaches calls (outerContext.operations (location 20) [] (child ordinal) (provider, count))
      phase (.done ⟨.returned (20 : Nat), (after, count + 3),
        [.query (innerRoot ordinal), .query (leaf ordinal 0), .provider event,
          .query (leaf ordinal 1), .provider (event + 1)]⟩) (phase + 2) := by
  have start := Zkc.Realization.QuerySourceContinuation.Produced.initial
    (interaction := calls)
    (operations := innerContext.operations
      (innerRoot ordinal).location (innerRoot ordinal).expansion)
    (source := innerParent.body) (initialState := (provider, count + 1)) (initialPhase := phase)
    QuerySourceContinuation.arenas
  have source : innerParent.body = QuerySourceContinuation.source (anchor 0) 0 := by kernel_rfl
  rw [source, QuerySourceContinuation.source_body] at start
  have left := start.resume (slot := 0)
    (leaf_return ordinal 0 provider first (count + 1) phase 10 event) rfl
  have right := left.resume (slot := 1)
    (leaf_return ordinal 1 first after (count + 2) (phase + 1) 20 (event + 1)) rfl
  rw [← QuerySourceContinuation.source_body, ← source] at right
  exact innerContext.completed (innerRoot ordinal).location (innerRoot ordinal).expansion
    (by decide) (by decide) (by decide) calls (provider, count) (after, count + 3)
    phase (phase + 2) QuerySourceContinuation.arenas [0, 1] (20 : Nat) _ right

def outerNext (_ : model.Value (child 0).kind.answer) :
    PIR.Process (oracleReadInterface model.toCarriers) (Values (Component model.Value) [.index]) :=
  PIR.Process.call (I := oracleReadInterface model.toCarriers) (child 1)
    (fun answer ↦ .done (.cons (some answer) .nil))

def innerNext (_ : model.Value (QuerySourceContext.child 0).kind.answer) :
    PIR.Process (oracleReadInterface model.toCarriers) (Values (Component model.Value) [.index]) :=
  PIR.Process.call (I := oracleReadInterface model.toCarriers) (QuerySourceContext.child 1)
    (fun answer ↦ .done (.cons (some answer) .nil))

def outerStart : Zkc.Realization.QuerySourceContinuation.Produced calls
    (outerContext.operations (location 20) []) outerParent.body (0, 1) 0
    QuerySourceContinuation.arenas (.call (child 0) outerNext) [] (0, 1) 0 [] := by
  have source : outerParent.body = .call (child 0) outerNext := by kernel_rfl
  rw [← source]
  exact .initial _

def innerStart : Zkc.Realization.QuerySourceContinuation.Produced calls
    (innerContext.operations (innerRoot 0).location (innerRoot 0).expansion)
    innerParent.body (0, 2) 0 QuerySourceContinuation.arenas
    (.call (QuerySourceContext.child 0) innerNext) [] (0, 2) 0 [] := by
  have source : innerParent.body = .call (QuerySourceContext.child 0) innerNext := by kernel_rfl
  rw [← source]
  exact .initial _

/-- Suspending at the first leaf attaches both installed parents in their
actual order. The same bind rule works at any nesting depth. -/
theorem nested_suspension :
    PIR.Reaches calls
      (OracleProcess.answer model 1 outerResult.state.entries root (0, 0)) 0
      (((innerContext.operations (innerRoot 0).location (innerRoot 0).expansion
        (QuerySourceContext.child 0) (0, 2)).bind
          (innerContext.restore (innerRoot 0).location (innerRoot 0).expansion innerNext [])).bind
            (outerContext.restore (location 20) [] outerNext [])) 0 :=
  (outerContext.suspended (location 20) [] (by decide) (by decide) (by decide)
    calls (initial := (0, 0)) outerStart).trans
      ((innerContext.suspended (innerRoot 0).location (innerRoot 0).expansion
        (by decide) (by decide) (by decide) calls (initial := (0, 1)) innerStart).bind _)

def savedOuterRecord : model.Value (QueryContinuation.layout "outer-frame" 0).type :=
  (0, 0, 0, 0, ())

noncomputable def savedOuter : Saved "outer-frame" 0 [savedOuterRecord] 0
    QuerySourceContinuation.arenas outerParent (child 0) outerNext :=
  save [] (show QueryContinuation.Encodes "outer-frame" 0 outerFrame savedOuterRecord
    from ⟨(), rfl, rfl⟩) outerStart.cursor

/-- Restoring the actual saved frame after its nested child returns also
recovers the source derivation, including the two child provider operations. -/
theorem restored_outer (program : Program) (context : Zkc.Construction.Context) :
    let environment : Zkc.Construction.Domain.Environment model.toCarriers :=
      [.data ⟨.sequence (QueryContinuation.layout "outer-frame" 0).type, rfl, [savedOuterRecord]⟩,
        .data (.index 0)]
    Nonempty (Zkc.Realization.QuerySourceContinuation.Produced calls
      (outerContext.operations (location 20) []) outerParent.body (0, 1) 0
      QuerySourceContinuation.arenas (outerNext (20 : Nat)) [1] (22, 4) 2
      [.query (innerRoot 0), .query (leaf 0 0), .provider 4, .query (leaf 0 1), .provider 5]) ∧
    ∃ stored, QueryContinuation.Encodes "outer-frame" 0 outerFrame stored ∧
      Nonempty (Zkc.Construction.Original.Simulation Eq (fun _ live ↦ environment <+: live)
        (.done (environment ++
          [.data ⟨(QueryContinuation.layout "outer-frame" 0).type, rfl, stored⟩] ++
          outerFrame.values.map (fun value ↦ Zkc.Construction.Domain.Value.data (.index value))))
        (Zkc.Construction.Domain.evaluate model program context
          (QueryContinuation.loadInstructions "outer-frame" 0 environment.length 0 1)
          environment)) :=
  savedOuter.load_produced outerStart (inner_return 0 0 11 22 1 0 4)
    (answerSlot := 1) rfl _ 0 1 rfl program context

/-- The root uses the same inner proof twice. Restoring the first physical
frame supplies the progress used for the second call. The complete tree has
seven logical query occurrences and four provider operations, without deduplication. -/
theorem nested_return (program : Program) (context : Zkc.Construction.Context) :
    PIR.Reaches calls
      (OracleProcess.answer model 1 outerResult.state.entries root (0, 0)) 0
      (.done ⟨.returned (20 : Nat), (44, 7),
        [.query root, .query (innerRoot 0), .query (leaf 0 0), .provider 4,
          .query (leaf 0 1), .provider 5, .query (innerRoot 1),
          .query (leaf 1 0), .provider 6, .query (leaf 1 1), .provider 7]⟩) 4 := by
  obtain ⟨first⟩ := (restored_outer program context).1
  have second := first.resume (slot := 1) (inner_return 1 22 33 44 4 2 6) rfl
  exact outerContext.completed (location 20) [] (by decide) (by decide) (by decide)
    calls (0, 0) (44, 7) 0 4 QuerySourceContinuation.arenas [1, 1] (20 : Nat) _ second

/-- A stop at the first nested leaf propagates through both actual parents.
Its poststate, three reached query occurrences and provider log are retained;
neither parent's later child runs. -/
theorem nested_stopped (reason : PIR.Stop) :
    PIR.Reaches calls
      (OracleProcess.answer model 1 outerResult.state.entries root (0, 0)) 0
      (.done ⟨.stopped reason, (11, 3),
        [.query root, .query (innerRoot 0), .query (leaf 0 0), .provider 4]⟩) 1 := by
  have stopped : PIR.Reaches calls
      (innerContext.operations (innerRoot 0).location (innerRoot 0).expansion
        (QuerySourceContext.child 0) (0, 2)) 0
      (.done ⟨.stopped reason, (11, 3), [.query (leaf 0 0), .provider 4]⟩) 1 := by
    change PIR.Reaches calls
      (.call (I := OracleProcess.Interface model Nat Nat) (.inr (leaf 0 0), 0)
        (fun reply ↦ .done (⟨reply.outcome, (reply.state, 3),
          .query (leaf 0 0) :: reply.events.map OracleEvent.provider⟩ :
            PIR.Execution (Nat × Nat) (OracleEvent Nat) Nat))) 0 _ 1
    exact .step (P := calls) (.inr (leaf 0 0), 0) _ 0
      ⟨.stopped reason, 11, [4]⟩ _ _ (.refl _ _)
  have inner := innerContext.child_reached (innerRoot 0).location (innerRoot 0).expansion
    (by decide) (by decide) (by decide) calls (initial := (0, 1)) innerStart _ stopped
  rw [SourceContext.restore_stopped] at inner
  have outer := outerContext.child_reached (location 20) []
    (by decide) (by decide) (by decide) calls (initial := (0, 0)) outerStart _ inner
  rw [SourceContext.restore_stopped] at outer
  exact outer

/-- Equal-typed, equal-valued nested queries still retain distinct enclosing
occurrences. Flattening their expansion paths would change the source event. -/
theorem nested_paths_distinct : (leaf 0 0).expansion ≠ (leaf 1 0).expansion := by decide +kernel

/-- An actual saved slot cannot replace its root continuation with a nested
continuation, even if both would eventually return the same numeric value. -/
theorem outer_continuation_swap_rejected :
    ¬ QueryContinuation.Stored "outer-frame" 0 [savedOuterRecord] 0
      {outerFrame with outer := 1} := by
  intro swapped
  have same := congrArg QueryContinuation.Frame.outer (savedOuter.decoded swapped)
  contradiction

#print axioms outerParent
#print axioms inner_return
#print axioms nested_suspension
#print axioms restored_outer
#print axioms nested_return
#print axioms nested_stopped
#print axioms nested_paths_distinct
#print axioms outer_continuation_swap_rejected
end Tests.QueryNestedSource
