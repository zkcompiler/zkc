module

public import Zkc.Realization.QueryController
public import Tests.QueryNestedSource
public import Tests.QuerySourceStack
public import Tests.QueryWork

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.QueryController
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization
open OracleProcessData VirtualStorageInstallation QueryController

abbrev source := OracleProcess.answer (E := Nat) model 1
  QueryNestedSource.outerResult.state.entries QueryNestedSource.root (0, 0)
abbrev calls := QueryNestedSource.calls
abbrev arenas := QuerySourceContinuation.arenas

def references := VirtualStorage.references checked QueryNestedSource.outerLayout
  QueryNestedSource.innerReferences QueryNestedSource.outerResult.state.entries
  [QueryNestedSource.outerRecord]

noncomputable def initial : Pending (snapshot := snapshot) (domains := []) (math := math)
    (self := 1) calls source 0 references (fun _ ↦ 0) (Header.initial 9 0 0) :=
  pending_initial calls QueryNestedSource.outerResult.state.entries QueryNestedSource.root
    (0, 0) 0 references (fun _ ↦ 0) rfl "outer-reference" 9 0
    ⟨rfl, rfl, location 10, 2, 4, 0, [1], QueryNestedSource.outerCaptures,
      rfl, QueryNestedSource.outerParent.installed⟩

def events : List (OracleEvent Nat) :=
  [.query QueryNestedSource.root, .query (QueryNestedSource.innerRoot 0),
    .query (QueryNestedSource.leaf 0 0), .provider 4,
    .query (QueryNestedSource.leaf 0 1), .provider 5,
    .query (QueryNestedSource.innerRoot 1),
    .query (QueryNestedSource.leaf 1 0), .provider 6,
    .query (QueryNestedSource.leaf 1 1), .provider 7]

def header : Header := ⟨⟨9, 0, 0, 0, 0⟩, 0, 3, 1⟩

/-- The actual nested source execution supplies the result, state and log.
The root cell is different from the first equal-typed answer in the arena.
This fixture exercises the finish continuation, not the dispatch/range proof. -/
noncomputable def completed (program : Program) (context : Context) :
    Returned (snapshot := snapshot) (domains := []) (math := math) (self := 1)
      calls source 0 (fun _ ↦ 0) arenas header := by
  let result := initial.returned arenas 1 (20 : Nat) (44, 7) events 4
    (QueryNestedSource.nested_return program context) rfl
  exact ⟨Returned.kind result, Returned.answer result, Returned.state result,
    Returned.phase result, Returned.events result, Returned.kind_eq result,
    Returned.cell result, Returned.stack result, Returned.reached result⟩

def environment : Domain.Environment model.toCarriers :=
  header.encode [.data ⟨.sequence .index, rfl, ([10, 20] : List Nat)⟩]

def finish : QueryFinish.Placement := ⟨9, 6, 5, 8, 7, "completed", "root-kind"⟩

/-- The output certificate now selects the same answer as the original
root, with all four provider calls and both saved nesting levels retained.
The finish body is evaluated by the existing construction semantics. -/
theorem source_output (program : Program) (context : Context) :
    ∃ answer : model.Value .index,
      PIR.Reaches calls source 0 (.done ⟨.returned answer, (44, 7), events⟩) 4 ∧
      Nonempty (Original.Simulation
        (fun value output ↦ output = [.data ⟨.index, rfl, value⟩])
        (fun _ frame ↦ environment <+: frame) (.done answer)
        ((Domain.evaluate model program context (QueryFinish.instructions .index finish)
          environment).bind fun final ↦ match Domain.read final [13] with
          | some values => .done values
          | none => .halt .refused)) := by
  exact (completed program context).output rfl rfl rfl
    ⟨.index, finish, rfl, rfl⟩ rfl program context rfl environment rfl rfl rfl rfl rfl

/-- Current stores, phase and exact work history are checked together. A
completed phase cannot be paired with the initial zero-step history. -/
theorem premature_completed_work :
    ¬ ∃ work : Work (model := model) Tests.QueryWork.repeated header
        (fun _ ↦ []) (fun _ _ ↦ []), work.steps = 0 := by
  rintro ⟨work, zero⟩
  have totals := work.completed rfl
  have nodes : Tests.QueryWork.repeated.nodes = 3 := by decide
  omega

/-- A physical arena cannot silently contain an uncharged extra answer. -/
theorem oversized_arena :
    ¬ Nonempty (Work (model := model) .base header arenas (fun _ _ ↦ [])) := by
  rintro ⟨work⟩
  have bounded := (work.bounds (Nat.le_refl _) (Nat.le_refl _)).2.2.1 kind
  change 2 ≤ 1 at bounded
  omega

def nestedShape : QueryWork.Shape :=
  .virtual [Tests.QueryWork.repeated, Tests.QueryWork.repeated]

def leafHeader : Header := ⟨⟨7, 0, 0, 2, 0⟩, 0, 2, 0⟩

def leafFrames (identity : String) : (count : Nat) →
    List (model.Value (QueryContinuation.layout identity count).type)
  | 0 => if identity = "inner-frame" then [(1, 0, 0, 0, ())]
    else if identity = "outer-frame" then [(0, 0, 0, 0, ())] else []
  | _ + 1 => []

noncomputable def savedOuter : QuerySavedSource.Saved "outer-frame" 0
    [QueryNestedSource.savedOuterRecord] 0 (fun _ ↦ [])
    QueryNestedSource.outerParent (QueryNestedSource.child 0) QueryNestedSource.outerNext :=
  QuerySavedSource.save [] (show QueryContinuation.Encodes "outer-frame" 0
    QueryNestedSource.outerFrame QueryNestedSource.savedOuterRecord from ⟨(), rfl, rfl⟩) (by
    convert Zkc.Realization.QuerySourceContinuation.initial (fun _ ↦ [])
      QueryNestedSource.outerParent.body using 1
    all_goals kernel_rfl)

noncomputable def savedInner : QuerySavedSource.Saved "inner-frame" 0
    [QuerySourceStack.innerRecord] 0 (fun _ ↦ [])
    QuerySourceStack.innerParent (QuerySourceContext.child 0) QueryNestedSource.innerNext :=
  QuerySavedSource.save [] (show QueryContinuation.Encodes "inner-frame" 0
    QuerySourceStack.innerFrame QuerySourceStack.innerRecord from ⟨(), rfl, rfl⟩) (by
    convert Zkc.Realization.QuerySourceContinuation.initial (fun _ ↦ [])
      QuerySourceStack.innerParent.body using 1
    all_goals kernel_rfl)

noncomputable def leafStack : Zkc.Realization.QuerySourceStack.Stack
    model snapshot [] math 1 Nat Nat kind kind 2 0 :=
  .saved QuerySourceStack.innerContext savedInner
    QuerySourceStack.first.location QuerySourceStack.first.expansion [] 1
    (.saved QueryNestedSource.outerContext savedOuter (location 20) [] [] 0 .root)

theorem leaf_resident : leafStack.Resident (fun _ ↦ []) leafFrames :=
  ⟨List.prefix_refl _, fun _ ↦ List.prefix_refl _,
    List.prefix_refl _, fun _ ↦ List.prefix_refl _, trivial⟩

/-- The earlier isolated source fixture deliberately used an existing answer
arena. Such a saved snapshot cannot be installed over the controller's empty
current arena, even though its source continuation has the same result. -/
theorem historical_answers_cannot_disappear :
    ¬ QuerySourceStack.nestedStack.Resident (fun _ ↦ []) leafFrames := by
  intro resident
  have bound := (resident.2.1 kind).length_le
  change 2 ≤ 0 at bound
  omega

theorem saved_frames_cannot_disappear :
    ¬ leafStack.Resident (fun _ ↦ []) (fun _ _ ↦ []) := by
  intro resident
  have bound := resident.1.length_le
  change 1 ≤ 0 at bound
  omega

noncomputable def leafPending : Pending (snapshot := snapshot) (domains := []) (math := math)
    (self := 1) calls source 0 VirtualStorageInstallation.references (fun _ ↦ 0) leafHeader where
  request := QuerySourceStack.leaf
  entries := before.entries
  state := (0, 2)
  phase := 0
  referenceIdentity := "parent-reference"
  reference := ⟨rfl, rfl, word, rfl, parent_stored⟩
  position := rfl
  kind := rfl
  stack := leafStack
  reached := QuerySourceStack.nested_progress

def leafWork : Work (model := model) nestedShape leafHeader (fun _ ↦ []) leafFrames where
  position := .request [[.base], [Tests.QueryWork.repeated]]
  steps := 3
  replies := 0
  answers := 0
  saves := 2
  history := .advance (.advance (.advance (.nil _) (.children _ _ _))
    (.children _ _ _)) (.base _)
  phase := rfl
  answerBound := fun _ ↦ Nat.le_refl _
  frameBound := by
    intro identity count
    cases count with
    | zero => simp only [leafFrames]; split_ifs <;> simp
    | succ => exact Nat.zero_le _

def afterLeaf : (kind : OracleKind) → List (model.Value kind.answer)
  | .table .index _ => ([10] : List Nat)
  | _ => []

def savedStores : Domain.Environment model.toCarriers :=
  [.data ⟨.sequence (QueryContinuation.layout "inner-frame" 0).type, rfl,
      leafFrames "inner-frame" 0⟩,
   .data ⟨.sequence (QueryContinuation.layout "outer-frame" 0).type, rfl,
      leafFrames "outer-frame" 0⟩]

def responseEnvironment : Domain.Environment model.toCarriers :=
  leafHeader.encode ([.data ⟨.sequence .index, rfl, ([] : List Nat)⟩] ++ savedStores) ++
    [.data (.index 10)] ++ leafHeader.toCoordinates.values.map (fun value ↦ .data (.index value))

def responsePlacement : QueryResumption.Placement :=
  ⟨17, 6, 5, ⟨0, 1, 2, 3, 4⟩, ⟨12, 13, 14, 15, 16⟩, 8, 11,
    "request", "kind", !["constructor", "instance", "position", "continuation", "frame"]⟩

/-- One application connects the whole resumption body, actual nested child
execution and root-derived capacity. Its two saved frames remain in order;
the reply adds exactly one cell and preserves the linked source continuation.
This still leaves enter/return dispatch and both enclosing ranges to connect. -/
theorem nested_resume (program : Program) (context : Context) :
    let nextHeader := {leafHeader with phase := 1, answer := 0}
    Nonempty {result : Returned (snapshot := snapshot) (domains := []) (math := math)
      (self := 1) calls source 0 (fun _ ↦ 0) afterLeaf nextHeader //
      (Returned.stack result).Resident afterLeaf leafFrames} ∧
    Nonempty (Work (model := model) nestedShape nextHeader afterLeaf leafFrames) ∧
    Nonempty (Original.Simulation Eq (fun _ frame ↦ responseEnvironment <+: frame)
      (.done (nextHeader.encode ([.data ⟨.sequence .index, rfl, ([10] : List Nat)⟩] ++ savedStores)))
      ((Domain.evaluate model program context
        (QueryResumption.instructions .index 0 responsePlacement) responseEnvironment).bind
        fun result ↦ match Domain.read result
          (QueryResumption.outputReferences responsePlacement [] [9, 10]) with
          | some values => .done values
          | none => .halt .refused)) :=
  leafPending.resume (nextArenas := afterLeaf) leafWork
    [[.base], [Tests.QueryWork.repeated]] rfl (by decide)
    (10 : Nat) (11, 3) [.query QuerySourceStack.leaf, .provider 4] 1
    (QueryNestedSource.leaf_return 0 0 0 11 2 0 10 4) rfl leaf_resident
    (fun _ ↦ List.nil_prefix)
    (by intro kind; cases kind with | table row shape => cases row <;> simp [afterLeaf])
    program context responsePlacement
    (QueryResumption.instructions .index 0 responsePlacement) rfl rfl (by decide)
    (by simp [QueryResumption.Coordinates.Bounded, QueryResumption.Coordinates.values,
      leafHeader, indexLimit])
    responseEnvironment rfl [] [9, 10] [] savedStores rfl rfl
    (.cons rfl rfl (.cons rfl rfl (.cons rfl rfl (.cons rfl rfl (.cons rfl rfl .nil)))))
    rfl rfl rfl rfl

#print axioms source_output
#print axioms premature_completed_work
#print axioms oversized_arena
#print axioms nested_resume
#print axioms historical_answers_cannot_disappear
#print axioms saved_frames_cannot_disappear
end Tests.QueryController
