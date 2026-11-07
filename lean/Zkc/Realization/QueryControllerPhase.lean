module

public import Zkc.Realization.QueryController
public import Zkc.Realization.QuerySourceWork

@[expose] public section

/-! The generated phase-only leaf and its complete state projection. Changing
the phase does not change the source suspension, returned answer, or stores.
The enclosing dispatch must establish its source/work case before using the
leaf; a literal Completed value alone does not establish query completion. -/
set_option autoImplicit false
namespace Zkc.Realization.QueryController
open Zkc.Source Zkc.Source.Structured Zkc.Construction

namespace Phase

def instructions (phase : Nat) : List Construction.Instruction :=
  [⟨.execute (.indexConstant phase), [], [.data .index], []⟩]

def output (state : List Nat) (start : Nat) : List Nat :=
  state.take 6 ++ start :: state.drop 7

structure Recognized (body : List Construction.Instruction) (returned : List Nat) where
  phase : Nat
  start : Nat
  state : List Nat
  exactBody : body = instructions phase
  exactOutput : returned = output state start

/-- Recognition fixes every returned coordinate, not just the new phase. -/
def recognize (start : Nat) (state : List Nat) (body : List Construction.Instruction)
    (returned : List Nat) : Option (Recognized body returned) := do
  let [instruction] := body | none
  let .execute (.indexConstant phase) := instruction.operation | none
  if exactBody : body = instructions phase then
    if exactOutput : returned = output state start then
      some ⟨phase, start, state, exactBody, exactOutput⟩
    else none
  else none

private theorem read_parts {carriers : Carriers} (environment : Domain.Environment carriers)
    (references : List Nat) (values : Domain.Environment carriers)
    (read : Domain.read environment references = some values) (count : Nat) :
    Domain.read environment (references.take count) = some (values.take count) ∧
      Domain.read environment (references.drop count) = some (values.drop count) := by
  induction references generalizing values count with
  | nil =>
      have empty : values = [] := Option.some.inj read.symm
      subst values
      simp [Domain.read]
  | cons reference references ih =>
      cases found : environment[reference]? with
      | none => simp [Domain.read, found] at read
      | some value =>
          cases tail : Domain.read environment references with
          | none =>
              simp only [Domain.read] at tail
              simp [Domain.read, found, tail] at read
          | some rest =>
              have tailMap := tail
              simp only [Domain.read] at tailMap
              have same : values = value :: rest := by
                apply Option.some.inj
                simpa [Domain.read, found, tailMap] using read.symm
              subst values
              cases count with
              | zero => exact ⟨rfl, read⟩
              | succ count =>
                  obtain ⟨first, last⟩ := ih rest tail count
                  exact ⟨Domain.View.read_cons _ _ _ _ _ found first, last⟩

/-- Readback of the old whole state determines the new whole state. The
single new SSA cell replaces precisely header field six. -/
theorem read_output {carriers : Carriers} (header : Header)
    (stores environment : Domain.Environment carriers) (state : List Nat)
    (read : Domain.read environment state = some (header.encode stores)) (phase : Nat) :
    Domain.read (environment ++ [.data (.index phase)]) (output state environment.length) =
      some ({header with phase := phase}.encode stores) := by
  have kept := RecordAllocator.read_extended environment [.data (.index phase)] _ _ read
  have first := (read_parts _ _ _ kept 6).1
  have last := (read_parts _ _ _ kept 7).2
  have added := Domain.View.read_cons _ environment.length _ (.data (.index phase)) _
    (by simp) last
  simp only [output, Domain.read, List.mapM_append] at first added ⊢
  rw [first, added]
  rfl

/-- The actual phase leaf, including both construction checkpoints and all
returned stores, is connected by the common primitive and projection rules. -/
theorem Recognized.simulation {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel) (program : Program)
    (context : Context) (header : Header) (stores environment : Domain.Environment model.toCarriers)
    (start : checked.start = environment.length) (bounded : checked.phase < indexLimit)
    (read : Domain.read environment checked.state = some (header.encode stores)) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done ({header with phase := checked.phase}.encode stores))
      ((Domain.evaluate model program context body environment).bind fun final ↦
        match Domain.read final returned with
        | some values => .done values
        | none => .halt .refused)) := by
  rcases checked with ⟨phase, offset, state, rfl, rfl⟩
  dsimp only at start bounded read ⊢
  subst offset
  have constant : Domain.View.execute model (.indexConstant phase) [] [.data .index]
      environment = .done (environment ++ [.data (.index phase)]) := by
    have law := ConnectionPrimitives.view_execute model (.indexConstant phase)
      .nil rfl rfl environment [] rfl
    simpa [Primitive.results, Primitive.evaluateOn, bounded, primitiveOutcome,
      PIR.Process.bind, Original.encodeHelperResult, Domain.encodeValues_cons,
      Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle] using law
  have bodyLaw := Domain.Correspondence.sequence
    (Domain.Correspondence.execute (.indexConstant phase) [] [.data .index])
    Domain.Correspondence.empty (model := model) (program := program) (context := context)
  change Domain.Correspondence.Block (instructions phase) _ at bodyLaw
  have head : Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (environment ++ [.data (.index phase)]))
      (Domain.evaluate model program context (instructions phase) environment) := by
    rw [bodyLaw]
    apply RecordAllocator.silent_sequence constant (List.prefix_refl _) (List.prefix_append _ _)
    exact .done rfl
  refine ⟨head.continueDone (fun _ held ↦ held) ?_⟩
  rw [read_output header stores environment state read phase]
  exact .done rfl

end Phase

namespace Root

def instructions (start continuation : Nat) (site : String) : List Construction.Instruction :=
  RequiredIndices.constantInstructions start continuation 0 site ++ Phase.instructions 3

structure Recognized (body : List Construction.Instruction) (returned : List Nat) where
  start : Nat
  continuation : Nat
  site : String
  state : List Nat
  continuationField : state[3]? = some continuation
  exactBody : body = instructions start continuation site
  exactOutput : returned = Phase.output state (start + 2)

/-- Admit the complete root arm, including the guard added by dispatch. The
guard must select the continuation field of the same returned controller. -/
def recognize (start : Nat) (state : List Nat) (body : List Construction.Instruction)
    (returned : List Nat) : Option (Recognized body returned) := do
  let _ :: comparison :: guard :: _ := body | none
  let [continuation, _] := comparison.operands | none
  let .require site := guard.operation | none
  if continuationField : state[3]? = some continuation then
    if exactBody : body = instructions start continuation site then
      if exactOutput : returned = Phase.output state (start + 2) then
        some ⟨start, continuation, site, state, continuationField, exactBody, exactOutput⟩
      else none
    else none
  else none

/-- Both the accepted root and a misselected non-root are connected. No
Completed value is projected before the actual continuation guard succeeds. -/
theorem Recognized.simulation {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel) (program : Program)
    (context : Context) (header : Header) (stores environment : Domain.Environment model.toCarriers)
    (start : checked.start = environment.length)
    (read : Domain.read environment checked.state = some (header.encode stores)) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (if header.continuation = 0 then .done ({header with phase := 3}.encode stores)
        else .halt .refused)
      ((Domain.evaluate model program context body environment).bind fun final ↦
        match Domain.read final returned with
        | some values => .done values
        | none => .halt .refused)) := by
  have readContinuation : environment[checked.continuation]? =
      some (.data (.index header.continuation)) := by
    have projected := Domain.View.read_getElem? read 3
    rw [checked.continuationField] at projected
    simpa [Header.encode, Header.values, QueryResumption.Coordinates.values] using projected.symm
  rcases checked with ⟨offset, continuation, site, state, _, rfl, rfl⟩
  dsimp only at start read readContinuation ⊢
  subst offset
  obtain ⟨guard⟩ := RequiredIndices.constant model environment environment (List.prefix_refl _)
    continuation 0 header.continuation site (by decide) readContinuation
  let added : Domain.Environment model.toCarriers :=
    [.data (.index 0), .data (.boolean true)]
  let literal : Phase.Recognized (Phase.instructions 3)
      (Phase.output state (environment.length + 2)) :=
    ⟨3, environment.length + 2, state, rfl, rfl⟩
  obtain ⟨tail⟩ := literal.simulation model program context header stores (environment ++ added)
    (by simp [literal, added]) (by change 3 < indexLimit; decide)
    (RecordAllocator.read_extended environment added _ _ read)
  have weakened := tail.mapRelations (fun _ _ equal ↦ equal)
    (fun _ _ held ↦ (List.prefix_append environment added).trans held)
  have guardBody := RequiredIndices.constantCorrespondence model program context
    environment.length continuation 0 site
  rw [← guardBody] at guard
  refine ⟨?_⟩
  rw [instructions, Domain.evaluate_append, PIR.Process.bind_assoc]
  by_cases root : header.continuation = 0
  · have accepted : RequiredIndices.Accepted [(header.continuation, 0)] := by
      simp [RequiredIndices.Accepted, root, indexLimit]
    simp only [root, ↓reduceIte] at guard ⊢
    exact guard.continueDone (fun _ held ↦ held) weakened
  · have refused : ¬ RequiredIndices.Accepted [(header.continuation, 0)] := by
      intro accepted
      exact root (accepted (header.continuation, 0) (by simp)).2.2
    simp only [root, ↓reduceIte, refused] at guard ⊢
    exact guard.continueHalt _ (fun _ held ↦ held)

end Root

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {self : Nat} {S E : Type} {root : OracleKind}

/-- A phase change preserves the complete source return witness. Completion
still requires the root continuation and the final work transition below. -/
def Returned.withPhase
    {interaction : PIR.Interaction (OracleProcess.Interface model S E)}
    {source : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value root.answer))}
    {initial : interaction.Phase} {kindSlot : OracleKind → Nat}
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)} {header : Header}
    (returned : Returned (snapshot := snapshot) (domains := domains) (math := math)
      (self := self) interaction source initial kindSlot arenas header) (phase : Nat) :
    Returned (snapshot := snapshot) (domains := domains) (math := math)
      (self := self) interaction source initial kindSlot arenas {header with phase := phase} :=
  ⟨Returned.kind returned, Returned.answer returned, Returned.state returned,
    Returned.phase returned, Returned.events returned, Returned.kind_eq returned,
    Returned.cell returned, Returned.stack returned, Returned.reached returned⟩

/-- Root completion joins the unchanged source return, the final charged
administrative transition, and the actual emitted leaf. No provider work or
answer/frame allocation can be charged to this transition. -/
theorem Returned.finish
    {interaction : PIR.Interaction (OracleProcess.Interface model S E)}
    {source : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value root.answer))}
    {initial : interaction.Phase} {kindSlot : OracleKind → Nat}
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)} {header : Header}
    (returned : Returned (snapshot := snapshot) (domains := domains) (math := math)
      (self := self) interaction source initial kindSlot arenas header)
    {shape : QueryWork.Shape}
    {frames : (identity : String) → (count : Nat) →
      List (model.Value (QueryContinuation.layout identity count).type)}
    (work : Work shape header arenas frames) (waiting : QueryWork.Frames)
    (position : work.position = .returned waiting)
    (expansion : OracleEntries model snapshot domains math → OracleRead → QueryWork.Shape → Prop)
    (currentShape : QueryWork.Shape)
    (scheduled : QuerySourceWork.StackSchedule expansion (Returned.stack returned)
      currentShape waiting)
    (atRoot : header.continuation = 0) (rootSlot : kindSlot root = 0)
    {body : List Construction.Instruction} {yielded : List Nat}
    (checked : Root.Recognized body yielded)
    (program : Program) (context : Context)
    (stores environment : Domain.Environment model.toCarriers)
    (start : checked.start = environment.length)
    (read : Domain.read environment checked.state = some (header.encode stores)) :
    Nonempty (Work shape {header with phase := 3} arenas frames) ∧
    (∃ answer : model.Value root.answer, (arenas root)[header.answer]? = some answer ∧
      PIR.Reaches interaction source initial
        (.done ⟨.returned answer, Returned.state returned, Returned.events returned⟩)
        (Returned.phase returned)) ∧
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done ({header with phase := 3}.encode stores))
      ((Domain.evaluate model program context body environment).bind fun final ↦
        match Domain.read final yielded with
        | some values => .done values
        | none => .halt .refused)) := by
  have noFrames : waiting = [] := by
    rcases header with
      ⟨⟨constructor, anchorInstance, query, continuation, savedSlot⟩, kind, phase, slot⟩
    dsimp only at atRoot
    subst continuation
    exact scheduled.zero_frames
  have step : QueryWork.Advance work.position .completed 0 0 := by
    rw [position, noFrames]
    exact .finish
  refine ⟨⟨work.advance step rfl (by simp) (by simp)⟩,
    (returned.completed_root atRoot rootSlot).2.2, ?_⟩
  simpa only [atRoot, ↓reduceIte] using
    checked.simulation model program context header stores environment start read

end Zkc.Realization.QueryController
