module

public import Zkc.Realization.QueryInitialize
public import Zkc.Realization.QueryFinish
public import Zkc.Realization.QueryResumptionOutput
public import Zkc.Realization.QuerySourceStack
public import Zkc.Realization.QueryWork

@[expose] public section

/-! The shared source/physical relation used by the generated controller.
The current query and its original execution determine the continuation stack;
the physical header and answer cells must describe that same state. Initialization
and completed-root projection use the actual generated instruction rules.
Enter/return dispatch must preserve this relation and its work accounting before
the enclosing conditional ranges can consume the existing progress theorems.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Realization.QueryController
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Header extends QueryResumption.Coordinates where
  kind : Nat
  phase : Nat
  answer : Nat
  deriving DecidableEq, Repr

def Header.values (header : Header) : List Nat :=
  header.toCoordinates.values ++ [header.kind, header.phase, header.answer]

def Header.encode {carriers : Carriers} (header : Header)
    (stores : Domain.Environment carriers) : Domain.Environment carriers :=
  header.values.map (fun value ↦ .data (.index value)) ++ stores

def Header.initial (constructor anchorInstance position : Nat) : Header :=
  ⟨⟨constructor, anchorInstance, position, 0, 0⟩, 0, 0, 0⟩

theorem initial_encoding (model : DomainModel) (constructor anchorInstance position : Nat)
    (types : List Ty) :
    (Header.initial constructor anchorInstance position).encode
      (QueryInitialize.emptyValues model types) =
        QueryInitialize.initialState model constructor anchorInstance position types := rfl

/-- The phase field belongs to the same complete carried state. In particular
it is not inferred from the kind field, which has the same physical type. -/
theorem Header.phase_read {carriers : Carriers} (header : Header)
    (stores : Domain.Environment carriers) :
    (header.encode stores)[6]? = some (.data (.index header.phase)) := by
  simp [Header.encode, Header.values, QueryResumption.Coordinates.values]

theorem Header.kind_read {carriers : Carriers} (header : Header)
    (stores : Domain.Environment carriers) :
    (header.encode stores)[5]? = some (.data (.index header.kind)) := by
  simp [Header.encode, Header.values, QueryResumption.Coordinates.values]

theorem Header.answer_read {carriers : Carriers} (header : Header)
    (stores : Domain.Environment carriers) :
    (header.encode stores)[7]? = some (.data (.index header.answer)) := by
  simp [Header.encode, Header.values, QueryResumption.Coordinates.values]

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {self : Nat} {S E : Type} {root : OracleKind}

/-- Pending source execution is indexed by the physical continuation coordinates.
The installation relation authenticates the current handle; source progress fixes
its position, older registry, provider state, interaction phase and continuation.
The compiler's kind layout supplies `kindSlot`; no answer type is used as identity. -/
structure Pending (interaction : PIR.Interaction (OracleProcess.Interface model S E))
    (source : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value root.answer)))
    (initial : interaction.Phase) (references : CaptureLayout.References)
    (kindSlot : OracleKind → Nat) (header : Header) where
  request : OracleRead
  entries : OracleEntries model snapshot domains math
  state : S × Nat
  phase : interaction.Phase
  referenceIdentity : String
  reference : references request.kind referenceIdentity request.anchor
    (header.constructor, header.anchorInstance)
  position : header.position = request.position
  kind : header.kind = kindSlot request.kind
  stack : QuerySourceStack.Stack model snapshot domains math self S E root request.kind
    header.continuation header.continuationInstance
  reached : PIR.Reaches interaction source initial
    ((OracleProcess.answer model self entries request state).bind stack.restore) phase

/-- A returned cell is tied to the actual child execution and saved parent chain.
The source root reaches that child's full execution record, not merely an equal
answer. Typed arena membership alone cannot manufacture this witness. -/
structure Returned (interaction : PIR.Interaction (OracleProcess.Interface model S E))
    (source : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value root.answer)))
    (initial : interaction.Phase) (kindSlot : OracleKind → Nat)
    (arenas : (kind : OracleKind) → List (model.Value kind.answer)) (header : Header) where
  kind : OracleKind
  answer : model.Value kind.answer
  state : S × Nat
  phase : interaction.Phase
  events : List (OracleEvent E)
  kind_eq : header.kind = kindSlot kind
  cell : (arenas kind)[header.answer]? = some answer
  stack : QuerySourceStack.Stack model snapshot domains math self S E root kind
    header.continuation header.continuationInstance
  reached : PIR.Reaches interaction source initial
    (stack.restore ⟨.returned answer, state, events⟩) phase

/-- Establish the root's source relation from its installed physical reference.
The initialization body supplies the header; this rule supplies its original
query and empty continuation chain without a source traversal or provider step. -/
def pending_initial
    (interaction : PIR.Interaction (OracleProcess.Interface model S E))
    (entries : OracleEntries model snapshot domains math) (request : OracleRead)
    (state : S × Nat) (phase : interaction.Phase) (references : CaptureLayout.References)
    (kindSlot : OracleKind → Nat) (rootSlot : kindSlot request.kind = 0)
    (identity : String) (constructor anchorInstance : Nat)
    (associated : references request.kind identity request.anchor (constructor, anchorInstance)) :
    Pending (snapshot := snapshot) (domains := domains) (math := math) (self := self) interaction
      (OracleProcess.answer model self entries request state) phase references kindSlot
      (Header.initial constructor anchorInstance request.position) where
  request := request
  entries := entries
  state := state
  phase := phase
  referenceIdentity := identity
  reference := associated
  position := rfl
  kind := rootSlot.symm
  stack := .root
  reached := QuerySourceStack.initial interaction entries request state phase

/-- Every state must relate its phase to the same work position. Allocation
counts bound the actual typed stores, including every repeated child occurrence.
Dispatch must construct these fields; this record is not an author premise. -/
structure Work (shape : QueryWork.Shape) (header : Header)
    (arenas : (kind : OracleKind) → List (model.Value kind.answer))
    (frames : (identity : String) → (count : Nat) →
      List (model.Value (QueryContinuation.layout identity count).type)) where
  position : QueryWork.Position
  steps : Nat
  replies : Nat
  answers : Nat
  saves : Nat
  history : QueryWork.Prefix (.enter shape []) position steps replies answers saves
  phase : header.phase = position.phase
  answerBound : ∀ kind, (arenas kind).length ≤ answers
  frameBound : ∀ identity count, (frames identity count).length ≤ saves

/-- A single reached prefix bounds the current ranges and every physical store.
No independent capacity premise is introduced for each arena or saved frame. -/
theorem Work.bounds {shape : QueryWork.Shape} {header : Header}
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)}
    {frames : (identity : String) → (count : Nat) →
      List (model.Value (QueryContinuation.layout identity count).type)}
    (work : Work shape header arenas frames) {nodes leaves : Nat}
    (nodeBound : shape.nodes ≤ nodes) (leafBound : shape.leaves ≤ leaves) :
    work.position.transitions < 2 * nodes + 1 ∧ work.position.reads < leaves + 1 ∧
      (∀ kind, (arenas kind).length ≤ nodes) ∧
      (∀ identity count, (frames identity count).length < nodes) := by
  have ranges := work.history.range_bounds nodeBound leafBound
  have totals := work.history.bounds
  refine ⟨ranges.1, ranges.2, ?_, ?_⟩
  · intro kind
    have bound := work.answerBound kind
    omega
  · intro identity count
    have bound := work.frameBound identity count
    omega

def work_initial (shape : QueryWork.Shape) (constructor anchorInstance position : Nat) :
    Work (model := model) shape (Header.initial constructor anchorInstance position)
      (fun _ ↦ []) (fun _ _ ↦ []) where
  position := .enter shape []
  steps := 0
  replies := 0
  answers := 0
  saves := 0
  history := .nil _
  phase := rfl
  answerBound := fun _ ↦ Nat.le_refl _
  frameBound := fun _ _ ↦ Nat.le_refl _

/-- Advance the very same history when a connected branch allocates its
answer or continuation. Store-growth facts come from the physical append rules;
the source companion does not supply a new capacity for each store. -/
def Work.advance {shape : QueryWork.Shape} {header nextHeader : Header}
    {arenas nextArenas : (kind : OracleKind) → List (model.Value kind.answer)}
    {frames nextFrames : (identity : String) → (count : Nat) →
      List (model.Value (QueryContinuation.layout identity count).type)}
    (work : Work shape header arenas frames) {next : QueryWork.Position}
    {answers saves : Nat} (step : QueryWork.Advance work.position next answers saves)
    (phase : nextHeader.phase = next.phase)
    (answerGrowth : ∀ kind, (nextArenas kind).length ≤ (arenas kind).length + answers)
    (frameGrowth : ∀ identity count,
      (nextFrames identity count).length ≤ (frames identity count).length + saves) :
    Work shape nextHeader nextArenas nextFrames where
  position := next
  steps := work.steps + 1
  replies := work.replies
  answers := work.answers + answers
  saves := work.saves + saves
  history := work.history.advance step
  phase := phase
  answerBound := fun kind ↦ (answerGrowth kind).trans (Nat.add_le_add_right (work.answerBound kind) _)
  frameBound := fun identity count ↦
    (frameGrowth identity count).trans (Nat.add_le_add_right (work.frameBound identity count) _)

def Work.respond {shape : QueryWork.Shape} {header nextHeader : Header}
    {arenas nextArenas : (kind : OracleKind) → List (model.Value kind.answer)}
    {frames : (identity : String) → (count : Nat) →
      List (model.Value (QueryContinuation.layout identity count).type)}
    (work : Work shape header arenas frames) {next : QueryWork.Position}
    (step : QueryWork.Respond work.position next)
    (phase : nextHeader.phase = next.phase)
    (answerGrowth : ∀ kind, (nextArenas kind).length ≤ (arenas kind).length + 1) :
    Work shape nextHeader nextArenas frames where
  position := next
  steps := work.steps
  replies := work.replies + 1
  answers := work.answers + 1
  saves := work.saves
  history := work.history.respond step
  phase := phase
  answerBound := fun kind ↦ (answerGrowth kind).trans (Nat.add_le_add_right (work.answerBound kind) _)
  frameBound := work.frameBound

/-- A completed header fixes the work position, hence the exact totals of
the history that bounded every intermediate physical allocation. -/
theorem Work.completed {shape : QueryWork.Shape} {header : Header}
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)}
    {frames : (identity : String) → (count : Nat) →
      List (model.Value (QueryContinuation.layout identity count).type)}
    (work : Work shape header arenas frames) (finished : header.phase = 3) :
    work.position = .completed ∧ work.steps = 2 * shape.nodes ∧
      work.replies = shape.leaves ∧ work.answers = shape.nodes ∧ work.saves = shape.nodes - 1 := by
  have position : work.position = .completed :=
    (QueryWork.Position.completed_iff _).mp (by rw [← work.phase, finished])
  refine ⟨position, ?_⟩
  have history := work.history
  rw [position] at history
  exact history.completed

/-- A real child execution and its actual arena cell establish Return. The
source phase, poststate and event log come from that execution. Header routing
retains the same continuation, constructor and instance. -/
def Pending.returned
    {interaction : PIR.Interaction (OracleProcess.Interface model S E)}
    {source : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value root.answer))}
    {initial : interaction.Phase} {references : CaptureLayout.References}
    {kindSlot : OracleKind → Nat} {header : Header}
    (pending : Pending (snapshot := snapshot) (domains := domains) (math := math)
      (self := self) interaction source initial references kindSlot header)
    (arenas : (kind : OracleKind) → List (model.Value kind.answer)) (slot : Nat)
    (answer : model.Value (Pending.request pending).kind.answer) (state : S × Nat)
    (events : List (OracleEvent E)) (final : interaction.Phase)
    (child : PIR.Reaches interaction
      (OracleProcess.answer model self (Pending.entries pending)
        (Pending.request pending) (Pending.state pending))
      (Pending.phase pending) (.done ⟨.returned answer, state, events⟩) final)
    (cell : (arenas (Pending.request pending).kind)[slot]? = some answer) :
    Returned (snapshot := snapshot) (domains := domains) (math := math) (self := self)
      interaction source initial kindSlot arenas {header with phase := 1, answer := slot} where
  kind := (Pending.request pending).kind
  answer := answer
  state := state
  phase := final
  events := events
  kind_eq := Pending.kind pending
  cell := cell
  stack := Pending.stack pending
  reached := QuerySourceStack.returned interaction (Pending.stack pending) (Pending.reached pending) _ child

theorem Pending.stopped
    {interaction : PIR.Interaction (OracleProcess.Interface model S E)}
    {source : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value root.answer))}
    {initial : interaction.Phase} {references : CaptureLayout.References}
    {kindSlot : OracleKind → Nat} {header : Header}
    (pending : Pending (snapshot := snapshot) (domains := domains) (math := math)
      (self := self) interaction source initial references kindSlot header)
    (reason : PIR.Stop) (state : S × Nat) (events : List (OracleEvent E))
    (final : interaction.Phase)
    (child : PIR.Reaches interaction
      (OracleProcess.answer model self (Pending.entries pending)
        (Pending.request pending) (Pending.state pending))
      (Pending.phase pending) (.done ⟨.stopped reason, state, events⟩) final) :
    PIR.Reaches interaction source initial
      (.done ⟨.stopped reason, state, (Pending.stack pending).events ++ events⟩) final :=
  QuerySourceStack.stopped interaction (Pending.stack pending) (Pending.reached pending)
    reason state events child

/-- The complete generated resumption body preserves source progress and
the same allocation history. Its answer is the actual child's returned value;
its capacity follows from the root work history, not a per-response premise.
The global store representation supplies the append and growth facts, including
aliases of one physical arena under compatible logical kind annotations. -/
theorem Pending.resume
    {interaction : PIR.Interaction (OracleProcess.Interface model S E)}
    {source : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value root.answer))}
    {initial : interaction.Phase} {references : CaptureLayout.References}
    {kindSlot : OracleKind → Nat} {header : Header}
    (pending : Pending (snapshot := snapshot) (domains := domains) (math := math)
      (self := self) interaction source initial references kindSlot header)
    {shape : QueryWork.Shape}
    {arenas nextArenas : (kind : OracleKind) → List (model.Value kind.answer)}
    {frames : (identity : String) → (count : Nat) →
      List (model.Value (QueryContinuation.layout identity count).type)}
    (work : Work shape header arenas frames) (waiting : QueryWork.Frames)
    (position : work.position = .request waiting) (capacity : shape.nodes ≤ indexLimit)
    (answer : model.Value (Pending.request pending).kind.answer) (state : S × Nat)
    (events : List (OracleEvent E)) (final : interaction.Phase)
    (child : PIR.Reaches interaction
      (OracleProcess.answer model self (Pending.entries pending)
        (Pending.request pending) (Pending.state pending))
      (Pending.phase pending) (.done ⟨.returned answer, state, events⟩) final)
    (appended : nextArenas (Pending.request pending).kind =
      arenas (Pending.request pending).kind ++ [answer])
    (resident : (Pending.stack pending).Resident arenas frames)
    (extension : ∀ kind, arenas kind <+: nextArenas kind)
    (growth : ∀ kind, (nextArenas kind).length ≤ (arenas kind).length + 1)
    (program : Program) (context : Context)
    (placement : QueryResumption.Placement) (body : List Construction.Instruction)
    (actual : body = QueryResumption.instructions (Pending.request pending).kind.answer
      header.kind placement)
    (data : (Pending.request pending).kind.answer.isHandle = false)
    (kindBound : header.kind < indexLimit) (bounded : header.toCoordinates.Bounded)
    (environment : Domain.Environment model.toCarriers) (start : placement.start = environment.length)
    (before after : List Nat) (beforeValues afterValues : Domain.Environment model.toCarriers)
    (readPhase : environment[placement.phase]? = some (.data (.index header.phase)))
    (readKind : environment[placement.kind]? = some (.data (.index header.kind)))
    (coordinates : RequiredIndices.Readback environment placement.checks
      (QueryResumption.pairs header.toCoordinates header.toCoordinates))
    (readArena : environment[placement.arena]? =
      some (.data ⟨.sequence (Pending.request pending).kind.answer, data,
        arenas (Pending.request pending).kind⟩))
    (readAnswer : environment[placement.answer]? =
      some (.data ⟨(Pending.request pending).kind.answer, data, answer⟩))
    (readBefore : Domain.read environment before = some beforeValues)
    (readAfter : Domain.read environment after = some afterValues) :
    let nextHeader := {header with
      phase := 1
      answer := (arenas (Pending.request pending).kind).length}
    Nonempty {result : Returned (snapshot := snapshot) (domains := domains) (math := math)
      (self := self) interaction source initial kindSlot nextArenas nextHeader //
      (Returned.stack result).Resident nextArenas frames} ∧
    Nonempty (Work shape nextHeader nextArenas frames) ∧
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (.done (nextHeader.encode (beforeValues ++
        [.data ⟨.sequence (Pending.request pending).kind.answer, data,
          nextArenas (Pending.request pending).kind⟩] ++ afterValues)))
      ((Domain.evaluate model program context body environment).bind fun result ↦
        match Domain.read result (QueryResumption.outputReferences placement before after) with
        | some values => .done values
        | none => .halt .refused)) := by
  dsimp only
  have step : QueryWork.Respond work.position (.returned waiting) := by
    rw [position]
    exact .base _
  have room : (arenas (Pending.request pending).kind).length < indexLimit := by
    have total := work.history.answer_room (addedSaves := 0) (Or.inr step)
    have arena := work.answerBound (Pending.request pending).kind
    omega
  have phase : header.phase = 2 := by
    rw [work.phase, position]
    rfl
  refine ⟨⟨pending.returned nextArenas _ answer state events final child ?_,
      resident.transport extension (fun _ _ ↦ List.prefix_refl _)⟩,
    ⟨work.respond step rfl growth⟩, ?_⟩
  · rw [appended]
    simp
  let recognized : QueryResumption.Recognized body :=
    ⟨(Pending.request pending).kind.answer, header.kind, placement, actual⟩
  obtain ⟨certificate⟩ := recognized.output model program context data kindBound
    environment start header.phase header.kind header.toCoordinates header.toCoordinates
    (arenas (Pending.request pending).kind) answer before after beforeValues afterValues
    readPhase readKind coordinates readArena readAnswer readBefore readAfter
  have coordinateChecks :=
    (QueryResumption.accepted_iff header.toCoordinates header.toCoordinates).mpr ⟨rfl, bounded⟩
  have phaseCheck : RequiredIndices.Accepted [(2, 2)] := by decide
  have kindCheck : RequiredIndices.Accepted [(header.kind, header.kind)] := by
    simpa [RequiredIndices.Accepted] using kindBound
  dsimp only [recognized] at certificate
  simp only [QueryResumption.resumed, phase, phaseCheck, kindCheck, coordinateChecks,
    room, ↓reduceIte, PIR.Process.bind] at certificate
  refine ⟨?_⟩
  convert certificate using 1
  simp [Header.encode, Header.values, QueryResumption.outputValues,
    appended, List.map_append, List.append_assoc]

/-- Returning through continuation zero recovers the original root's complete
execution. The same-typed kind tag is derived from the checked root layout. -/
theorem Returned.completed_root
    {interaction : PIR.Interaction (OracleProcess.Interface model S E)}
    {source : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value root.answer))}
    {initial : interaction.Phase} {kindSlot : OracleKind → Nat}
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)} {header : Header}
    (returned : Returned (snapshot := snapshot) (domains := domains) (math := math)
      (self := self) interaction source initial kindSlot arenas header)
    (atRoot : header.continuation = 0) (rootSlot : kindSlot root = 0) :
    header.kind = 0 ∧ header.continuationInstance = 0 ∧
      ∃ answer : model.Value root.answer, (arenas root)[header.answer]? = some answer ∧
        PIR.Reaches interaction source initial
          (.done ⟨.returned answer, Returned.state returned, Returned.events returned⟩)
          (Returned.phase returned) := by
  rcases header with ⟨⟨constructor, anchorInstance, position, continuation, outer⟩, kind, phase, slot⟩
  dsimp only at atRoot
  subst continuation
  rcases returned with ⟨current, value, state, reachedPhase, events, kind_eq, cell, stack, reached⟩
  cases stack
  exact ⟨kind_eq.trans rootSlot, rfl, value, cell, reached⟩

/-- Reconnect the checked physical finish to the source execution accumulated
by the controller. The arena cell and root kind are consequences of the saved
source chain. Only SSA readback and the actually recognized body are supplied by
the installation. This is the final continuation of the enclosing range proof. -/
theorem Returned.output
    {interaction : PIR.Interaction (OracleProcess.Interface model S E)}
    {source : PIR.Process (OracleProcess.Interface model S E)
      (PIR.Execution (S × Nat) (OracleEvent E) (model.Value root.answer))}
    {initial : interaction.Phase} {kindSlot : OracleKind → Nat}
    {arenas : (kind : OracleKind) → List (model.Value kind.answer)} {header : Header}
    (returned : Returned (snapshot := snapshot) (domains := domains) (math := math)
      (self := self) interaction source initial kindSlot arenas header)
    (atRoot : header.continuation = 0) (rootSlot : kindSlot root = 0)
    (completed : header.phase = 3)
    {body : List Construction.Instruction} {outputs : List Nat}
    (checked : QueryFinish.Recognized body outputs) (type : checked.type = root.answer)
    (program : Program) (context : Context) (data : root.answer.isHandle = false)
    (environment : Domain.Environment model.toCarriers)
    (start : checked.placement.start = environment.length)
    (readPhase : environment[checked.placement.phase]? = some (.data (.index header.phase)))
    (readKind : environment[checked.placement.kind]? = some (.data (.index header.kind)))
    (readArena : environment[checked.placement.arena]? =
      some (.data ⟨.sequence root.answer, data, arenas root⟩))
    (readSlot : environment[checked.placement.answer]? = some (.data (.index header.answer))) :
    ∃ answer : model.Value root.answer,
      PIR.Reaches interaction source initial
        (.done ⟨.returned answer, Returned.state returned, Returned.events returned⟩)
        (Returned.phase returned) ∧
      Nonempty (Original.Simulation
        (fun value output ↦ output = [.data ⟨root.answer, data, value⟩])
        (fun _ frame ↦ environment <+: frame) (.done answer)
        ((Domain.evaluate model program context body environment).bind fun final ↦
          match Domain.read final outputs with
          | some values => .done values
          | none => .halt .refused)) := by
  obtain ⟨rootKind, _, answer, cell, reached⟩ := returned.completed_root atRoot rootSlot
  refine ⟨answer, reached, ?_⟩
  rcases checked with ⟨resultType, placement, rfl, rfl⟩
  dsimp only at type
  subst resultType
  obtain ⟨certificate⟩ :=
    (⟨root.answer, placement, rfl, rfl⟩ :
      QueryFinish.Recognized (QueryFinish.instructions root.answer placement)
        [placement.start + 4]).output model program context data environment start
      header.phase header.kind header.answer (arenas root) readPhase readKind readArena readSlot
  refine ⟨?_⟩
  simp only [QueryFinish.answer, completed, rootKind] at certificate
  simp [RequiredIndices.Accepted, indexLimit, cell] at certificate
  convert certificate using 1

end Zkc.Realization.QueryController
