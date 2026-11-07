module

public import Zkc.Realization.TableRead
public import Zkc.Realization.QueryResumptionOutput
public import Zkc.Construction.OriginalFrameRelations

@[expose] public section

/-! The clear base read followed by checked controller resumption. The value
inserted into the answer arena is the actual bounded table read, including its
refusal behavior. Request checks follow that read in the emitted order. -/
set_option autoImplicit false
namespace Zkc.Realization.QueryReadResponse
open Zkc.Source Zkc.Source.Structured Zkc.Construction

def instructions (domain : String) (kind : Nat) (read : TableRead.Placement)
    (response : QueryResumption.Placement) : List Construction.Instruction :=
  TableRead.instructions domain read ++ QueryResumption.instructions (.field domain) kind response

structure Recognized (body : List Construction.Instruction) where
  domain : String
  kind : Nat
  read : TableRead.Placement
  response : QueryResumption.Placement
  start : response.start = read.start + 2
  answer : response.answer = read.start + 1
  position : read.position = response.pending.position
  exactBody : body = instructions domain kind read response

def recognize (body : List Construction.Instruction) : Option (Recognized body) := do
  let read ← TableRead.recognize (body.take 3)
  let response ← QueryResumption.recognizeAt (read.placement.start + 2) (body.drop 3)
  if start : response.placement.start = read.placement.start + 2 then
    if answer : response.placement.answer = read.placement.start + 1 then
      if position : read.placement.position = response.placement.pending.position then
        if exactBody : body = instructions read.domain response.kind
            read.placement response.placement then
          some ⟨read.domain, response.kind, read.placement, response.placement,
            start, answer, position, exactBody⟩
        else none
      else none
    else none
  else none

def response (model : DomainModel) (domain : String) (kind phase actualKind : Nat)
    (pending supplied : QueryResumption.Coordinates) (answers : List (model.Field domain))
    (answer : model.Field domain) (before after : Domain.Environment model.toCarriers) :=
  (QueryResumption.resumed model (.field domain) rfl [] kind phase actualKind
    pending supplied answers answer).bind fun _ ↦
      .done (QueryResumption.outputValues model (.field domain) rfl pending kind
        answers answer before after)

/-- Compose all outcomes without assuming the read succeeds. The original
frame establishes the request/arena associations; append preservation derives
their availability after the read, and the new answer slot is computed. -/
theorem Recognized.simulation {body : List Construction.Instruction} (checked : Recognized body)
    (model : DomainModel) (program : Program) (context : Context)
    (kindBound : checked.kind < indexLimit) (environment : Domain.Environment model.toCarriers)
    (start : checked.read.start = environment.length)
    (cells : List (model.Field checked.domain)) (rows phase actualKind : Nat)
    (pending supplied : QueryResumption.Coordinates) (answers : List (model.Field checked.domain))
    (before after : List Nat) (beforeValues afterValues : Domain.Environment model.toCarriers)
    (readData : environment[checked.read.data]? =
      some (.data ⟨.vector checked.domain, rfl, cells⟩))
    (readRows : environment[checked.read.rows]? = some (.data (.index rows)))
    (readPhase : environment[checked.response.phase]? = some (.data (.index phase)))
    (readKind : environment[checked.response.kind]? = some (.data (.index actualKind)))
    (coordinates : RequiredIndices.Readback environment checked.response.checks
      (QueryResumption.pairs pending supplied))
    (readArena : environment[checked.response.arena]? =
      some (.data ⟨.sequence (.field checked.domain), rfl, answers⟩))
    (readBefore : Domain.read environment before = some beforeValues)
    (readAfter : Domain.read environment after = some afterValues) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (((TableRead.read model checked.domain cells rows pending.position).interpret
          (closedLift (I := Domain.effects model.toCarriers))).bind fun answer ↦
        QueryReadResponse.response model checked.domain checked.kind phase actualKind
          pending supplied
          answers answer beforeValues afterValues)
      ((Domain.evaluate model program context body environment).bind fun final ↦
        match Domain.read final
          (QueryResumption.outputReferences checked.response before after) with
        | some values => .done values
        | none => .halt .refused)) := by
  rcases checked with
    ⟨domain, kind, read, resumption, resumptionStart, answerSlot, positionSlot, rfl⟩
  dsimp only at *
  let checkedRead : TableRead.Recognized (TableRead.instructions domain read) := ⟨domain, read, rfl⟩
  let checkedResponse : QueryResumption.Recognized
      (QueryResumption.instructions (.field domain) kind resumption) :=
    ⟨.field domain, kind, resumption, rfl⟩
  have head := checkedRead.simulation model program context environment cells rows pending.position
    start readData readRows
    (by rw [positionSlot]; exact QueryResumption.read_pending_position coordinates)
  simp only [QueryReadResponse.instructions, Domain.evaluate_append, PIR.Process.bind_assoc]
  refine ⟨head.continueClosed (TableRead.read model domain cells rows pending.position)
    (fun value ↦ environment ++ [.data (.boolean true), .data ⟨.field domain, rfl, value⟩])
    (fun _ _ _ held ↦ held) ?_⟩
  intro value
  let added : Domain.Environment model.toCarriers :=
    [.data (.boolean true), .data ⟨.field domain, rfl, value⟩]
  let tail := Classical.choice (checkedResponse.output model program context rfl kindBound
    (environment ++ added) (by simpa [checkedResponse, added, start] using resumptionStart)
    phase actualKind pending supplied answers value
    before after beforeValues afterValues
    (Original.read_append readPhase added) (Original.read_append readKind added)
    (coordinates.extended added) (Original.read_append readArena added)
    (by simp [checkedResponse, answerSlot, start, added])
    (RecordAllocator.read_extended _ added _ _ readBefore)
    (RecordAllocator.read_extended _ added _ _ readAfter))
  have retained := tail.mapRelations (fun _ _ held ↦ held)
    (fun _ _ held ↦ (List.prefix_append environment added).trans held)
  have frameIndependent := QueryResumption.resumed_constant model (.field domain) rfl
    (environment ++ added) kind phase actualKind pending supplied answers value
    (.done (QueryResumption.outputValues model (.field domain) rfl pending kind
      answers value beforeValues afterValues))
  rw [frameIndependent] at retained
  exact retained

end Zkc.Realization.QueryReadResponse
