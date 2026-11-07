module

public import Zkc.Realization.QueryResumption

@[expose] public section

/-! The resumption's returned controller state, derived from its actual SSA
references. Other arenas and continuation stores keep their original order.
The projection runs only after the complete checked resumption succeeds. -/
set_option autoImplicit false
namespace Zkc.Realization.QueryResumption
open Zkc.Source Zkc.Source.Structured Zkc.Construction

/-- The updated answer arena can occur between other retained state stores. -/
def outputReferences (placement : Placement) (before after : List Nat) : List Nat :=
  placement.pending.values ++
    [placement.start + 2, placement.start + 11, placement.start + 9] ++
    before ++ [placement.start + 10] ++ after

def outputValues (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (pending : Coordinates) (kind : Nat) (answers : List (model.Value type))
    (answer : model.Value type) (before after : Domain.Environment model.toCarriers) :
    Domain.Environment model.toCarriers :=
  pending.values.map (fun value ↦ .data (.index value)) ++
    [.data (.index kind), .data (.index 1), .data (.index answers.length)] ++
    before ++ [.data ⟨.sequence type, data, answers ++ [answer]⟩] ++ after

/-- Once the controller selects its returned state, intermediate SSA cells do
not affect that state. All checks and stops still precede the continuation. -/
theorem resumed_constant {A : Type} (model : DomainModel) (type : Ty)
    (data : type.isHandle = false) (environment : Domain.Environment model.toCarriers)
    (kind phase actualKind : Nat) (pending supplied : Coordinates)
    (answers : List (model.Value type)) (answer : model.Value type)
    (next : PIR.Process (Domain.effects model.toCarriers) A) :
    (resumed model type data environment kind phase actualKind pending supplied answers answer).bind
        (fun _ ↦ next) =
      (resumed model type data [] kind phase actualKind pending supplied answers answer).bind
        (fun _ ↦ next) := by
  unfold resumed
  split_ifs <;> rfl

private theorem read_join {carriers : Carriers} (environment : Domain.Environment carriers)
    (left right : List Nat) (first second : Domain.Environment carriers)
    (readFirst : Domain.read environment left = some first)
    (readSecond : Domain.read environment right = some second) :
    Domain.read environment (left ++ right) = some (first ++ second) := by
  simp only [Domain.read, List.mapM_append] at *
  simp [readFirst, readSecond]

private theorem readLeft {carriers : Carriers} {environment : Domain.Environment carriers}
    {checks : List RequiredIndices.Check} {values : List (Nat × Nat)}
    (readback : RequiredIndices.Readback environment checks values) :
    Domain.read environment (checks.map RequiredIndices.Check.left) =
      some (values.map (fun value ↦ .data (.index value.1))) := by
  induction readback with
  | nil => rfl
  | cons first second tail ih => exact Domain.View.read_cons _ _ _ _ _ first ih

/-- The saved position's value is determined by coordinate readback. A caller
does not supply an independent equation identifying the subsequent table query. -/
theorem read_pending_position {carriers : Carriers} {environment : Domain.Environment carriers}
    {placement : Placement} {pending supplied : Coordinates}
    (coordinates : RequiredIndices.Readback environment placement.checks
      (pairs pending supplied)) :
    environment[placement.pending.position]? = some (.data (.index pending.position)) := by
  cases coordinates with
  | cons _ _ rest =>
      cases rest with
      | cons _ _ rest =>
          cases rest with
          | cons found _ _ => exact found

/-- Read the complete returned state, including the original five coordinates,
the checked kind, Return phase, old arena length and appended answer. -/
theorem read_output (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (placement : Placement) (environment : Domain.Environment model.toCarriers)
    (start : placement.start = environment.length) (kind : Nat)
    (pending supplied : Coordinates) (answers : List (model.Value type))
    (answer : model.Value type) (before after : List Nat)
    (beforeValues afterValues : Domain.Environment model.toCarriers)
    (coordinates : RequiredIndices.Readback environment placement.checks
      (pairs pending supplied))
    (readBefore : Domain.read environment before = some beforeValues)
    (readAfter : Domain.read environment after = some afterValues) :
    Domain.read (environment ++ checkResults kind ++ answerResults model type data answers answer)
      (outputReferences placement before after) =
        some (outputValues model type data pending kind answers answer
          beforeValues afterValues) := by
  let suffix := checkResults (carriers := model.toCarriers) kind ++
    answerResults model type data answers answer
  have readPending : Domain.read environment placement.pending.values =
      some (pending.values.map (fun value ↦ Domain.Value.data (.index value))) := by
    simpa only [Placement.checks, pairs, Coordinates.values, List.zip_cons_cons,
      List.zip_nil_left, List.map_cons, List.map_nil] using readLeft coordinates
  have pendingExtended := RecordAllocator.read_extended environment suffix _ _ readPending
  have beforeExtended := RecordAllocator.read_extended environment suffix _ _ readBefore
  have afterExtended := RecordAllocator.read_extended environment suffix _ _ readAfter
  have header : Domain.read (environment ++ suffix)
      [placement.start + 2, placement.start + 11, placement.start + 9] =
        some [.data (.index kind), .data (.index 1), .data (.index answers.length)] := by
    simp [Domain.read, start, suffix, checkResults, RequiredIndices.results, answerResults]
  have arena : Domain.read (environment ++ suffix) [placement.start + 10] =
      some [.data ⟨.sequence type, data, answers ++ [answer]⟩] := by
    simp [Domain.read, start, suffix, checkResults, RequiredIndices.results, answerResults]
  simpa only [outputReferences, outputValues, suffix, List.append_assoc] using
    read_join _ _ _ _ _
      (read_join _ _ _ _ _ (read_join _ _ _ _ _
        (read_join _ _ _ _ _ pendingExtended header) beforeExtended) arena) afterExtended

/-- Connect the checked body's complete output selection. The same source
resumption decides refusal and exhaustion before any output is projected. -/
theorem Recognized.output {body : List Construction.Instruction} (checked : Recognized body)
    (model : DomainModel) (program : Program) (context : Context)
    (data : checked.type.isHandle = false) (kindBound : checked.kind < indexLimit)
    (environment : Domain.Environment model.toCarriers)
    (start : checked.placement.start = environment.length)
    (phase actualKind : Nat) (pending supplied : Coordinates)
    (answers : List (model.Value checked.type)) (answer : model.Value checked.type)
    (before after : List Nat) (beforeValues afterValues : Domain.Environment model.toCarriers)
    (readPhase : environment[checked.placement.phase]? = some (.data (.index phase)))
    (readKind : environment[checked.placement.kind]? = some (.data (.index actualKind)))
    (coordinates : RequiredIndices.Readback environment checked.placement.checks
      (pairs pending supplied))
    (readArena : environment[checked.placement.arena]? =
      some (.data ⟨.sequence checked.type, data, answers⟩))
    (readAnswer : environment[checked.placement.answer]? =
      some (.data ⟨checked.type, data, answer⟩))
    (readBefore : Domain.read environment before = some beforeValues)
    (readAfter : Domain.read environment after = some afterValues) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      ((resumed model checked.type data environment checked.kind phase actualKind
        pending supplied answers answer).bind fun _ ↦
          .done (outputValues model checked.type data pending checked.kind
            answers answer beforeValues afterValues))
      ((Domain.evaluate model program context body environment).bind fun final ↦
        match Domain.read final (outputReferences checked.placement before after) with
        | some values => .done values
        | none => .halt .refused)) := by
  obtain ⟨head⟩ := checked.simulation model program context data kindBound environment start
    phase actualKind pending supplied answers answer readPhase readKind coordinates
    readArena readAnswer
  refine ⟨?_⟩
  unfold resumed at head ⊢
  split_ifs at head ⊢ with phaseOk kindOk coordinatesOk room
  · simp only [PIR.Process.bind]
    apply head.continueDone (fun _ held ↦ held)
    rw [read_output model checked.type data checked.placement environment start checked.kind
      pending supplied answers answer before after beforeValues afterValues
      coordinates readBefore readAfter]
    exact .done rfl
  all_goals
    simpa only [PIR.Process.bind] using head.continueHalt _ (fun _ held ↦ held)

end Zkc.Realization.QueryResumption
