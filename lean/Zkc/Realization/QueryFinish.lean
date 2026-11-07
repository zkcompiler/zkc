module

public import Zkc.Realization.RequiredIndices
public import Zkc.Construction.ConnectionClosedSimulation

@[expose] public section

/-! The complete generated finish body checks Completed and the root kind
before reading its answer arena. Its final SSA projection is checked with the
body. Refusal is retained even if the arena happens to contain an answer.
-/
set_option autoImplicit false
namespace Zkc.Realization.QueryFinish
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Placement where
  start : Nat
  phase : Nat
  kind : Nat
  arena : Nat
  answer : Nat
  phaseSite : String
  kindSite : String

def instructions (type : Ty) (placement : Placement) : List Construction.Instruction :=
  RequiredIndices.constantInstructions placement.start placement.phase 3 placement.phaseSite ++
    RequiredIndices.constantInstructions
      (placement.start + 2) placement.kind 0 placement.kindSite ++
    [⟨.execute (.sequenceAt type), [placement.arena, placement.answer], [.data type], []⟩]

def spine (type : Ty) (placement : Placement) : ConnectionTargetPrefix.Prefix :=
  (RequiredIndices.constantSpine placement.start placement.phase 3 placement.phaseSite).append
    ((RequiredIndices.constantSpine
      (placement.start + 2) placement.kind 0 placement.kindSite).append
      (.step (fun model ↦ Domain.View.execute model (.sequenceAt type)
        [placement.arena, placement.answer] [.data type]) .empty))

theorem correspondence (model : DomainModel) (program : Program) (context : Context)
    (type : Ty) (placement : Placement) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (instructions type placement) ((spine type placement).block model) := by
  unfold instructions spine
  rw [List.append_assoc]
  exact ConnectionTargetPrefix.correspondence_append model program context
    (RequiredIndices.constantCorrespondence model program context _ _ _ _)
    (ConnectionTargetPrefix.correspondence_append model program context
      (RequiredIndices.constantCorrespondence model program context _ _ _ _)
      (Domain.Correspondence.sequence
        (Domain.Correspondence.execute _ _ _) Domain.Correspondence.empty))

def checkResults {carriers : Carriers} : Domain.Environment carriers :=
  [.data (.index 3), .data (.boolean true), .data (.index 0), .data (.boolean true)]

/-- The exact finish result, including incorrect phases, kinds and missing
answer cells. No success condition is required for this interpretation. -/
def finished (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (environment : Domain.Environment model.toCarriers) (phase kind : Nat)
    (answers : List (model.Value type)) (slot : Nat) :
    PIR.Process (Domain.effects model.toCarriers) (Domain.Environment model.toCarriers) :=
  if RequiredIndices.Accepted [(phase, 3)] then
    if RequiredIndices.Accepted [(kind, 0)] then
      match answers[slot]? with
      | none => .halt .refused
      | some value => .done (environment ++ checkResults ++ [.data ⟨type, data, value⟩])
    else .halt .refused
  else .halt .refused

set_option backward.isDefEq.respectTransparency false in
theorem simulation (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (placement : Placement) (environment : Domain.Environment model.toCarriers)
    (start : placement.start = environment.length) (phase kind slot : Nat)
    (answers : List (model.Value type))
    (readPhase : environment[placement.phase]? = some (.data (.index phase)))
    (readKind : environment[placement.kind]? = some (.data (.index kind)))
    (readArena : environment[placement.arena]? = some (.data ⟨.sequence type, data, answers⟩))
    (readSlot : environment[placement.answer]? = some (.data (.index slot))) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (finished model type data environment phase kind answers slot)
      ((spine type placement).block model environment)) := by
  let phaseResults : Domain.Environment model.toCarriers :=
    [.data (.index 3), .data (.boolean true)]
  let kindResults : Domain.Environment model.toCarriers :=
    [.data (.index 0), .data (.boolean true)]
  let afterPhase := environment ++ phaseResults
  let afterKind := afterPhase ++ kindResults
  obtain ⟨phaseLaw⟩ := RequiredIndices.constant model environment environment (List.prefix_refl _)
    placement.phase 3 phase placement.phaseSite (by decide) readPhase
  obtain ⟨kindLaw⟩ := RequiredIndices.constant model afterPhase environment (List.prefix_append _ _)
    placement.kind 0 kind placement.kindSite (by decide)
    (Original.read_append readKind phaseResults)
  have kindStart : afterPhase.length = environment.length + 2 := by
    simp [afterPhase, phaseResults]
  rw [kindStart] at kindLaw
  have kept : environment <+: afterKind :=
    (List.prefix_append environment phaseResults).trans (List.prefix_append _ _)
  have read : Domain.read afterKind [placement.arena, placement.answer] =
      Domain.encodeValues (tys := [.sequence type, .index]) (.cons answers (.cons slot .nil)) := by
    have first := Original.read_append (Original.read_append readArena phaseResults) kindResults
    have second := Original.read_append (Original.read_append readSlot phaseResults) kindResults
    have both := Domain.View.read_cons afterKind placement.arena [placement.answer] _ _ first
      (Domain.View.read_cons afterKind placement.answer [] _ [] second rfl)
    simpa [Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
      Domain.Payload.ofValue, Ty.isHandle, data] using both
  have localType : Domain.localType type = true := by
    simp [Domain.localType, Domain.dataType, data]
  have inputTypes : (Primitive.sequenceAt type).arguments.all Domain.localType = true := by
    simp [Primitive.arguments, Domain.localType, Domain.dataType, Ty.isHandle, Ty.isCustody, data]
  have readLaw := ConnectionPrimitives.view_execute model (.sequenceAt type)
    (.cons answers (.cons slot .nil)) inputTypes (by simpa [Primitive.results] using localType)
    afterKind [placement.arena, placement.answer] read
  refine ⟨?_⟩
  unfold spine ConnectionTargetPrefix.Prefix.block
  rw [ConnectionTargetPrefix.Prefix.append_plug, ConnectionTargetPrefix.Prefix.plug_eq_bind, start]
  unfold finished
  by_cases phaseOk : RequiredIndices.Accepted [(phase, 3)]
  · simp only [phaseOk, ↓reduceIte] at phaseLaw ⊢
    apply phaseLaw.continueDone (fun _ held ↦ held)
    rw [ConnectionTargetPrefix.Prefix.append_plug, ConnectionTargetPrefix.Prefix.plug_eq_bind]
    by_cases kindOk : RequiredIndices.Accepted [(kind, 0)]
    · simp only [kindOk, ↓reduceIte] at kindLaw ⊢
      apply kindLaw.continueDone (fun _ held ↦ held)
      change Original.Simulation _ _ _ (Domain.View.sequence _ _ afterKind)
      cases found : answers[slot]? with
      | none =>
          have stopped : Domain.View.execute model (.sequenceAt type)
              [placement.arena, placement.answer] [.data type] afterKind = .halt .refused := by
            simpa [Primitive.evaluateOn, found, primitiveOutcome, PIR.Process.bind,
              Primitive.results] using readLaw
          rw [Domain.View.sequence_stop _ _ _ _ stopped]
          exact .checkpoint _ kept (.halt .refused)
      | some value =>
          have encoded : Domain.Value.encode type value = some (.data ⟨type, data, value⟩) :=
            Domain.Value.encode_ofPayload (by simp [Domain.Payload.ofValue, data])
          have step : Domain.View.execute model (.sequenceAt type)
              [placement.arena, placement.answer] [.data type] afterKind =
                .done (afterKind ++ [.data ⟨type, data, value⟩]) := by
            simpa [Primitive.evaluateOn, found, primitiveOutcome, PIR.Process.bind,
              Primitive.results, Original.encodeHelperResult, Domain.encodeValues_cons,
              Domain.encodeValues_nil, encoded] using readLaw
          apply RecordAllocator.silent_sequence step kept (kept.trans (List.prefix_append _ _))
          exact .done (by simp [afterKind, afterPhase, phaseResults, kindResults,
            checkResults, List.append_assoc])
    · simp only [kindOk, ↓reduceIte] at kindLaw ⊢
      exact kindLaw.continueHalt _ (fun _ held ↦ held)
  · simp only [phaseOk, ↓reduceIte] at phaseLaw ⊢
    exact phaseLaw.continueHalt _ (fun _ held ↦ held)

structure Recognized (body : List Construction.Instruction) (returned : List Nat) where
  type : Ty
  placement : Placement
  exactBody : body = instructions type placement
  exactOutput : returned = [placement.start + 4]

/-- Recognize the entire finish body and its single answer output. Operand
and result typing alone cannot justify returning a different same-typed cell. -/
def recognize (start : Nat) (body : List Construction.Instruction) (returned : List Nat) :
    Option (Recognized body returned) := do
  let [_, phaseComparison, phaseGuard, _, kindComparison, kindGuard, answer] := body | none
  let [phase, _] := phaseComparison.operands | none
  let [kind, _] := kindComparison.operands | none
  let .require phaseSite := phaseGuard.operation | none
  let .require kindSite := kindGuard.operation | none
  let .execute (.sequenceAt type) := answer.operation | none
  let [arena, slot] := answer.operands | none
  let placement : Placement := ⟨start, phase, kind, arena, slot, phaseSite, kindSite⟩
  if exactBody : body = instructions type placement then
    if exactOutput : returned = [placement.start + 4] then
      some ⟨type, placement, exactBody, exactOutput⟩
    else none
  else none

theorem Recognized.simulation {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel)
    (program : Program) (context : Context)
    (data : checked.type.isHandle = false) (environment : Domain.Environment model.toCarriers)
    (start : checked.placement.start = environment.length) (phase kind slot : Nat)
    (answers : List (model.Value checked.type))
    (readPhase : environment[checked.placement.phase]? = some (.data (.index phase)))
    (readKind : environment[checked.placement.kind]? = some (.data (.index kind)))
    (readArena : environment[checked.placement.arena]? =
      some (.data ⟨.sequence checked.type, data, answers⟩))
    (readSlot : environment[checked.placement.answer]? = some (.data (.index slot))) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (finished model checked.type data environment phase kind answers slot)
      (Domain.evaluate model program context body environment)) := by
  rcases checked with ⟨type, placement, rfl, rfl⟩
  rw [correspondence]
  exact QueryFinish.simulation model type data placement environment start
    phase kind slot answers readPhase readKind readArena readSlot

/-- The root answer is available only at Completed with the root kind and a
present arena cell. Invalid finish attempts preserve their refusal. -/
def answer (model : DomainModel) (type : Ty) (phase kind : Nat)
    (answers : List (model.Value type)) (slot : Nat) :
    PIR.Process (Domain.effects model.toCarriers) (model.Value type) :=
  if RequiredIndices.Accepted [(phase, 3)] then
    if RequiredIndices.Accepted [(kind, 0)] then
      match answers[slot]? with
      | none => .halt .refused
      | some value => .done value
    else .halt .refused
  else .halt .refused

theorem Recognized.output {body : List Construction.Instruction} {returned : List Nat}
    (checked : Recognized body returned) (model : DomainModel)
    (program : Program) (context : Context)
    (data : checked.type.isHandle = false) (environment : Domain.Environment model.toCarriers)
    (start : checked.placement.start = environment.length) (phase kind slot : Nat)
    (answers : List (model.Value checked.type))
    (readPhase : environment[checked.placement.phase]? = some (.data (.index phase)))
    (readKind : environment[checked.placement.kind]? = some (.data (.index kind)))
    (readArena : environment[checked.placement.arena]? =
      some (.data ⟨.sequence checked.type, data, answers⟩))
    (readSlot : environment[checked.placement.answer]? = some (.data (.index slot))) :
    Nonempty (Original.Simulation
      (fun value output ↦ output = [.data ⟨checked.type, data, value⟩])
      (fun _ frame ↦ environment <+: frame)
      (answer model checked.type phase kind answers slot)
      ((Domain.evaluate model program context body environment).bind fun final ↦
        match Domain.read final returned with
        | some values => .done values
        | none => .halt .refused)) := by
  obtain ⟨head⟩ := checked.simulation model program context data environment start
    phase kind slot answers readPhase readKind readArena readSlot
  refine ⟨?_⟩
  unfold finished at head
  unfold answer
  split_ifs at head ⊢ with phaseOk kindOk
  · cases found : answers[slot]? with
    | none =>
        rw [found] at head
        exact head.continueHalt _ (fun _ held ↦ held)
    | some value =>
        rw [found] at head
        apply head.continueDone (fun _ held ↦ held)
        have projected : Domain.read
            (environment ++ checkResults ++ [.data ⟨checked.type, data, value⟩]) returned =
              some [.data ⟨checked.type, data, value⟩] := by
          simp [checked.exactOutput, start, Domain.read, checkResults]
        rw [projected]
        exact .done rfl
  all_goals exact head.continueHalt _ (fun _ held ↦ held)

end Zkc.Realization.QueryFinish
