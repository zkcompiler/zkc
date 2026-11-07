module

public import Zkc.Realization.RequiredIndices
public import Zkc.Construction.ConnectionClosedSimulation

@[expose] public section

/-! The checked resumption of one suspended controller request. Coordinate
agreement and kind selection precede answer insertion. This is an actual-body
rule: the surrounding controller must still relate the saved coordinates to
the reached source request and its parent continuation. -/
set_option autoImplicit false
namespace Zkc.Realization.QueryResumption
open Zkc.Source Zkc.Source.Structured Zkc.Construction

structure Coordinates where
  constructor : Nat
  anchorInstance : Nat
  position : Nat
  continuation : Nat
  continuationInstance : Nat
  deriving DecidableEq, Repr

def Coordinates.values (coordinates : Coordinates) : List Nat :=
  [coordinates.constructor, coordinates.anchorInstance, coordinates.position,
   coordinates.continuation, coordinates.continuationInstance]

structure Placement where
  start : Nat
  phase : Nat
  kind : Nat
  pending : Coordinates
  supplied : Coordinates
  arena : Nat
  answer : Nat
  phaseSite : String
  kindSite : String
  coordinateSites : Fin 5 → String

def Placement.checks (placement : Placement) : List RequiredIndices.Check :=
  [⟨placement.pending.constructor, placement.supplied.constructor, placement.coordinateSites 0⟩,
   ⟨placement.pending.anchorInstance, placement.supplied.anchorInstance,
     placement.coordinateSites 1⟩,
   ⟨placement.pending.position, placement.supplied.position, placement.coordinateSites 2⟩,
   ⟨placement.pending.continuation, placement.supplied.continuation, placement.coordinateSites 3⟩,
   ⟨placement.pending.continuationInstance, placement.supplied.continuationInstance,
     placement.coordinateSites 4⟩]

def pairs (pending supplied : Coordinates) : List (Nat × Nat) :=
  pending.values.zip supplied.values

def Coordinates.Bounded (coordinates : Coordinates) : Prop :=
  ∀ coordinate ∈ coordinates.values, coordinate < indexLimit

/-- Same-typed coordinates retain all five associations, including the saved
outer continuation instance. Agreement alone does not remove ingress bounds. -/
theorem accepted_iff (pending supplied : Coordinates) :
    RequiredIndices.Accepted (pairs pending supplied) ↔
      pending = supplied ∧ pending.Bounded := by
  cases pending with
  | mk a b c d e =>
    cases supplied with
    | mk f g h i j =>
      simp only [pairs, Coordinates.values, RequiredIndices.Accepted, Coordinates.Bounded,
        List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil,
        forall_eq_or_imp, false_implies, implies_true, and_true,
        Coordinates.mk.injEq]
      constructor
      · intro all
        exact ⟨⟨all.1.2.2, all.2.1.2.2, all.2.2.1.2.2, all.2.2.2.1.2.2,
          all.2.2.2.2.2.2⟩, all.1.1, all.2.1.1, all.2.2.1.1, all.2.2.2.1.1, all.2.2.2.2.1⟩
      · rintro ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, a, b, c, d, e⟩
        exact ⟨⟨a, a, rfl⟩, ⟨b, b, rfl⟩, ⟨c, c, rfl⟩, ⟨d, d, rfl⟩, ⟨e, e, rfl⟩⟩

def appendInstructions (type : Ty) (arena answer : Nat) : List Construction.Instruction :=
  [⟨.execute (.sequenceLength type), [arena], [.data .index], []⟩,
   ⟨.execute (.sequenceAppend type), [arena, answer], [.data (.sequence type)], []⟩]

def appendSpine (type : Ty) (arena answer : Nat) : ConnectionTargetPrefix.Prefix :=
  .step (fun model ↦ Domain.View.execute model (.sequenceLength type) [arena] [.data .index])
  (.step (fun model ↦ Domain.View.execute model (.sequenceAppend type)
    [arena, answer] [.data (.sequence type)]) .empty)

theorem appendCorrespondence (model : DomainModel) (program : Program) (context : Context)
    (type : Ty) (arena answer : Nat) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (appendInstructions type arena answer) ((appendSpine type arena answer).block model) :=
  Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
    (Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
      Domain.Correspondence.empty)

def appendResults (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (answers : List (model.Value type)) (answer : model.Value type) :
    Domain.Environment model.toCarriers :=
  [.data (.index answers.length), .data ⟨.sequence type, data, answers ++ [answer]⟩]

set_option backward.isDefEq.respectTransparency false in
/-- Checked length failure precedes insertion. On success the returned index
names precisely the appended answer. Phase assignment belongs to the caller. -/
theorem appendSimulation (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (environment captured : Domain.Environment model.toCarriers)
    (preserved : captured <+: environment)
    (arena answerSlot : Nat) (answers : List (model.Value type)) (answer : model.Value type)
    (readArena : environment[arena]? = some (.data ⟨.sequence type, data, answers⟩))
    (readAnswer : environment[answerSlot]? = some (.data ⟨type, data, answer⟩)) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ captured <+: frame)
      (if answers.length < indexLimit then
        .done (environment ++ appendResults model type data answers answer) else .halt .exhausted)
      ((appendSpine type arena answerSlot).block model environment)) := by
  have localType : Domain.localType type = true := by
    simp [Domain.localType, Domain.dataType, data]
  have localSequence : Domain.localType (.sequence type) = true := by
    simp [Domain.localType, Domain.dataType, Ty.isHandle, Ty.isCustody, data]
  have lengthRead : Domain.read environment [arena] =
      Domain.encodeValues (tys := [.sequence type]) (.cons answers .nil) := by
    simp [Domain.read, readArena, Domain.encodeValues_cons, Domain.encodeValues_nil,
      Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle, data]
  have lengthLaw := ConnectionPrimitives.view_execute model (.sequenceLength type)
    (.cons answers .nil)
    (by simpa [Primitive.arguments] using localSequence) rfl environment [arena] lengthRead
  refine ⟨?_⟩
  change Original.Simulation _ _ _ (Domain.View.sequence _ _ environment)
  by_cases bounded : answers.length < indexLimit
  · simp only [bounded, ↓reduceIte]
    let length : Domain.Value model.toCarriers := .data (.index answers.length)
    let extended : Domain.Value model.toCarriers :=
      .data ⟨.sequence type, data, answers ++ [answer]⟩
    have lengthStep : Domain.View.execute model (.sequenceLength type) [arena] [.data .index]
        environment = .done (environment ++ [length]) := by
      simpa [Primitive.results, Primitive.evaluateOn, bounded, primitiveOutcome, length,
        PIR.Process.bind, Original.encodeHelperResult, Domain.encodeValues_cons,
        Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue,
        Ty.isHandle] using lengthLaw
    have encoded : Domain.Value.encode type answer = some (.data ⟨type, data, answer⟩) :=
      Domain.Value.encode_ofPayload (by simp [Domain.Payload.ofValue, data])
    have sequenceEncoded : Domain.Value.encode (.sequence type) answers =
        some (.data ⟨.sequence type, data, answers⟩) :=
      Domain.Value.encode_ofPayload (by simp [Domain.Payload.ofValue, Ty.isHandle, data])
    have appendRead : Domain.read (environment ++ [length]) [arena, answerSlot] =
        Domain.encodeValues (tys := [.sequence type, type])
          (.cons answers (.cons answer .nil)) := by
      simp [Domain.read, Original.read_append readArena [length],
        Original.read_append readAnswer [length], Domain.encodeValues_cons,
        Domain.encodeValues_nil, encoded, sequenceEncoded]
    have appendStep : Domain.View.execute model (.sequenceAppend type) [arena, answerSlot]
        [.data (.sequence type)] (environment ++ [length]) =
          .done (environment ++ [length, extended]) := by
      have law := ConnectionPrimitives.view_execute model (.sequenceAppend type)
        (.cons answers (.cons answer .nil))
        (by simp [Primitive.arguments, localSequence, localType])
        (by simpa [Primitive.results] using localSequence) _ _ appendRead
      simpa [Primitive.results, Primitive.evaluateOn, primitiveOutcome, extended,
        PIR.Process.bind, Original.encodeHelperResult, Domain.encodeValues_cons,
        Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue,
        Ty.isHandle, data, List.append_assoc] using law
    apply RecordAllocator.silent_sequence lengthStep preserved
      (preserved.trans (List.prefix_append _ _))
    apply RecordAllocator.silent_sequence appendStep
      (preserved.trans (List.prefix_append _ _)) (preserved.trans (List.prefix_append _ _))
    exact .done rfl
  · simp only [bounded, ↓reduceIte]
    have stopped : Domain.View.execute model (.sequenceLength type) [arena] [.data .index]
        environment = .halt .exhausted := by
      simpa [Primitive.results, Primitive.evaluateOn, bounded, primitiveOutcome,
        PIR.Process.bind] using lengthLaw
    rw [Domain.View.sequence_stop _ _ _ _ stopped]
    exact .checkpoint environment preserved (.halt .exhausted)

def answerInstructions (type : Ty) (arena answer : Nat) : List Construction.Instruction :=
  appendInstructions type arena answer ++
    [⟨.execute (.indexConstant 1), [], [.data .index], []⟩]

def answerSpine (type : Ty) (arena answer : Nat) : ConnectionTargetPrefix.Prefix :=
  (appendSpine type arena answer).append
    (.step (fun model ↦ Domain.View.execute model (.indexConstant 1) [] [.data .index]) .empty)

theorem answerCorrespondence (model : DomainModel) (program : Program) (context : Context)
    (type : Ty) (arena answer : Nat) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (answerInstructions type arena answer) ((answerSpine type arena answer).block model) :=
  Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
    (Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
      (Domain.Correspondence.sequence (Domain.Correspondence.execute _ _ _)
        Domain.Correspondence.empty))

def answerResults (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (answers : List (model.Value type)) (answer : model.Value type) :
    Domain.Environment model.toCarriers :=
  [.data (.index answers.length), .data ⟨.sequence type, data, answers ++ [answer]⟩,
   .data (.index 1)]

set_option backward.isDefEq.respectTransparency false in
/-- Checked length failure precedes insertion. On success the returned index
names precisely the appended answer, and the final phase is Return (one). -/
theorem answerSimulation (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (environment captured : Domain.Environment model.toCarriers)
    (preserved : captured <+: environment)
    (arena answerSlot : Nat) (answers : List (model.Value type)) (answer : model.Value type)
    (readArena : environment[arena]? = some (.data ⟨.sequence type, data, answers⟩))
    (readAnswer : environment[answerSlot]? = some (.data ⟨type, data, answer⟩)) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ captured <+: frame)
      (if answers.length < indexLimit then
        .done (environment ++ answerResults model type data answers answer) else .halt .exhausted)
      ((answerSpine type arena answerSlot).block model environment)) := by
  obtain ⟨insert⟩ := appendSimulation model type data environment captured preserved
    arena answerSlot answers answer readArena readAnswer
  change Nonempty (Original.Simulation _ _ _
    (((appendSpine type arena answerSlot).append
      (.step (fun model ↦ Domain.View.execute model (.indexConstant 1) [] [.data .index])
        .empty)).plug (fun _ ↦ Domain.View.empty) model environment))
  rw [ConnectionTargetPrefix.Prefix.append_plug, ConnectionTargetPrefix.Prefix.plug_eq_bind]
  refine ⟨?_⟩
  by_cases bounded : answers.length < indexLimit
  · simp only [bounded, ↓reduceIte] at insert ⊢
    apply insert.continueDone (fun _ held ↦ held)
    have phaseStep : Domain.View.execute model (.indexConstant 1) [] [.data .index]
        (environment ++ appendResults model type data answers answer) =
          .done (environment ++ answerResults model type data answers answer) := by
      have law := ConnectionPrimitives.view_execute model (.indexConstant 1)
        .nil rfl rfl (environment ++ appendResults model type data answers answer) [] rfl
      simpa [Primitive.results, Primitive.evaluateOn, indexLimit, primitiveOutcome,
        PIR.Process.bind, Original.encodeHelperResult, Domain.encodeValues_cons,
        Domain.encodeValues_nil, Domain.Value.encode, Domain.Payload.ofValue,
        Ty.isHandle, answerResults, appendResults, List.append_assoc] using law
    apply RecordAllocator.silent_sequence phaseStep
      (preserved.trans (List.prefix_append _ _)) (preserved.trans (List.prefix_append _ _))
    exact .done rfl
  · simp only [bounded, ↓reduceIte] at insert ⊢
    exact insert.continueHalt _ (fun _ held ↦ held)

def instructions (type : Ty) (kind : Nat) (placement : Placement) : List Construction.Instruction :=
  RequiredIndices.constantInstructions placement.start placement.phase 2 placement.phaseSite ++
  RequiredIndices.constantInstructions (placement.start + 2)
    placement.kind kind placement.kindSite ++
  RequiredIndices.instructions (placement.start + 4) placement.checks ++
  answerInstructions type placement.arena placement.answer

def spine (type : Ty) (kind : Nat) (placement : Placement) : ConnectionTargetPrefix.Prefix :=
  (RequiredIndices.constantSpine placement.start placement.phase 2 placement.phaseSite).append
  ((RequiredIndices.constantSpine (placement.start + 2)
    placement.kind kind placement.kindSite).append
  ((RequiredIndices.spine (placement.start + 4) placement.checks).append
  (answerSpine type placement.arena placement.answer)))

theorem correspondence (model : DomainModel) (program : Program) (context : Context)
    (type : Ty) (kind : Nat) (placement : Placement) :
    Domain.Correspondence.Block (model := model) (program := program) (context := context)
      (instructions type kind placement) ((spine type kind placement).block model) := by
  unfold instructions spine
  rw [List.append_assoc, List.append_assoc]
  exact ConnectionTargetPrefix.correspondence_append model program context
    (RequiredIndices.constantCorrespondence model program context _ _ _ _)
    (ConnectionTargetPrefix.correspondence_append model program context
      (RequiredIndices.constantCorrespondence model program context _ _ _ _)
      (ConnectionTargetPrefix.correspondence_append model program context
        (RequiredIndices.correspondence model program context _ _)
        (answerCorrespondence model program context _ _ _)))

def checkResults {carriers : Carriers} (kind : Nat) : Domain.Environment carriers :=
  [.data (.index 2), .data (.boolean true)] ++
  [.data (.index kind), .data (.boolean true)] ++ RequiredIndices.results 5

/-- The complete checked outcome. Invalid phase, kind or coordinates refuse;
only an admitted request can reach the separate arena-capacity check. -/
def resumed (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (environment : Domain.Environment model.toCarriers) (kind phase actualKind : Nat)
    (pending supplied : Coordinates) (answers : List (model.Value type))
    (answer : model.Value type) :
    PIR.Process (Domain.effects model.toCarriers) (Domain.Environment model.toCarriers) :=
  if RequiredIndices.Accepted [(phase, 2)] then
    if RequiredIndices.Accepted [(actualKind, kind)] then
      if RequiredIndices.Accepted (pairs pending supplied) then
        if answers.length < indexLimit then
          .done (environment ++ checkResults kind ++ answerResults model type data answers answer)
        else .halt .exhausted
      else .halt .refused
    else .halt .refused
  else .halt .refused

/-- A successful resumption determines the phase, kind and exact saved request.
This is a value association, not an unforgeable or single-use capability. -/
theorem resumed_returned (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (environment final : Domain.Environment model.toCarriers) (kind phase actualKind : Nat)
    (pending supplied : Coordinates) (answers : List (model.Value type)) (answer : model.Value type)
    (returned : resumed model type data environment kind phase actualKind pending supplied
      answers answer = .done final) :
    phase = 2 ∧ actualKind = kind ∧ pending = supplied ∧ pending.Bounded ∧
      answers.length < indexLimit ∧
      final = environment ++ checkResults kind ++ answerResults model type data answers answer := by
  unfold resumed at returned
  split_ifs at returned with phaseOk kindOk coordinatesOk room
  have phaseValue := phaseOk (phase, 2) (by simp)
  have kindValue := kindOk (actualKind, kind) (by simp)
  have associated := (accepted_iff pending supplied).mp coordinatesOk
  exact ⟨phaseValue.2.2, kindValue.2.2, associated.1, associated.2, room,
    (PIR.Process.done.inj returned).symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- Compose the existing primitive and requirement rules for the entire
resumption body. All values and both coordinate tuples are arbitrary. The
surrounding controller supplies their association to the reached request. -/
theorem simulation (model : DomainModel) (type : Ty) (data : type.isHandle = false)
    (kind : Nat) (kindBound : kind < indexLimit) (placement : Placement)
    (environment : Domain.Environment model.toCarriers)
    (start : placement.start = environment.length)
    (phase actualKind : Nat) (pending supplied : Coordinates)
    (answers : List (model.Value type)) (answer : model.Value type)
    (readPhase : environment[placement.phase]? = some (.data (.index phase)))
    (readKind : environment[placement.kind]? = some (.data (.index actualKind)))
    (readCoordinates : RequiredIndices.Readback environment placement.checks
      (pairs pending supplied))
    (readArena : environment[placement.arena]? = some (.data ⟨.sequence type, data, answers⟩))
    (readAnswer : environment[placement.answer]? = some (.data ⟨type, data, answer⟩)) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (resumed model type data environment kind phase actualKind pending supplied answers answer)
      ((spine type kind placement).block model environment)) := by
  let phaseResults : Domain.Environment model.toCarriers :=
    [.data (.index 2), .data (.boolean true)]
  let kindResults : Domain.Environment model.toCarriers :=
    [.data (.index kind), .data (.boolean true)]
  let afterPhase := environment ++ phaseResults
  let afterKind := afterPhase ++ kindResults
  let afterChecks := afterKind ++ RequiredIndices.results 5
  obtain ⟨phaseLaw⟩ := RequiredIndices.constant model environment environment (List.prefix_refl _)
    placement.phase 2 phase placement.phaseSite (by decide) readPhase
  obtain ⟨kindLaw⟩ := RequiredIndices.constant model afterPhase environment (List.prefix_append _ _)
    placement.kind kind actualKind placement.kindSite kindBound
    (Original.read_append readKind phaseResults)
  have checkReads : RequiredIndices.Readback afterKind placement.checks (pairs pending supplied) :=
    (readCoordinates.extended phaseResults).extended kindResults
  obtain ⟨checkLaw⟩ := RequiredIndices.simulation model checkReads environment
    ((List.prefix_append environment phaseResults).trans (List.prefix_append _ _))
  have finalPreserved : environment <+: afterChecks :=
    ((List.prefix_append environment phaseResults).trans (List.prefix_append _ _)).trans
      (List.prefix_append _ _)
  obtain ⟨answerLaw⟩ := answerSimulation model type data afterChecks environment finalPreserved
    placement.arena placement.answer answers answer
    (Original.read_append (Original.read_append (Original.read_append readArena phaseResults)
      kindResults) (RequiredIndices.results 5))
    (Original.read_append (Original.read_append (Original.read_append readAnswer phaseResults)
      kindResults) (RequiredIndices.results 5))
  have phaseLength : afterPhase.length = environment.length + 2 := by
    simp [afterPhase, phaseResults]
  have kindLength : afterKind.length = environment.length + 4 := by
    simp [afterKind, afterPhase, phaseResults, kindResults]
  have checkLength : placement.checks.length = 5 := rfl
  rw [phaseLength] at kindLaw
  rw [kindLength, checkLength] at checkLaw
  refine ⟨?_⟩
  unfold spine ConnectionTargetPrefix.Prefix.block
  rw [ConnectionTargetPrefix.Prefix.append_plug, ConnectionTargetPrefix.Prefix.plug_eq_bind, start]
  unfold resumed
  by_cases phaseOk : RequiredIndices.Accepted [(phase, 2)]
  · simp only [phaseOk, ↓reduceIte] at phaseLaw ⊢
    apply phaseLaw.continueDone (fun _ held ↦ held)
    rw [ConnectionTargetPrefix.Prefix.append_plug, ConnectionTargetPrefix.Prefix.plug_eq_bind]
    by_cases kindOk : RequiredIndices.Accepted [(actualKind, kind)]
    · simp only [kindOk, ↓reduceIte] at kindLaw ⊢
      apply kindLaw.continueDone (fun _ held ↦ held)
      rw [ConnectionTargetPrefix.Prefix.append_plug, ConnectionTargetPrefix.Prefix.plug_eq_bind]
      by_cases coordinatesOk : RequiredIndices.Accepted (pairs pending supplied)
      · simp only [coordinatesOk, ↓reduceIte] at checkLaw ⊢
        apply checkLaw.continueDone (fun _ held ↦ held)
        simpa only [afterChecks, afterKind, afterPhase, checkResults, phaseResults, kindResults,
          List.append_assoc, ConnectionTargetPrefix.Prefix.block] using answerLaw
      · simp only [coordinatesOk, ↓reduceIte] at checkLaw ⊢
        exact checkLaw.continueHalt _ (fun _ held ↦ held)
    · simp only [kindOk, ↓reduceIte] at kindLaw ⊢
      exact kindLaw.continueHalt _ (fun _ held ↦ held)
  · simp only [phaseOk, ↓reduceIte] at phaseLaw ⊢
    exact phaseLaw.continueHalt _ (fun _ held ↦ held)

structure Recognized (body : List Construction.Instruction) where
  type : Ty
  kind : Nat
  placement : Placement
  exactBody : body = instructions type kind placement

/-- Read the operand graph, then check every instruction, result sort, guard
and constant. Inlined self-comparisons are retained; no origin name is trusted. -/
def recognizeAt (start : Nat) (body : List Construction.Instruction) :
    Option (Recognized body) := do
  let [_, phaseEqual, phaseGuard, kindConstant, kindEqual, kindGuard,
    firstEqual, firstGuard, secondEqual, secondGuard, thirdEqual, thirdGuard,
    fourthEqual, fourthGuard, fifthEqual, fifthGuard, length, append, _] := body | none
  let [phase, _] := phaseEqual.operands | none
  let [actualKind, _] := kindEqual.operands | none
  let .execute (.indexConstant kind) := kindConstant.operation | none
  let .require phaseSite := phaseGuard.operation | none
  let .require kindSite := kindGuard.operation | none
  let [a, f] := firstEqual.operands | none
  let [b, g] := secondEqual.operands | none
  let [c, h] := thirdEqual.operands | none
  let [d, i] := fourthEqual.operands | none
  let [e, j] := fifthEqual.operands | none
  let .require firstSite := firstGuard.operation | none
  let .require secondSite := secondGuard.operation | none
  let .require thirdSite := thirdGuard.operation | none
  let .require fourthSite := fourthGuard.operation | none
  let .require fifthSite := fifthGuard.operation | none
  let .execute (.sequenceLength type) := length.operation | none
  let [arena] := length.operands | none
  let [_, answer] := append.operands | none
  let placement : Placement := ⟨start, phase, actualKind, ⟨a, b, c, d, e⟩, ⟨f, g, h, i, j⟩,
    arena, answer, phaseSite, kindSite, ![firstSite, secondSite, thirdSite, fourthSite, fifthSite]⟩
  if matched : body = instructions type kind placement then
    some ⟨type, kind, placement, matched⟩
  else none

theorem Recognized.simulation {body : List Construction.Instruction} (checked : Recognized body)
    (model : DomainModel) (program : Program) (context : Context)
    (data : checked.type.isHandle = false) (kindBound : checked.kind < indexLimit)
    (environment : Domain.Environment model.toCarriers)
    (start : checked.placement.start = environment.length)
    (phase actualKind : Nat) (pending supplied : Coordinates)
    (answers : List (model.Value checked.type)) (answer : model.Value checked.type)
    (readPhase : environment[checked.placement.phase]? = some (.data (.index phase)))
    (readKind : environment[checked.placement.kind]? = some (.data (.index actualKind)))
    (readCoordinates : RequiredIndices.Readback environment checked.placement.checks
      (pairs pending supplied))
    (readArena : environment[checked.placement.arena]? =
      some (.data ⟨.sequence checked.type, data, answers⟩))
    (readAnswer : environment[checked.placement.answer]? =
      some (.data ⟨checked.type, data, answer⟩)) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (resumed model checked.type data environment checked.kind phase actualKind
        pending supplied answers answer)
      (Domain.evaluate model program context body environment)) := by
  rcases checked with ⟨type, kind, placement, rfl⟩
  rw [correspondence]
  exact QueryResumption.simulation model type data kind kindBound placement
    environment start phase actualKind pending supplied answers answer
    readPhase readKind readCoordinates readArena readAnswer

end Zkc.Realization.QueryResumption
