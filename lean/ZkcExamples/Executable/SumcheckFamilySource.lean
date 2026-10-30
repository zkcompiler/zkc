module

public import ZkcExamples.Executable.SumcheckFamilyBudget
public import ZkcExamples.Executable.SumcheckMessages
public import Zkc.Executable.DomainSuccessRules
public import Zkc.Construction.Uniform.DomainIteration
public meta import ZkcTools.ConstructionBindings.ArtifactBindingTactic

@[expose] public section

/-! Local admission and a shared mathematical proof for arbitrary realizations
of the canonical Sumcheck shape. No whole-program success or correspondence is
an admission field. The only semantic equations concern the five helpers and
the four occurrences in one round. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.SumcheckFamily.Source
open Zkc Zkc.Construction Zkc.Executable Zkc.Source Zkc.Source.Structured
open Zkc.Construction.Uniform Zkc.Construction.Uniform.DomainAdapter
open Zkc.Construction.ArtifactBinding
open SumcheckShape
open Zkc.Polynomial.Multilinear
open SumcheckMessages (lowSum highSum)

abbrev Shape := ProgramShape.Description

def staticOrigin (shape : Shape) (template : Template) : Origin :=
  (template.origin shape.context).getD ⟨"", [], none⟩

def transcript (shape : Shape) : SumcheckMessages.Transcript :=
  ⟨shape.names.scalar, staticOrigin shape shape.names.firstMessage,
    staticOrigin shape shape.names.secondMessage, staticOrigin shape shape.names.draw,
    staticOrigin shape shape.names.delivery⟩

/-- The request is explicit, so the query reply really has the scalar carrier.
The resolution law below checks this exact origin against the actual template. -/
def drawOrigin (shape : Shape) (index : Nat) : Origin :=
  let origin := Domain.atCoordinates (staticOrigin shape shape.names.draw) [index]
  ⟨origin.entry, origin.event, some (.draw shape.names.scalar)⟩

/-- Canonical admission is stronger than mere `Template.origin.isSome`:
repeat coordinates, selected context, receive schemas, and typed draw requests
are checked explicitly. Projected keys must match the honest producer's keys. -/
structure Occurrences (shape : Shape) : Prop where
  firstSchema : shape.names.firstReceive.2.1 = shape.names.firstReceive.1
  secondSchema : shape.names.secondReceive.2.1 = shape.names.secondReceive.1
  first : ∀ index, Domain.templateOrigin shape.context shape.names.firstMessage [index] =
    some (Domain.atCoordinates (staticOrigin shape shape.names.firstMessage) [index])
  second : ∀ index, Domain.templateOrigin shape.context shape.names.secondMessage [index] =
    some (Domain.atCoordinates (staticOrigin shape shape.names.secondMessage) [index])
  draw : ∀ index, Domain.queryOrigin shape.context shape.names.suite shape.names.scalar shape.names.draw [index] =
    some (drawOrigin shape index)
  delivery : ∀ index, Domain.templateOrigin shape.context shape.names.delivery [index] =
    some (Domain.atCoordinates (staticOrigin shape shape.names.delivery) [index])
  firstRequest : (staticOrigin shape shape.names.firstMessage).request = none
  secondRequest : (staticOrigin shape shape.names.secondMessage).request = none
  deliveryRequest : (staticOrigin shape shape.names.delivery).request = none
  firstKey : ∀ index, Origin.withoutCoordinates
    (Domain.atCoordinates (staticOrigin shape shape.names.firstMessage) [index]) = (transcript shape).firstMessage
  secondKey : ∀ index, Origin.withoutCoordinates
    (Domain.atCoordinates (staticOrigin shape shape.names.secondMessage) [index]) = (transcript shape).secondMessage
  drawKey : ∀ index, Origin.withoutCoordinates (drawOrigin shape index) = (transcript shape).draw
  deliveryKey : ∀ index, Origin.withoutCoordinates
    (Domain.atCoordinates (staticOrigin shape shape.names.delivery) [index]) = (transcript shape).delivery

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Local mathematical laws on actual closed Domain helpers. The terminal law
is needed only on the bounded, correctly shaped tables reached by honesty;
outside those arguments the helper remains completely unconstrained here. -/
structure Helpers (shape : Shape) : Prop where
  pending : ∀ (claim : F), Domain.callHelper (ringModel F G) shape.program shape.names.pendingHelper
    [.data (.vector shape.names.scalar), .data (.field shape.names.scalar)] [.data (.field shape.names.scalar claim)] =
      .returned [.data (.vector shape.names.scalar []), .data (.field shape.names.scalar claim)]
  openClaim : ∀ (point : List F) (claim : F), Domain.callHelper (ringModel F G) shape.program shape.names.openClaimHelper
    [.data (.vector shape.names.scalar), .data (.field shape.names.scalar)]
    [.data (.vector shape.names.scalar point), .data (.field shape.names.scalar claim)] =
      .returned [.data (.vector shape.names.scalar point), .data (.field shape.names.scalar claim)]
  atPrefix : ∀ (point : List F) (claim : F), Domain.callHelper (ringModel F G) shape.program shape.names.atPrefixHelper
    [.data (.vector shape.names.scalar), .data (.field shape.names.scalar)]
    [.data (.vector shape.names.scalar point), .data (.field shape.names.scalar claim)] =
      .returned [.data (.vector shape.names.scalar point), .data (.field shape.names.scalar claim)]
  append : ∀ (point : List F) (answer : F),
    Domain.callHelper (ringModel F G) shape.program shape.names.appendHelper [.data (.vector shape.names.scalar)]
      [.data (.vector shape.names.scalar point), .data (.field shape.names.scalar answer)] =
      .returned [.data (.vector shape.names.scalar (point ++ [answer]))]
  check : ∀ (values point : List F) (claim : F), point.length < 64 → values.length = 2 ^ point.length →
    Domain.callHelper (ringModel F G) shape.program shape.names.checkHelper [.data .boolean]
      [.data (.vector shape.names.scalar values), .data (.vector shape.names.scalar point),
        .data (.field shape.names.scalar claim)] =
      .returned [.data (.boolean (decide ((restrictPrefixValues values point).sum = claim)))]

structure RoundState (F G : Type) where
  point : List F
  scalar : F
  history : Domain.History (uniformCarriers F G)

def roundState (shape : Shape) (index : Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) :
    PIR.Process (Domain.effects (uniformCarriers F G)) (RoundState F G) :=
  .call (.receive (.field shape.names.scalar) shape.names.firstReceive.1
      shape.names.firstReceive.1 shape.names.firstReceive.2.2) fun low =>
    let lowEvent := Domain.Event.message (Domain.atCoordinates (staticOrigin shape shape.names.firstMessage) [index])
      (.field shape.names.scalar low)
    .call (.observe lowEvent) fun _ =>
      .call (.receive (.field shape.names.scalar) shape.names.secondReceive.1
          shape.names.secondReceive.1 shape.names.secondReceive.2.2) fun high =>
        let highEvent := Domain.Event.message (Domain.atCoordinates (staticOrigin shape shape.names.secondMessage) [index])
          (.field shape.names.scalar high)
        .call (.observe highEvent) fun _ =>
          if scalar = low + high then
            .call (.query (history ++ [lowEvent, highEvent]) (drawOrigin shape index)) fun (answer : F) =>
              let delivery := Domain.Event.message (Domain.atCoordinates (staticOrigin shape shape.names.delivery) [index])
                (.field shape.names.scalar answer)
              .call (.observe delivery) fun _ =>
                .done ⟨point ++ [answer], (1 - answer) * low + answer * high,
                  history ++ [lowEvent, highEvent, .challenge (drawOrigin shape index), delivery]⟩
          else .halt .reject

def roundProcess (shape : Shape) (index : Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) :=
  (roundState shape index point scalar history).bind fun state =>
    .done (ProgramShape.carried shape state.point state.scalar state.history)

/-- Generated local correspondence: every branch and every typed reply of the
actual canonical round, proved using only occurrence and append-helper laws. -/
theorem round_projection (shape : Shape) (occurrences : Occurrences shape) (helpers : Helpers (F := F) (G := G) shape)
    (a b c d e f g h : Domain.Value (uniformCarriers F G)) (index : Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) :
    (((Domain.evaluate (ringModel F G) shape.program shape.context (roundBody shape.names)
      ([a,b,c,d,e,f,g,h] ++ .data (.index index) :: ProgramShape.carried shape point scalar history)).bind
      (yieldValues yielded (carriedSorts shape.names))).interpret Original.forgetCheckpoints) =
      roundProcess shape index point scalar history := by
  have lowResolved := occurrences.first index
  have highResolved := occurrences.second index
  have drawResolved := occurrences.draw index
  have deliveryResolved := occurrences.delivery index
  have firstRequest : (Domain.atCoordinates (staticOrigin shape shape.names.firstMessage) [index]).request = none := occurrences.firstRequest
  have secondRequest : (Domain.atCoordinates (staticOrigin shape shape.names.secondMessage) [index]).request = none := occurrences.secondRequest
  have deliveryRequest : (Domain.atCoordinates (staticOrigin shape shape.names.delivery) [index]).request = none := occurrences.deliveryRequest
  normalize_artifact_operations [lowResolved, highResolved, drawResolved, deliveryResolved,
      firstRequest, secondRequest, deliveryRequest, occurrences.firstSchema, occurrences.secondSchema,
      shape.suite, helpers.append, Domain.Calculations.fieldAdd (F := F) (G := G),
      Domain.Calculations.fieldEqual (F := F) (G := G)]
    unfolding [roundProcess, roundState, roundBody, drawOrigin, ProgramShape.carried, Domain.evaluate, Domain.step,
      PIR.Process.interpret, Original.forgetCheckpoints, Structured.Ty.isHandle, Bool.not_false, Bool.not_true]
  congr 1
  funext low
  simp only [PIR.Process.bind]
  congr 1
  funext ignoredLow
  congr 1
  funext high
  congr 1
  funext ignoredHigh
  by_cases valid : scalar = low + high
  all_goals simp only [valid, decide_true, decide_false, ite_true, ite_false]
  all_goals normalize_artifact_operations [helpers.append, shape.suite, drawResolved,
      deliveryResolved, deliveryRequest, Domain.Calculations.fieldConstant (F := F) (G := G),
      Domain.Calculations.fieldSubtract (F := F) (G := G), Domain.Calculations.fieldMultiply (F := F) (G := G),
      Domain.Calculations.fieldAdd (F := F) (G := G)]
    unfolding [Domain.evaluate, Domain.step, PIR.Process.interpret, Original.forgetCheckpoints, Structured.Ty.isHandle,
      Bool.not_false, Bool.not_true, List.append_assoc, Nat.cast_one, yieldValues, carriedSorts, drawOrigin]
  all_goals rfl


/-- All-reply loop correspondence is derived from the generated local round
proof, using the shared Domain iteration seam. No loop equation is admitted. -/
theorem loop_projection (shape : Shape) (occurrences : Occurrences shape) (helpers : Helpers (F := F) (G := G) shape)
    (a b c d e f g h : Domain.Value (uniformCarriers F G)) (indices : List Nat)
    (point : List F) (scalar : F) (history : Domain.History (uniformCarriers F G)) :
    (Domain.iterate (Domain.evaluate (ringModel F G) shape.program shape.context (roundBody shape.names))
      [a,b,c,d,e,f,g,h] yielded (carriedSorts shape.names) indices (ProgramShape.carried shape point scalar history)).interpret
        Original.forgetCheckpoints =
      (Finite.fold (fun state index => roundState shape index state.point state.scalar state.history)
        indices (⟨point, scalar, history⟩ : RoundState F G)).bind fun state =>
          .done (ProgramShape.carried shape state.point state.scalar state.history) := by
  induction indices generalizing point scalar history with
  | nil => rfl
  | cons index rest ih =>
      rw [iterate_bind, PIR.Process.interpret_bind]
      rw [round_projection shape occurrences helpers a b c d e f g h index point scalar history]
      simp only [roundProcess, Finite.fold, PIR.Process.bind_assoc, PIR.Process.bind]
      congr 1
      funext state
      exact ih state.point state.scalar state.history

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Read back the precise two absorbed message events, retaining the arbitrary
initial history outside the nominal transcript suffix. -/
theorem mapped_messages (shape : Shape) (occurrences : Occurrences shape)
    (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory Origin.withoutCoordinates history = some suffix)
    (index : Nat) (low high : F) :
    readbackHistory Origin.withoutCoordinates
      (history ++ [.message (Domain.atCoordinates (staticOrigin shape shape.names.firstMessage) [index])
        (.field shape.names.scalar low),
        .message (Domain.atCoordinates (staticOrigin shape shape.names.secondMessage) [index])
          (.field shape.names.scalar high)]) =
      some (suffix ++ [.message (transcript shape).firstMessage (.field shape.names.scalar low),
        .message (transcript shape).secondMessage (.field shape.names.scalar high)]) := by
  rw [readbackHistory_append, mapped]
  simp [readbackHistory, readbackEvent, readbackPayload,
    occurrences.firstKey index, occurrences.secondKey index]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- All four transcript events survive readback, in their actual order. -/
theorem mapped_round (shape : Shape) (occurrences : Occurrences shape)
    (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory Origin.withoutCoordinates history = some suffix)
    (index : Nat) (low high answer : F) :
    readbackHistory Origin.withoutCoordinates
      (history ++ [.message (Domain.atCoordinates (staticOrigin shape shape.names.firstMessage) [index])
        (.field shape.names.scalar low),
        .message (Domain.atCoordinates (staticOrigin shape shape.names.secondMessage) [index])
          (.field shape.names.scalar high), .challenge (drawOrigin shape index),
        .message (Domain.atCoordinates (staticOrigin shape shape.names.delivery) [index])
          (.field shape.names.scalar answer)]) =
      some (suffix ++ [.message (transcript shape).firstMessage (.field shape.names.scalar low),
        .message (transcript shape).secondMessage (.field shape.names.scalar high),
        .challenge (transcript shape).draw,
        .message (transcript shape).delivery (.field shape.names.scalar answer)]) := by
  rw [readbackHistory_append, mapped]
  simp [readbackHistory, readbackEvent, readbackPayload,
    occurrences.firstKey index, occurrences.secondKey index, occurrences.drawKey index, occurrences.deliveryKey index]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The generic producer uses the same four resolved occurrence templates. -/
theorem drawn_eq (shape : Shape) (history : History F G) (low high : F) :
    (transcript shape).drawn history low high = history ++
      [.message (transcript shape).firstMessage (.field shape.names.scalar low),
       .message (transcript shape).secondMessage (.field shape.names.scalar high),
       .challenge (transcript shape).draw] := by
  simp only [SumcheckMessages.Transcript.drawn, List.append_assoc, List.cons_append, List.nil_append]
  rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem delivered_eq (shape : Shape) (history : History F G) (low high answer : F) :
    (transcript shape).delivered history low high answer = history ++
      [.message (transcript shape).firstMessage (.field shape.names.scalar low),
       .message (transcript shape).secondMessage (.field shape.names.scalar high),
       .challenge (transcript shape).draw,
       .message (transcript shape).delivery (.field shape.names.scalar answer)] := by
  simp only [SumcheckMessages.Transcript.delivered, drawn_eq, List.append_assoc, List.cons_append, List.nil_append]
  rfl

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Actual deterministic success of one honest round, including both typed
receives and the mapped query handler's request and history checks. -/
theorem round_passes (shape : Shape) (occurrences : Occurrences shape)
    (oracle : History F G → F) (initial : History F G) (index : Nat)
    (point : List F) (low high : F) (history : Domain.History (uniformCarriers F G)) (suffix : History F G)
    (mapped : readbackHistory Origin.withoutCoordinates history = some suffix) (proof : Proof F G) :
    DomainVM.Passes Origin.withoutCoordinates initial oracle
      (roundState shape index point (low + high) history)
      (.field shape.names.scalar low :: .field shape.names.scalar high :: proof)
      (fun state unread =>
        let answer := oracle ((transcript shape).drawn (initial ++ suffix) low high)
        state.point = point ++ [answer] ∧ state.scalar = (1 - answer) * low + answer * high ∧
        ∃ suffix', readbackHistory Origin.withoutCoordinates state.history = some suffix' ∧
          initial ++ suffix' = (transcript shape).delivered (initial ++ suffix) low high answer ∧ unread = proof) := by
  have queried : query (m := Id) Origin.withoutCoordinates initial oracle
      (history ++
        [.message (Domain.atCoordinates (staticOrigin shape shape.names.firstMessage) [index]) (.field shape.names.scalar low),
         .message (Domain.atCoordinates (staticOrigin shape shape.names.secondMessage) [index]) (.field shape.names.scalar high)])
      (drawOrigin shape index) = .returned (oracle ((transcript shape).drawn (initial ++ suffix) low high)) := by
    have result := query_draw (m := Id) Origin.withoutCoordinates initial oracle _
      (drawOrigin shape index).entry (drawOrigin shape index).event
      shape.names.scalar _ (mapped_messages shape occurrences history suffix mapped index low high)
    change query (m := Id) Origin.withoutCoordinates initial oracle _ (drawOrigin shape index) =
      .returned (oracle (initial ++ _ ++ [.challenge (Origin.withoutCoordinates (drawOrigin shape index))])) at result
    simpa only [occurrences.drawKey index, drawn_eq, List.append_assoc, List.cons_append, List.nil_append] using result
  simp only [roundState, DomainVM.Passes, Value.decode, ite_true, queried,
    show Domain.drawRequest (drawOrigin shape index) = true from rfl, true_and]
  refine ⟨suffix ++
    [.message (transcript shape).firstMessage (.field shape.names.scalar low),
     .message (transcript shape).secondMessage (.field shape.names.scalar high),
     .challenge (transcript shape).draw,
     .message (transcript shape).delivery
       (.field shape.names.scalar (oracle ((transcript shape).drawn (initial ++ suffix) low high)))], ?_, ?_, trivial⟩
  · simpa only [drawn_eq, List.append_assoc] using mapped_round shape occurrences history suffix mapped index low high
      (oracle ((transcript shape).drawn (initial ++ suffix) low high))
  · rw [delivered_eq]
    simp only [drawn_eq, List.append_assoc]

/-- Honest fold invariant: the claim is the restricted table's sum and the
proof contains exactly the honest messages of the remaining rounds. -/
def Honest (shape : Shape) (oracle : History F G → F) (initial : History F G) (values : List F) (rounds : Nat)
    (indices : List Nat) (state : RoundState F G) (proof : Proof F G) : Prop :=
  state.point.length + indices.length = rounds ∧
  (restrictPrefixValues values state.point).length = 2 ^ indices.length ∧
  state.scalar = (restrictPrefixValues values state.point).sum ∧
  ∃ suffix, readbackHistory Origin.withoutCoordinates state.history = some suffix ∧
    proof = (SumcheckMessages.honestRounds (transcript shape) oracle (initial ++ suffix) (restrictPrefixValues values state.point) indices.length).map
      (.field shape.names.scalar)

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The actual round constructs the invariant at the next point from the two
honest half sums; no successful-execution premise is assumed. -/
theorem honest_step (shape : Shape) (occurrences : Occurrences shape) (oracle : History F G → F) (initial : History F G) (values : List F) (rounds : Nat)
    (index : Nat) (rest : List Nat) (state : RoundState F G) (proof : Proof F G)
    (honest : Honest shape oracle initial values rounds (index :: rest) state proof) :
    DomainVM.Passes Origin.withoutCoordinates initial oracle
      (roundState shape index state.point state.scalar state.history) proof
      (fun next unread => Honest shape oracle initial values rounds rest next unread) := by
  obtain ⟨length, tableShape, scalar, suffix, mapped, proofEq⟩ := honest
  let table := restrictPrefixValues values state.point
  have even : table.length % 2 = 0 := by rw [tableShape, List.length_cons, pow_succ]; simp
  have sumEq : table.sum = lowSum table + highSum table :=
    (List.sum_take_add_sum_drop table _).symm
  rw [scalar, sumEq, proofEq]
  simp only [SumcheckMessages.honestRounds, SumcheckMessages.honestRounds, List.length_cons, List.map_cons]
  apply DomainVM.Passes.mono Origin.withoutCoordinates initial oracle _ _ _ _ ?_
    (round_passes shape occurrences oracle initial index state.point (lowSum table) (highSum table)
      state.history suffix mapped _)
  intro next unread result
  obtain ⟨pointEq, scalarEq, suffix', mapped', historyEq, unreadEq⟩ := result
  refine ⟨?_, ?_, ?_, suffix', mapped', ?_⟩
  · simp only [pointEq, List.length_append, List.length_cons, List.length_nil] at length ⊢
    omega
  · rw [pointEq, restrictPrefixValues_append]
    exact restrictValues_length table _ (by rw [tableShape, List.length_cons, pow_succ, Nat.mul_comm])
  · rw [scalarEq, pointEq, restrictPrefixValues_append]
    exact (Zkc.Protocols.Sumcheck.Multilinear.restrictValues_sum table _ even).symm
  · rw [unreadEq, historyEq, pointEq, restrictPrefixValues_append]
    rfl

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The invariant composes for an arbitrary number and list of round indices. -/
theorem reduce_passes (shape : Shape) (occurrences : Occurrences shape) (oracle : History F G → F) (initial : History F G) (values : List F) (rounds : Nat)
    (indices : List Nat) (state : RoundState F G) (proof : Proof F G)
    (honest : Honest shape oracle initial values rounds indices state proof) :
    DomainVM.Passes Origin.withoutCoordinates initial oracle
      (Finite.fold (fun state index => roundState shape index state.point state.scalar state.history) indices state) proof
      (fun next unread => Honest shape oracle initial values rounds [] next unread) := by
  exact DomainVM.Passes.fold Origin.withoutCoordinates initial oracle _
    (Honest shape oracle initial values rounds)
    (fun index rest state proof => honest_step shape occurrences oracle initial values rounds index rest state proof)
    indices state proof honest



/-- Complete nominal result and exact empty unread suffix, with evidence that
native transcript readback succeeds for every initial legacy history. -/
def Success (shape : Shape) (returned : DomainVM.Environment F G) (unread : Proof F G) : Prop :=
  unread = [] ∧ ∃ history, returned = [.data (.boolean true), .transcript shape.names.suite history] ∧
    ∃ suffix, readbackHistory Origin.withoutCoordinates history = some suffix

/-- Honesty is derived at the canonical observation, rather than admitted. -/
theorem observation_passes (shape : Shape) (occurrences : Occurrences shape) (helpers : Helpers (F := F) (G := G) shape)
    (oracle : History F G → F) (initial : History F G) (values : List F) (rounds : Nat)
    (admitted : rounds ≤ shape.maximum) (shaped : values.length = 2 ^ rounds) :
    DomainVM.Passes Origin.withoutCoordinates initial oracle
      (DomainVM.observation shape.program shape.context (instructions shape.names shape.maximum) [13,10]
        (ProgramShape.inputs shape values values.sum rounds []))
      ((SumcheckMessages.honestRounds (transcript shape) oracle initial values rounds).map (.field shape.names.scalar))
      (Success shape) := by
  unfold DomainVM.observation DomainVM.outcome
  normalize_artifact_operations [helpers.pending, helpers.openClaim, helpers.atPrefix, shape.suite, admitted]
    unfolding [instructions, pendingCall, openClaimCall, atPrefixCall, ProgramShape.inputs, Domain.evaluate, Domain.step,
      carriedSorts, PIR.Process.interpret, Original.forgetCheckpoints]
  rw [PIR.Process.interpret_bind]
  have loopEq := loop_projection shape occurrences helpers
    (.data (.vector shape.names.scalar values)) (.data (.field shape.names.scalar values.sum))
    (.data (.index rounds)) (.transcript shape.names.suite []) (.data (.vector shape.names.scalar []))
    (.data (.field shape.names.scalar values.sum)) (.data (.vector shape.names.scalar []))
    (.data (.field shape.names.scalar values.sum)) (List.range rounds) [] values.sum []
  simp only [ProgramShape.carried, carriedSorts] at loopEq
  rw [loopEq]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  rw [DomainVM.Passes.bind]
  apply DomainVM.Passes.mono Origin.withoutCoordinates initial oracle _ _ _ _ ?_
    (reduce_passes shape occurrences oracle initial values rounds (List.range rounds) ⟨[], values.sum, []⟩ _ ?_)
  · intro state proof valid
    obtain ⟨length, tableShape, scalar, suffix, mapped, proofEq⟩ := valid
    simp only [List.length_nil, Nat.add_zero] at length
    have small : state.point.length < 64 := by have := shape.small; omega
    have checked := helpers.check values state.point state.scalar small (by rw [length]; exact shaped)
    have correct : decide ((restrictPrefixValues values state.point).sum = state.scalar) = true := by
      simp only [scalar, decide_true]
    rw [correct] at checked
    normalize_artifact_operations [helpers.atPrefix, checked]
      unfolding [ProgramShape.carried, carriedSorts, atPrefixCall, checkCall, Domain.evaluate, Domain.step, DomainVM.readback,
        PIR.Process.interpret, Original.forgetCheckpoints, DomainVM.Passes]
    refine ⟨?_, state.history, rfl, suffix, mapped⟩
    simp only [proofEq, SumcheckMessages.honestRounds, List.length_nil, List.map_nil]
  · exact ⟨by simp, by simpa only [restrictPrefixValues_nil, List.length_range] using shaped,
      rfl, [], rfl, by simp [restrictPrefixValues_nil]⟩

end ZkcExamples.Executable.SumcheckFamily.Source
