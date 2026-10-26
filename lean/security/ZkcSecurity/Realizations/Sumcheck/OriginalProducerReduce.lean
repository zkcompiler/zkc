module

public import ZkcSecurity.Realizations.Sumcheck.OriginalProducer
public import ZkcSecurity.Realizations.Sumcheck.OriginalProducerLoop
public import ZkcExamples.Structured.OriginalSumcheckReduce

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.OriginalProducer
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open OriginalSumcheckLibrary SumcheckVerifierBodies SumcheckVerifierHelpers

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem less_lift (payload : UnitPayload)
    (bodies : SumcheckUnitContracts.Bodies payload.definitions)
    (left right : Nat) (leftBound : left < indexLimit) (rightBound : right < indexLimit) :
    invoke (helpers (F := F) (G := G) payload).closed MapFirstBodies.lessHelper
      (.cons left (.cons right .nil)) = .done (.cons (decide (left < right)) .nil) := by
  rw [← (helpers_lift payload).closed, closed_invoke_plain,
    MapFirstContracts.less_law payload.linked bodies.first left right leftBound rightBound]
  rfl

/-- The producer prelude of the shared original Reduce, with the real observed
repeat retained. Width and dimension guards are discharged by explicit admitted
input assumptions; the repeat itself still performs its maximum check. -/
theorem source_reduce (payload : UnitPayload)
    (bodies : SumcheckUnitContracts.Bodies payload.definitions)
    (maximum : Nat) (context : ProtocolContext) (separate : context.roles 1 ≠ context.roles 0)
    (protocols : ProtocolTable (assignment F G) (OriginalSumcheckLibrary.signature (F := F) (G := G)))
    (raw : List F) (dimension count : Nat)
    (dimensionBound : dimension < indexLimit) (countBound : count < indexLimit)
    (enough : count ≤ dimension) (handle : Option Nat) :
    OriginalSumcheckLibrary.reduce payload maximum context (context.roles 0) protocols
      (.cons (some raw) (.cons (some dimension) (.cons (some 1)
        (.cons none (.cons (some count) (.cons handle .nil)))))) =
      (denoteRepeatOn (carriers := uniformCarriers F G) (repeatSpec maximum) context
        (context.roles 0) (some count) (SumcheckProverLaws.embedP (raw, dimension, 1, []))
        (.cons handle .nil) (OriginalSumcheckLibrary.round payload context (context.roles 0))
        Occurrence.iterations "s15").bind
          (fun state => .done (reduceReturnValues state)) := by
  have verifierBodies : SumcheckVerifierHelpers.Bodies payload.definitions :=
    ⟨bodies.empty, bodies.append, bodies.width, bodies.variables, bodies.values⟩
  change (invoke (helpers (F := F) (G := G) payload).components MapFirstBodies.widthHelper
    (.cons (some raw) (.cons (some dimension) (.cons (some 1) .nil)))).bind _ = _
  rw [width_lift payload verifierBodies]
  dsimp only [PIR.Process.bind]
  change (((Participant.guard (services := services) (Value := assignment F G)
    (context.roles 0) (context.roles 0) (some true)).interpret actions).bind
      (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))).bind _ = _
  simp only [Participant.guard, ↓reduceIte, PIR.Process.interpret, PIR.Process.bind]
  change (invoke (helpers (F := F) (G := G) payload).components MapFirstBodies.variablesHelper
    (.cons (some raw) (.cons (some dimension) (.cons (some 1) .nil)))).bind _ = _
  rw [variables_lift payload verifierBodies]
  dsimp only [PIR.Process.bind]
  change (Participant.owned (context.roles 0) (context.roles 0)
    (invoke (helpers (F := F) (G := G) payload).closed MapFirstBodies.lessHelper)
    (.cons (some dimension) (.cons (some count) .nil))).bind _ = _
  simp only [Participant.owned, ↓reduceIte, RoleFamily.sequence,
    Bind.bind, Pure.pure, Option.bind, less_lift payload bodies dimension count dimensionBound countBound, PIR.Process.bind]
  have notLess : ¬ dimension < count := by omega
  try simp only [notLess, decide_false]
  change (((Participant.guard (services := services) (Value := assignment F G)
    (context.roles 0) (context.roles 0) (some true)).interpret actions).bind
      (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))).bind _ = _
  simp only [Participant.guard, ↓reduceIte, PIR.Process.interpret, PIR.Process.bind]
  change (Participant.owned (context.roles 0) (context.roles 0)
    (invoke (helpers (F := F) (G := G) payload).closed SumcheckHelperBodies.emptyHelper)
    .nil).bind _ = _
  simp only [Participant.owned, ↓reduceIte, RoleFamily.sequence, empty_lift payload verifierBodies,
    PIR.Process.bind]
  change (Participant.owned (context.roles 0) (context.roles 1)
    (invoke (helpers (F := F) (G := G) payload).closed SumcheckHelperBodies.emptyHelper)
    .nil).bind _ = _
  simp only [Participant.owned, separate, ↓reduceIte, PIR.Process.bind]
  change (denoteRepeatOn (carriers := uniformCarriers F G) (repeatSpec maximum) context
    (context.roles 0) (some count) (SumcheckProverLaws.embedP (raw, dimension, 1, []))
    (.cons handle .nil) (fun args => roundBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn
        (context.roles 0) protocols context Occurrence.iterations) args.get)
    Occurrence.iterations "s15").bind _ = _
  simp only [OriginalSumcheckLibrary.round_on]
  congr 1
  funext state
  cases state with | cons a state => cases state with | cons b state =>
    cases state with | cons c state => cases state with | cons d state =>
      cases state with | cons e state => cases state with | cons f state =>
        cases state
        rfl

/-- The full original Reduce result and all five appended target values. -/
def ReduceReturns (context : Zkc.Construction.Context) (dimension : Nat)
    (captured : Domain.Environment (uniformCarriers F G))
    (source : Values (Component (assignment F G)) reduceOutputs × Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ raw width point history,
    source = (reduceReturnValues (SumcheckProverLaws.embedP (raw, dimension, width, point)),
      ⟨[], history⟩) ∧ frame = captured ++ carried context raw dimension width point history ∧
    PrimitiveLibrary.HasShape raw dimension width ∧ raw.length < indexLimit

/-- Shared actual producer Reduce, including the source maximum refusal. Every
accepted iteration uses the independent actual-artifact callback certificate. -/
def ProducerCallback.reduce (program : Structured.Program)
    (bodies : SumcheckUnitContracts.Bodies program.payload.definitions)
    (routing : Original.Routing) (occurrence : ZkcSecurity.Realizations.Sumcheck.ArtifactBinding.Occurrence)
    (separate : occurrence.protocol.roles 1 ≠ occurrence.protocol.roles 0)
    (context : Zkc.Construction.Context) (outputs : Outputs context.suite) (offset maximum handle : Nat)
    (body : Domain.View.Block (uniformCarriers F G))
    (certificate : ProducerCallback program routing occurrence context outputs offset handle body)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (raw : List F) (dimension count countRef : Nat) (initialRefs : List Nat)
    (shape : PrimitiveLibrary.HasShape raw dimension 1) (bounded : raw.length < indexLimit)
    (countBound : count < indexLimit) (enough : count ≤ dimension)
    (history : Domain.History (uniformCarriers F G))
    (countRead : captured[countRef]? = some (.data (.index count)))
    (initialRead : Domain.read captured initialRefs = some (carried context raw dimension 1 [] history)) :
    Original.Simulation (ReduceReturns context (dimension - count) captured)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Original.fold routing
        (OriginalSumcheckLibrary.reduce program.payload maximum occurrence.protocol
          (occurrence.protocol.roles 0) []
          (.cons (some raw) (.cons (some dimension) (.cons (some 1)
            (.cons none (.cons (some count) (.cons none .nil))))))) ⟨[], history⟩)
      (Domain.View.loop maximum outputs.references
        countRef initialRefs
        [.data (.vector "bls12-381.fr"), .data .index, .data .index,
          .data (.vector "bls12-381.fr"), .transcript context.suite] body captured) := by
  rw [source_reduce program.payload bodies maximum occurrence.protocol separate [] raw dimension count
    (lt_trans shape.2.1 (by decide +kernel)) countBound enough none]
  rw [Original.fold_bind, Original.fold_repeat]
  have active : (((repeatSpec maximum).roles.map occurrence.protocol.roles).contains
      (occurrence.protocol.roles 0)) = true := by
    simp []
  simp only [active, ↓reduceIte, SumcheckProverLaws.mask_embedP _ _ rfl maximum]
  simp only [Domain.View.loop, countRead, initialRead, carried, Domain.sortsMatch,
    Domain.Value.sort, Domain.Payload.ty, List.map_cons, List.map_nil,
    beq_self_eq_true, and_true]
  by_cases admitted : count ≤ maximum
  · simp only [admitted, ↓reduceIte]
    rw [List.range_eq_range']
    have loopRule := certificate.loop program routing occurrence context outputs offset maximum handle body
      captured size 0 count dimension enough
      (SumcheckProverLaws.embedP (raw, dimension, 1, []), ⟨[], history⟩)
      (carried context raw dimension 1 [] history) ⟨raw, 1, [], history, rfl, rfl, shape, bounded⟩
    apply loopRule.bind (fun _ _ related => related)
    intro result final returned
    apply Classical.choice
    obtain ⟨nextRaw, width, point, reached, rfl, rfl, nextShape, nextBound⟩ := returned
    refine ⟨?_⟩
    simp only [Original.fold, PIR.Process.interpretState, Domain.View.append, carried,
      Domain.sortsMatch, Domain.Value.sort, Domain.Payload.ty, List.map_cons, List.map_nil,
      beq_self_eq_true, ↓reduceIte]
    exact .done ⟨nextRaw, width, point, reached, rfl, rfl, nextShape, nextBound⟩
  · simp only [admitted, ↓reduceIte, PIR.Process.bind]
    exact .halt .refused

end ZkcSecurity.Realizations.Sumcheck.OriginalProducer
