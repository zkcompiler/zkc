module

public import ZkcExamples.Construction.GkrDomainRoundReceives
public import ZkcExamples.Structured.Generated.Constructed.GkrValidator
public meta import Zkc.Construction.ProcessViewTactic
public meta import Mathlib.Tactic.FailIfNoProgress

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrDomainRounds
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured GkrSourceProtocol
open GkrDomainPhaseBinding GkrDomainRoundReceives
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def output_step (outer : Env (F := F) (G := G)) (length : outer.length = 35)
    (handle index : Nat) (point : List F) (suffix : Hist (F := F) (G := G)) :
    Original.Simulation PointReturns (fun _ _ => True)
      (SourceProcess.sourceView context (GkrVerifier.outputRound {} handle point) (history suffix))
      (((View.output (ringModel F G) program context
        (outer ++ .data (.index index) :: pointValues point suffix)).bind
          (yieldValues [45, 44] [.data (.vector "bls12-381.fr"), .transcript context.suite])).interpret operations) := by
  unfold View.output
  unfold_component_bodies [Generated.Constructed.GkrValidator.bodyStep34Body]
  derive_artifact_binding [query_binding (F := F) (G := G)] normalizing (
    repeat' (first
    | (fail_if_no_progress normalize_artifact_operations [GkrDomainHelpers.append] unfolding
      [pointValues, yieldValues, GkrVerifier.outputRound, GkrVerifier.outputDelivery,
       guard_decide, PIR.Process.bind_ite, sourceView_ite, interpret_ite, SourceProcess.sourceView, SourceProcess.receive, SourceProcess.send, SourceProcess.query,
       PIR.Process.interpret_bind, PIR.Process.interpret, operations, history, event,
       Domain.queryOrigin, Domain.templateOrigin, Template.origin, Template.qualify, Template.applicationPrefix, Template.repeats,
       Domain.atCoordinates, Origin.withoutCoordinates, context, Context.fiatShamir, Context.suite,
       Context.contract, Context.request, Context.replacement?, Context.query, Context.service,
       Context.role, Context.message, Origin.message, Origin.query,
       GkrVerifier.outputSite, GkrVerifier.outputDeliverySite, qualifyProtocolSite,
       ProtocolContext.roles, List.getElem?_append, length, List.isEmpty_cons,
       Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, GkrVerifier.scalar,
       eq_mp_eq_cast, cast_eq, decimalDigit, left_size, right_size,
       Payload.ofValue, DomainAdapter.embedPayload, Ty.isHandle, Bool.false_eq_true, Bool.not_false,
       entry_metadata, suite_metadata, List.getD_cons_zero, List.getD_cons_succ, decimal,
       List.map_append, Origin.withoutCoordinates])
    | (fail_if_no_progress erw [GkrDomainHelpers.append (F := F) (G := G)])
    | (fail_if_no_progress erw [Domain.Calculations.fieldAdd (F := F) (G := G)])
    | (fail_if_no_progress erw [Domain.Calculations.fieldMultiply (F := F) (G := G)])
    | (fail_if_no_progress erw [Domain.Calculations.fieldEqual (F := F) (G := G)])))
    solving (first
      | rfl
      | (simp only [history, List.map_append, List.map_cons, List.map_nil, event, Origin.withoutCoordinates,
          Origin.withoutCoordinates, String.reduceBEq, String.reduceEq,
          Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true,
          left_size, right_size, Nat.reduceLT, decimalDigit, String.reduceAppend,
          List.getD_cons_zero, List.getD_cons_succ])
      | (
          unfold PointReturns
          refine ⟨_, _, ?_, rfl⟩
          simp only [history, List.map_append, List.map_cons, List.map_nil, event, Origin.withoutCoordinates,
            Origin.withoutCoordinates]
          try rfl))

/-- Exact left degree-two callback, including all three coefficients and
its guard, query, delivery and physical yield. -/
def coefficient_step (outer : Env (F := F) (G := G)) (length : outer.length = 72)
    (layerIndex : Nat) (layerFound : outer[40]? = some (.data (.index layerIndex)))
    (index : Nat) (point : List F) (suffix : Hist (F := F) (G := G)) :
    Original.Simulation PointReturns (fun _ _ => True)
      (SourceProcess.sourceView context (GkrVerifier.lineCoefficient {} point) (history suffix))
      (((View.coefficient (ringModel F G) program context
        (outer ++ .data (.index index) :: pointValues point suffix)).bind
          (yieldValues [80, 79] [.data (.vector "bls12-381.fr"), .transcript context.suite])).interpret operations) := by
  unfold View.coefficient
  unfold_component_bodies [Generated.Constructed.GkrValidator.bodyStep37BodyStep16Body]
  derive_artifact_binding [query_binding (F := F) (G := G)] normalizing (
    repeat' (first
    | (fail_if_no_progress normalize_artifact_operations [GkrDomainHelpers.append] unfolding
      [pointValues, yieldValues, GkrVerifier.lineCoefficient,
       guard_decide, PIR.Process.bind_ite, sourceView_ite, interpret_ite, SourceProcess.sourceView, SourceProcess.receive, SourceProcess.send, SourceProcess.query,
       PIR.Process.interpret_bind, PIR.Process.interpret, operations, history, event,
       Domain.queryOrigin, Domain.templateOrigin, Template.origin, Template.qualify, Template.applicationPrefix, Template.repeats,
       Domain.atCoordinates, Origin.withoutCoordinates, context, Context.fiatShamir, Context.suite,
       Context.contract, Context.request, Context.replacement?, Context.query, Context.service,
       Context.role, Context.message, Origin.message, Origin.query,
       GkrVerifier.lineCoefficientSite, qualifyProtocolSite, layerFound,
       ProtocolContext.roles, List.getElem?_append, length, List.isEmpty_cons,
       Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, GkrVerifier.scalar,
       eq_mp_eq_cast, cast_eq, decimalDigit, left_size, right_size,
       Payload.ofValue, DomainAdapter.embedPayload, Ty.isHandle, Bool.false_eq_true, Bool.not_false,
       entry_metadata, suite_metadata, List.getD_cons_zero, List.getD_cons_succ, decimal,
       List.map_append, Origin.withoutCoordinates])
    | (fail_if_no_progress erw [GkrDomainHelpers.append (F := F) (G := G)])
    | (fail_if_no_progress erw [Domain.Calculations.fieldAdd (F := F) (G := G)])
    | (fail_if_no_progress erw [Domain.Calculations.fieldMultiply (F := F) (G := G)])
    | (fail_if_no_progress erw [Domain.Calculations.fieldEqual (F := F) (G := G)])))
    solving (first
      | rfl
      | (simp only [history, List.map_append, List.map_cons, List.map_nil, event, Origin.withoutCoordinates,
          Origin.withoutCoordinates, String.reduceBEq, String.reduceEq,
          Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true,
          left_size, right_size, Nat.reduceLT, decimalDigit, String.reduceAppend,
          List.getD_cons_zero, List.getD_cons_succ])
      | (
          unfold PointReturns
          refine ⟨_, _, ?_, rfl⟩
          simp only [history, List.map_append, List.map_cons, List.map_nil, event, Origin.withoutCoordinates,
            Origin.withoutCoordinates]
          try rfl))

def left_step (outer : Env (F := F) (G := G)) (length : outer.length = 50)
    (layerIndex : Nat) (layerFound : outer[40]? = some (.data (.index layerIndex)))
    (handle index : Nat) (point : List F) (claim : F) (suffix : Hist (F := F) (G := G)) :
    Original.Simulation RoundReturns (fun _ _ => True)
      (SourceProcess.sourceView context
        (GkrVerifier.round (GkrVerifier.leftContext {}) handle (point, claim)) (history suffix))
      (((View.left (ringModel F G) program context
        (outer ++ .data (.index index) :: roundValues point claim suffix)).bind
          (yieldValues [82, 86, 81] [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"),
            .transcript context.suite])).interpret operations) := by
  unfold View.left
  rw [PIR.Process.interpret_bind, left_decomposition]
  simp only [PIR.Process.bind_assoc]
  unfold GkrVerifier.round GkrVerifier.scalar
  refine receive_continue (GkrVerifier.roundSite (GkrVerifier.leftContext {}) "0") 0 leftTemplate0
    54 53 40 50 layerIndex index (leftOrigin0 layerIndex index)
    _ _ _ _ ?_ ?_ ?_ ?_ (left_resolved0 layerIndex index) (left_projected0 layerIndex index) ?_
  · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
  · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
  · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
  · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
  · intro c0
    unfold GkrVerifier.roundFirst GkrVerifier.scalar
    refine receive_continue (GkrVerifier.roundSite (GkrVerifier.leftContext {}) "1") 0 leftTemplate1
      59 58 40 50 layerIndex index (leftOrigin1 layerIndex index)
      _ _ _ _ ?_ ?_ ?_ ?_ (left_resolved1 layerIndex index) (left_projected1 layerIndex index) ?_
    · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
    · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
    · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
    · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
    · intro c1
      unfold GkrVerifier.roundSecond GkrVerifier.scalar
      refine receive_continue (GkrVerifier.roundSite (GkrVerifier.leftContext {}) "2") 0 leftTemplate2
        64 63 40 50 layerIndex index (leftOrigin2 layerIndex index)
        _ _ _ _ ?_ ?_ ?_ ?_ (left_resolved2 layerIndex index) (left_projected2 layerIndex index) ?_
      · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
      · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
      · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
      · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
      · intro c2
        rw [← PIR.Process.interpret_bind]
        apply GkrDomainRoundTail.left_binding (layerIndex := layerIndex) (index := index)
        all_goals first | rfl | simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]


def right_step (outer : Env (F := F) (G := G)) (length : outer.length = 57)
    (layerIndex : Nat) (layerFound : outer[40]? = some (.data (.index layerIndex)))
    (handle index : Nat) (point : List F) (claim : F) (suffix : Hist (F := F) (G := G)) :
    Original.Simulation RoundReturns (fun _ _ => True)
      (SourceProcess.sourceView context
        (GkrVerifier.round (GkrVerifier.rightContext {}) handle (point, claim)) (history suffix))
      (((View.right (ringModel F G) program context
        (outer ++ .data (.index index) :: roundValues point claim suffix)).bind
          (yieldValues [89, 93, 88] [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"),
            .transcript context.suite])).interpret operations) := by
  unfold View.right
  rw [PIR.Process.interpret_bind, right_decomposition]
  simp only [PIR.Process.bind_assoc]
  unfold GkrVerifier.round GkrVerifier.scalar
  refine receive_continue (GkrVerifier.roundSite (GkrVerifier.rightContext {}) "0") 0 rightTemplate0
    61 60 40 57 layerIndex index (rightOrigin0 layerIndex index)
    _ _ _ _ ?_ ?_ ?_ ?_ (right_resolved0 layerIndex index) (right_projected0 layerIndex index) ?_
  · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
  · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
  · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
  · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
  · intro c0
    unfold GkrVerifier.roundFirst GkrVerifier.scalar
    refine receive_continue (GkrVerifier.roundSite (GkrVerifier.rightContext {}) "1") 0 rightTemplate1
      66 65 40 57 layerIndex index (rightOrigin1 layerIndex index)
      _ _ _ _ ?_ ?_ ?_ ?_ (right_resolved1 layerIndex index) (right_projected1 layerIndex index) ?_
    · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
    · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
    · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
    · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
    · intro c1
      unfold GkrVerifier.roundSecond GkrVerifier.scalar
      refine receive_continue (GkrVerifier.roundSite (GkrVerifier.rightContext {}) "2") 0 rightTemplate2
        71 70 40 57 layerIndex index (rightOrigin2 layerIndex index)
        _ _ _ _ ?_ ?_ ?_ ?_ (right_resolved2 layerIndex index) (right_projected2 layerIndex index) ?_
      · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
      · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
      · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
      · simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]
      · intro c2
        rw [← PIR.Process.interpret_bind]
        apply GkrDomainRoundTail.right_binding (layerIndex := layerIndex) (index := index)
        all_goals first | rfl | simp only [receivedFrame, pointValues, roundValues,
      List.length_append, List.length_cons, List.length_nil, length,
      List.getElem?_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, layerFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      List.cons_append, List.nil_append, ite_true, ite_false]


end ZkcExamples.Construction.GkrDomainRounds
