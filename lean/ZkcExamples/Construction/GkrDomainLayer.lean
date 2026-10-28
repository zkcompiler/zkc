module

public import ZkcExamples.Construction.GkrDomainLoops
public import ZkcExamples.Construction.GkrDomainHelperCalls
public meta import Zkc.Construction.ProcessViewTactic
public meta import Mathlib.Tactic.FailIfNoProgress

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.GkrDomainLayer
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Construction.Uniform Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured GkrSourceProtocol GkrDomainHelpers GkrDomainRounds GkrDomainLoops
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
attribute [local irreducible] PIR.Process.bind SourceProcess.sourceView Domain.callHelper GkrSourceProtocol.helper Domain.View.loop GkrSourceProtocol.rounds GkrSourceProtocol.coefficients

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- One complete reached layer of the actual full artifact. Immutable public
captures are read at their physical coordinates; no relation-validity premise
is required for this transport. -/
noncomputable def layer_step (outer : Env (F := F) (G := G)) (length : outer.length = 40)
    (add mul : List F) (selector width handle index : Nat)
    (addFound : outer[2]? = some (.data (.vector "bls12-381.fr" add)))
    (mulFound : outer[3]? = some (.data (.vector "bls12-381.fr" mul)))
    (selectorFound : outer[5]? = some (.data (.index selector)))
    (widthFound : outer[6]? = some (.data (.index width)))
    (point : List F) (claim : F) (suffix : Hist (F := F) (G := G)) :
    Original.Simulation RoundReturns (fun _ _ => True)
      (SourceProcess.sourceView context (layer {} index handle selector width add mul point claim) (history suffix))
      (((Generated.Constructed.GkrValidator.bodyStep37Body (ringModel F G) program context
        (outer ++ .data (.index index) :: roundValues point claim suffix)).bind
          (yieldValues [94, 95, 91] [.data (.vector "bls12-381.fr"), .data (.field "bls12-381.fr"),
            .transcript context.suite])).interpret operations) := by
  unfold_component_bodies [Generated.Constructed.GkrValidator.bodyStep37Body]
  derive_artifact_binding
    [query_binding (F := F) (G := G),
     (fun outer size layerFound handle bound pending claim suffix countFound initialFound => bind_round (left_loop (F := F) (G := G) outer size index layerFound handle bound pending claim suffix countFound initialFound)),
     (fun outer size layerFound handle bound pending claim suffix countFound initialFound => bind_round (right_loop (F := F) (G := G) outer size index layerFound handle bound pending claim suffix countFound initialFound)),
     (fun outer size layerFound bound point suffix countFound initialFound events equal => bind_point (at_history (coefficient_loop (F := F) (G := G) outer size index layerFound bound point suffix countFound initialFound) events equal)),
     (fun point claim env refs read suffix => GkrDomainHelperCalls.bind_state (GkrDomainHelperCalls.unpackState (F := F) (G := G) point claim env refs read suffix)),
     (fun claim env refs read suffix => GkrDomainHelperCalls.bind_state (GkrDomainHelperCalls.pending (F := F) (G := G) claim env refs read suffix)),
     (fun point claim env refs read suffix => GkrDomainHelperCalls.bind_state (GkrDomainHelperCalls.openPending (F := F) (G := G) point claim env refs read suffix)),
     (fun point env refs read suffix => GkrDomainHelperCalls.bind_vectors (GkrDomainHelperCalls.split (F := F) (G := G) point env refs read suffix)),
     (fun point claim env refs read suffix => GkrDomainHelperCalls.bind_state (GkrDomainHelperCalls.packState (F := F) (G := G) point claim env refs read suffix)),
     (fun xs env refs read suffix => GkrDomainHelperCalls.bind_field (GkrDomainHelperCalls.sum (F := F) (G := G) xs env refs read suffix)),
     (fun xs index selector env refs read suffix => GkrDomainHelperCalls.bind_vector (GkrDomainHelperCalls.selectBlock (F := F) (G := G) xs index selector env refs read suffix)),
     (fun xs point left right env refs read suffix => GkrDomainHelperCalls.bind_field (GkrDomainHelperCalls.evaluateWiring (F := F) (G := G) xs point left right env refs read suffix)),
     (fun xs challenge env refs read suffix => GkrDomainHelperCalls.bind_field (GkrDomainHelperCalls.evaluateCoefficients (F := F) (G := G) xs challenge env refs read suffix)),
     (fun left right challenge env refs read suffix => GkrDomainHelperCalls.bind_vector (GkrDomainHelperCalls.linePoint (F := F) (G := G) left right challenge env refs read suffix))]
    normalizing (
      try simp_all only [TypedABI.get_cons_here, TypedABI.get_cons_there,
        Values.get, Values.get_cons, decide_true, decide_false, ite_true, ite_false]
      repeat' (first
      | (fail_if_no_progress simp_all only [TypedABI.get_cons_here, TypedABI.get_cons_there,
          Values.get, Values.get_cons,
          decide_true, decide_false, ite_true, ite_false])
      | (fail_if_no_progress normalize_component_operations [GkrDomainHelperCalls.tuple40_view, GkrDomainHelperCalls.tuple49_view,
          GkrDomainHelperCalls.tuple40, GkrDomainHelperCalls.tuple49, GkrDomainHelperCalls.empty_view, GkrDomainHelperCalls.append_view_read, GkrDomainHelpers.append (F := F) (G := G),
          Domain.Calculations.fieldAdd (F := F) (G := G),
          Domain.Calculations.fieldMultiply (F := F) (G := G),
          Domain.Calculations.fieldEqual (F := F) (G := G)]
        unfolding [layer, afterCoefficients, sourceView_bind, sourceView_ite, interpret_ite, guard_decide, pointValues, roundValues,
          fieldResult, vectorResult, GkrDomainHelperCalls.stateResult, GkrDomainHelperCalls.vectorsResult, yieldValues, Values.get, Values.get_cons, PIR.Process.interpret_bind,
          PIR.Process.interpret, operations, history, event, SourceProcess.sourceView,
          SourceProcess.receive, SourceProcess.send, SourceProcess.query, PIR.Process.bind_ite,
          GkrSourceCallbacks.leftContext, GkrSourceCallbacks.rightContext,
          GkrVerifier.leftContext, GkrVerifier.rightContext,
          GkrSourceCallbacks.lineConstantSite, GkrSourceCallbacks.lineChallengeSite,
          GkrSourceCallbacks.lineDeliverySite, ProtocolContext.roles,
          Domain.queryOrigin, Domain.templateOrigin, Template.origin, Template.qualify,
          Template.applicationPrefix, Template.repeats, Domain.atCoordinates, Origin.withoutCoordinates,
          context, Context.fiatShamir, Context.suite, Context.contract, Context.request,
          Context.replacement?, Context.query, Context.service, Context.role, Context.message,
          Origin.message, Origin.query, qualifyProtocolSite, List.getElem?_append, length,
          addFound, mulFound, selectorFound, widthFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
          List.isEmpty_cons, List.getD_cons_zero, List.getD_cons_succ, decimal, decimalDigit,
          Payload.ofValue, DomainAdapter.embedPayload, Ty.isHandle, Bool.not_false, Bool.not_true, Bool.false_eq_true, eq_mp_eq_cast, cast_eq,
          List.map_append, Origin.withoutCoordinates])
      | (fail_if_no_progress erw [guard_decide (F := F) (G := G)])
      | (fail_if_no_progress erw [GkrDomainHelperCalls.tuple40_source (F := F) (G := G)])
      | (fail_if_no_progress erw [GkrDomainHelperCalls.tuple40 (F := F) (G := G)])
      | (fail_if_no_progress erw [GkrDomainHelperCalls.tuple49 (F := F) (G := G)])
      | (fail_if_no_progress erw [GkrDomainHelpers.append (F := F) (G := G),
          Domain.Calculations.fieldAdd (F := F) (G := G),
          Domain.Calculations.fieldMultiply (F := F) (G := G),
          Domain.Calculations.fieldEqual (F := F) (G := G)])
      | (fail_if_no_progress erw [Domain.Calculations.fieldAdd (F := F) (G := G)])
      | (fail_if_no_progress erw [Domain.Calculations.fieldMultiply (F := F) (G := G)])
      | (fail_if_no_progress erw [Domain.Calculations.fieldEqual (F := F) (G := G)])))
    solving (first
      | (exact True.intro)
      | (solve | simp only [pointValues, roundValues, Domain.read, List.mapM_cons, List.mapM_nil,
          Bind.bind, Option.bind, Option.bind_some, Option.pure_def, ite_true, ite_false,
          eq_mp_eq_cast, cast_eq, ↓reduceTransport, List.getElem?_append, length,
          List.length_append, List.length_cons, List.length_nil, List.getElem?_cons_zero,
          List.getElem?_cons_succ, List.getElem?_nil, List.cons_append, List.nil_append,
          addFound, mulFound, selectorFound, widthFound, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT]
         <;> rfl)
      | (solve | simp only [history, List.map_append, List.map_cons, List.map_nil, event, Origin.withoutCoordinates,
          Origin.withoutCoordinates, String.reduceBEq, String.reduceEq,
          Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true,
          Nat.reduceLT, decimalDigit, String.reduceAppend,
          List.getD_cons_zero, List.getD_cons_succ] <;> rfl)
      | (unfold RoundReturns
         refine ⟨_, _, _, ?_, rfl⟩
         simp only [history, List.map_append, List.map_cons, List.map_nil, event, Origin.withoutCoordinates,
           Origin.withoutCoordinates]
         try rfl))

end ZkcExamples.Construction.GkrDomainLayer
