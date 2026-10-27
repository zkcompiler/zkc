module

public import ZkcSecurity.Realizations.Gkr.OriginalRegions
public import ZkcExamples.Construction.GkrOriginalLine
public meta import Zkc.Construction.OriginalComponentReduction

@[expose] public section
/-! Composition of the two qualified round components and the fully indexed
coefficient component inside the actual layer callback. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.OriginalLayer
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks GkrRoundsNormalForms
open ZkcExamples.Construction GkrSourceRouting HonestProducerSource
attribute [local irreducible] coefficientBody
attribute [local irreducible] Generated.Producer.bodyStep2Body Generated.Validator.bodyStep37Body
attribute [local irreducible] Original.receive Original.send Original.query
attribute [local irreducible] Original.fold invoke invokeProtocol denoteRepeatOn
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def producerCarried (point : List F) (history : Domain.History (uniformCarriers F G)) :
    Domain.Environment (uniformCarriers F G) :=
  [.data (.vector scalarDomain point), .transcript context.suite history]

def ProducerReturns
    (source : Values (Component (assignment F G)) layerState × Original.State (uniformCarriers F G))
    (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ point history, source = (proverLayerState (some point), ⟨[], history⟩) ∧
    frame = producerCarried (F := F) (G := G) point history


def producer (handle layer : Nat) (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = 10) (initial add mul : List F) (layers selector width : Nat)
    (inputRead : captured[0]? = some (.data (.vector scalarDomain initial)))
    (addRead : captured[1]? = some (.data (.vector scalarDomain add)))
    (mulRead : captured[2]? = some (.data (.vector scalarDomain mul)))
    (layersRead : captured[3]? = some (.data (.index layers)))
    (selectorRead : captured[4]? = some (.data (.index selector)))
    (widthRead : captured[5]? = some (.data (.index width)))
    (point : List F) (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation
      (Original.IterationReturns (ProducerReturns (F := F) (G := G)) [] "s57" layer [48, 47]
        [.data (.vector scalarDomain), .transcript context.suite])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .producer)
        (layerBody.denote
          (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
            observedHelpers 0 beforeRoot {} Occurrence.iterations)
          ((.cons (some layer) ((proverLayerState (some point)).append
            (.cons (some initial) (.cons (some add) (.cons (some mul) (.cons (some layers)
              (.cons (some selector) (.cons (some width) (.cons none .nil))))))))) :
            Values (Component (assignment F G)) (.index :: (layerState ++ layerCaptures))).get)
        ⟨[⟨"s57", layer⟩], history⟩)
      (Generated.Producer.bodyStep2Body (ringModel F G) GkrSourceViews.program context
        (captured ++ .data (.index layer) :: producerCarried (F := F) (G := G) point history)) := by
  apply Classical.choice
  obtain ⟨replacement, profile⟩ := Original.Routing.draw_profile (line_draw handle layer .producer)
  constructor
  unfold layerBody
  have roundsLeft := OriginalRegions.producer_rounds (F := F) (G := G) .left
  have roundsRight := OriginalRegions.producer_rounds (F := F) (G := G) .right
  dsimp only [roundContext, GkrVerifier.leftContext, ProtocolContext.enter] at roundsLeft
  dsimp only [roundContext, GkrVerifier.rightContext, ProtocolContext.enter] at roundsRight
  simp only [GkrSourceBodies.roundsSignature, qualify_root] at roundsLeft roundsRight
  have lineSend := GkrOriginalLine.producer_send (F := F) (G := G) handle layer
  have lineReceive := GkrOriginalLine.producer_receive (F := F) (G := G) handle layer
  dsimp only [GkrOriginalLine.frames, GkrOriginalLine.constantSite,
    GkrOriginalLine.challengeSite, GkrOriginalLine.deliverySite, scalarDomain] at lineSend lineReceive
  have suite : context.suite = "merlin3.bls12-381.fr64be/0" := rfl
  have compiledConstant := GkrOriginalLine.compiled_constant layer
  have compiledDraw := GkrOriginalLine.compiled_draw layer
  have compiledDelivery := GkrOriginalLine.compiled_delivery layer
  dsimp only [template12] at compiledConstant
  dsimp only [template14] at compiledDraw
  dsimp only [template15] at compiledDelivery
  unfold_component_bodies [Generated.Producer.bodyStep2Body]
  derive_artifact_binding [GkrOriginalHelpers.continuation (F := F) (G := G),
      OriginalRounds.producerRepeat (F := F) (G := G) .left handle layer,
      OriginalRounds.producerRepeat (F := F) (G := G) .right handle layer,
      OriginalCoefficient.producerRepeat (F := F) (G := G) handle layer] normalizing (
    saturate_artifact (
      unfold_component_bodies [Generated.Producer.bodyStep2Body]
      apply Classical.choice
      try cases_type* Values
      simp (config := { failIfUnchanged := false }) only
        [GkrOriginalRounds.ProducerReturns, GkrOriginalCoefficient.ProducerReturns] at *
      try casesm* ∃ _, _
      try casesm* _ ∧ _
      try casesm* ∃ _, _
      try casesm* _ ∧ _
      try subst_vars
      constructor
      simp (config := { failIfUnchanged := false }) only
        [↓Original.simplifyBindHead, ↓Original.simplifyRegionHead, ↓Original.stopAtCall, ↓Original.stopAtViewLoop,
         ↓Original.stopAtViewHelper, Original.fold_bind, Original.fold_done,
         observed_helper, ↓OriginalRegions.coefficient_table, PIR.Process.interpret_identity,
         roundsLeft, roundsRight, roundsPresentation,
         PIR.Process.bind_assoc, Values.present, Values.get, ↓Values.reify_get, ↓Environment.toValues_get]
      normalize_component_operations
        [↓Values.reify_get, ↓Environment.toValues_get, ↓Original.simplifyBindHead, ↓Original.reducePresent, ↓Original.reducePrepend,
         ↓Original.reducePush, ↓Original.reduceSequence, ↓Original.simplifyRegionHead, ↓Original.stopAtRepeat,
         ↓Original.stopAtViewLoop, ↓Original.stopAtViewHelper, roundsLeft, roundsRight,
         lineSend,
         lineReceive,
         compiledConstant, compiledDraw,
         compiledDelivery, GkrOriginalLine.draw_request]
        unfolding [participantMeaningWithOn, protocolOperationWithOn,
          Participant.owned, RoleFamily.sequence, Participant.restrict, Participant.guard,
          Participant.exchange, Participant.query, Evaluation.componentOperationOn,
          strictComponent, Evaluation.meaningOn, Evaluation.operationOn, Op.calculationRegions,
          profile, suite, Nat.reduceEqDiff, qualify_root, GkrOriginalCoefficient.outer,
          ProtocolContext.roles, ProtocolContext.contains, ProtocolContext.enter,
          GkrSourceBodies.roundsSignature, roleSubstitution, List.range_succ, List.range_zero,
          List.any_cons, List.any_nil, Nat.reduceBEq,
          Values.absent, Values.present, Values.split, Values.append, Values.get,
          TypedABI.get_cons_here, TypedABI.get_cons_there, proverState, verifierState, proverCoefficientState, verifierCoefficientState, proverLayerState,
          verifierLayerState, Environment.prepend, Environment.push,
          List.contains_cons, List.contains_nil,
          Operands.eval, Regions.denote, SiteObservations.silent, ProtocolOp.results, Op.results,
          producerCarried, GkrOriginalRounds.producerCarried, GkrOriginalCoefficient.carried,
          Original.encodeHelperResult, Domain.encodeValues, Ty.isService,
          Original.foldActionCall, Original.foldActionDone, Original.foldActionHalt,
          Original.operations, Original.fieldReply, Request.draw, Domain.Raw,
          PIR.Process.interpret_bind, Original.fold_bind, Original.fold_done, Original.foldIf,
          PIR.Process.bind_ite, List.append_assoc]
      simp (config := { failIfUnchanged := false }) (disch := omega) only
        [↓Original.simplifyBindHead, ↓Original.stopAtCall, List.cons_append, List.nil_append, List.length_cons,
         List.length_nil, List.length_append, List.getElem?_append_left, List.getElem?_append_right,
         size, inputRead, addRead, mulRead, layersRead, selectorRead, widthRead,
         Nat.add_sub_cancel_left, Nat.sub_self, List.getElem?_cons_zero, List.getElem?_cons_succ]))

    solving (first
      | solve | exact fun index => GkrOriginalRoutes.round _ _ _ _ index
      | solve | exact fun index => GkrOriginalRoutes.coefficient _ _ _ index
      | solve | (intro process frame retained
                 apply ArtifactBinding.captures_trans (inner := retained)
                 simp [ArtifactBinding.Captures, List.append_assoc])
      | solve | (try casesm* ∃ _, _
                 try casesm* _ ∧ _
                 try subst_vars
                 simp [ArtifactBinding.Captures, List.append_assoc])
      | solve | simp [producerCarried, GkrOriginalRounds.producerCarried, Original.encodeHelperResult, Domain.encodeValues, Domain.Value.encode, Domain.Payload.ofValue, Ty.isService, List.length_append, size]
      | solve | (simp (disch := omega) only [Domain.read, List.mapM_cons, List.mapM_nil, Original.encodeHelperResult, Domain.encodeValues, Domain.Value.encode, Domain.Payload.ofValue,
          Ty.isService, producerCarried, GkrOriginalRounds.producerCarried, OriginalRounds.producerInitial, OriginalRounds.producerOffset, List.getElem?_append_left, List.getElem?_append_right,
          size, inputRead, addRead, mulRead, layersRead, selectorRead, widthRead,
          List.append_assoc, List.cons_append, List.nil_append, List.length_append,
          List.length_cons, List.length_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Nat.sub_self, Nat.add_sub_cancel_left, Bind.bind, Option.bind, Option.pure_def] <;> rfl)
      | solve | decide +kernel
      | (unfold Original.IterationReturns ProducerReturns
         refine ⟨rfl, _, ?_, rfl, _, _, rfl, rfl⟩
         simp (disch := omega) only [Domain.read, producerCarried, List.mapM_cons,
           List.mapM_nil, List.getElem?_append_right, size, List.getElem?_cons_zero,
           List.getElem?_cons_succ, Bind.bind, Option.bind, Option.pure_def]
         rfl))

def producerRepeat (handle : Nat) (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = 10) (initial add mul : List F) (layers selector width : Nat)
    (inputRead : captured[0]? = some (.data (.vector scalarDomain initial)))
    (addRead : captured[1]? = some (.data (.vector scalarDomain add)))
    (mulRead : captured[2]? = some (.data (.vector scalarDomain mul)))
    (layersRead : captured[3]? = some (.data (.index layers)))
    (selectorRead : captured[4]? = some (.data (.index selector)))
    (widthRead : captured[5]? = some (.data (.index width)))
    (point : List F) (history : Domain.History (uniformCarriers F G))
    (initialRead : Domain.read captured [8, 9] = some (producerCarried point history)) :
    Original.Simulation
      (fun original final => ∃ next, ProducerReturns original next ∧ final = captured ++ next)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle .producer)
        (denoteRepeatOn layerSpec {} 0 (some layers) (proverLayerState (some point))
          (.cons (some initial) (.cons (some add) (.cons (some mul) (.cons (some layers)
        (.cons (some selector) (.cons (some width) (.cons none .nil)))))))
          (fun args => layerBody.denote
            (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
              observedHelpers 0 beforeRoot {} Occurrence.iterations) args.get) Occurrence.iterations "s57") ⟨[], history⟩)
      (Generated.Producer.bodyStep2 (ringModel F G) GkrSourceViews.program context captured) := by
  change Original.Simulation _ _ _
    (Domain.View.loop 4 [48, 47] 3 [8, 9] [.data (.vector scalarDomain), .transcript context.suite]
      (Generated.Producer.bodyStep2Body (ringModel F G) GkrSourceViews.program context) captured)
  apply Original.Simulation.occurrenceRepeat (routing handle .producer) layerSpec {} 0
    (captures := (.cons (some initial) (.cons (some add) (.cons (some mul) (.cons (some layers)
        (.cons (some selector) (.cons (some width) (.cons none .nil))))))))
    (sourceBody := (fun args => layerBody.denote
            (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
              observedHelpers 0 beforeRoot {} Occurrence.iterations) args.get)) (site := "s57") (relation := ProducerReturns)
  · rfl
  · intro original frame related
    obtain ⟨point, history, rfl, rfl⟩ := related
    exact ⟨point, history, rfl, rfl⟩
  · intro value state frame index related
    apply Classical.choice
    obtain ⟨point, history, pair, rfl⟩ := related
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    refine ⟨?_⟩
    rw [proverLayerState_masked {} 0 rfl]
    exact producer handle index captured size initial add mul layers selector width
      inputRead addRead mulRead layersRead selectorRead widthRead point history
  · intro original frame related
    obtain ⟨point, history, rfl, rfl⟩ := related
    rfl
  · exact layersRead
  · exact initialRead
  · rfl
  · exact ⟨point, history, rfl, rfl⟩


end ZkcSecurity.Realizations.Gkr.OriginalLayer
