module

public import ZkcSecurity.Realizations.Gkr.OriginalCertificateFrames
public import ZkcSecurity.Realizations.Gkr.OriginalProducerLayer
public import ZkcSecurity.Realizations.Gkr.OriginalOutput
public import ZkcSecurity.Realizations.Gkr.OriginalRootRegions
public import ZkcExamples.Structured.GkrProverContinuation
public import Zkc.Construction.OriginalFrameRelations
public import Zkc.Construction.OriginalExecution
public meta import Zkc.Construction.OriginalComponentReduction

@[expose] public section
/-! Complete nominal certificates for the actual authored GKR pair. Each root
uses the same all-reply occurrence process and the complete constructed view. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.OriginalCertificates
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks
open ZkcExamples.Construction GkrSourceRouting HonestProducerSource
attribute [local irreducible] outputBody layerBody
attribute [local irreducible] Generated.Producer.body Generated.Validator.body
attribute [local irreducible] Original.fold invoke invokeProtocol denoteRepeatOn
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Every physical slot of the completed producer frame is fixed, including
both nested-loop results and histories; the original optional return is absent. -/
def ProducerFrameReturns (inputs : Domain.Environment (uniformCarriers F G))
    (source : SourceResult (F := F) (G := G)) (frame : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ empty outputPoint outputHistory point history,
    source = (.cons none .nil, ⟨[], history⟩) ∧
    frame = inputs ++ [.data (.vector scalarDomain empty), .data (.vector scalarDomain outputPoint),
      .transcript context.suite outputHistory, .data (.vector scalarDomain point), .transcript context.suite history]

def producerBody (handle : Nat) (initial add mul : List F) (layers selector width : Nat)
    (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation
      (ProducerFrameReturns (producerInputs initial add mul layers selector width history))
      (fun _ frame => ArtifactBinding.Captures (producerInputs initial add mul layers selector width history) frame)
      (Original.fold (routing handle .producer)
        (Occurrence.participant (ringModel F G) GkrSourceViews.program 0
          (GkrProverContinuation.inputs (G := G) initial add mul layers selector width)) ⟨[], history⟩)
      (Generated.Producer.body (ringModel F G) GkrSourceViews.program context
        (producerInputs initial add mul layers selector width history)) := by
  rw [OriginalRootRegions.root_body]
  have masked : maskValues 0 (({} : ProtocolContext).mapScopes GkrSourceViews.gkrDefinition.inputScopes)
      (GkrProverContinuation.inputs (G := G) initial add mul layers selector width) =
      GkrProverContinuation.inputs (G := G) initial add mul layers selector width := by rfl
  rw [masked]
  have expansion : gkrBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers 0 beforeRoot {} Occurrence.iterations)
      (GkrProverContinuation.inputs (G := G) initial add mul layers selector width).get = ?_ := by
    derive_process
    all_goals exact Region.Derivation.identity _ _ _
  rw [expansion]
  clear expansion masked
  unfold_component_bodies [Generated.Producer.body]
  derive_artifact_binding [GkrOriginalHelpers.continuation (F := F) (G := G),
      OriginalOutput.producerRepeat (F := F) (G := G) handle, OriginalLayer.producerRepeat (F := F) (G := G) handle]
    normalizing (
      saturate_artifact (
        unfold_component_bodies [Generated.Producer.body]
        apply Classical.choice
        try cases_type* Values
        simp (config := { failIfUnchanged := false }) only
          [GkrOriginalOutput.Returns, OriginalLayer.ProducerReturns] at *
        try casesm* ∃ _, _
        try casesm* _ ∧ _
        try subst_vars
        constructor
        simp (config := { failIfUnchanged := false }) only
          [↓Original.simplifyBindHead, ↓Original.stopAtCall, ↓Original.stopAtViewLoop,
           ↓Original.stopAtViewHelper, Original.fold_bind, Original.fold_done, observed_helper,
           OriginalRegions.output_table, PIR.Process.interpret_identity, PIR.Process.bind_assoc,
           Values.present, Values.get, ↓Values.reify_get, ↓Environment.toValues_get]
        normalize_component_operations
          [↓Values.reify_get, ↓Environment.toValues_get, ↓Original.simplifyBindHead, ↓Original.reducePresent, ↓Original.reducePrepend,
           ↓Original.reducePush, ↓Original.reduceSequence, ↓Original.stopAtRegion,
           ↓Original.stopAtViewLoop, ↓Original.stopAtViewHelper]
          unfolding [participantMeaningWithOn, protocolOperationWithOn,
            Participant.owned, RoleFamily.sequence, Participant.restrict, Participant.guard,
            Participant.exchange, Participant.query, Evaluation.componentOperationOn,
            strictComponent, Evaluation.meaningOn, Evaluation.operationOn, Op.calculationRegions,
            Nat.reduceEqDiff, qualify_root, ProtocolContext.roles, ProtocolContext.contains, ProtocolContext.enter,
            roleSubstitution, GkrSourceBodies.sourceProtocol80Signature,
            List.contains_cons, List.contains_nil,
            List.range_succ, List.range_zero, List.any_cons, List.any_nil, Nat.reduceBEq,
            Values.absent, Values.present, Values.split, Values.append, Values.get,
            GkrOriginalOutput.values, proverLayerState, verifierLayerState,
            TypedABI.get_cons_here, TypedABI.get_cons_there, Environment.prepend, Environment.push,
            Operands.eval, Regions.denote, SiteObservations.silent, ProtocolOp.results, Op.results,
            producerInputs, GkrProverContinuation.inputs, Original.encodeHelperResult,
            Domain.encodeValues, Ty.isService, maskValues, ProtocolContext.mapScopes,
            Original.operations, PIR.Process.interpret_bind, Original.fold_bind,
            Original.fold_done, Original.foldIf, PIR.Process.bind_ite, List.append_assoc,
            Primitive.evaluate, primitiveOutcome]
        simp (config := { failIfUnchanged := false }) only
          [↓Original.simplifyBindHead, ↓Original.stopAtCall, List.cons_append, List.nil_append,
           List.getElem?_cons_zero, List.getElem?_cons_succ]))
    solving (first
      | solve | decide +kernel
      | solve | exact fun index => GkrOriginalRoutes.output _ _ index
      | solve | (intro process frame retained
                 apply ArtifactBinding.captures_trans (inner := retained)
                 simp [ArtifactBinding.Captures, producerInputs, List.append_assoc])
      | solve | (try casesm* ∃ _, _
                 try casesm* _ ∧ _
                 try subst_vars
                 simp [ArtifactBinding.Captures, producerInputs, List.append_assoc])
      | solve | (simp [producerInputs, Original.encodeHelperResult, Domain.encodeValues,
          Domain.Value.encode, Domain.Payload.ofValue, Ty.isService, GkrOriginalOutput.carried,
          OriginalLayer.producerCarried, Domain.read, List.mapM_cons, List.mapM_nil,
          Bind.bind, Option.bind, Option.pure_def, List.append_assoc] <;> rfl)
      | (unfold ProducerFrameReturns
         rename_i empty outputPoint outputHistory point finalHistory
         refine ⟨empty, outputPoint, outputHistory, point, finalHistory, ?_, ?_⟩
         · simp
         · simp only [producerInputs, Original.encodeHelperResult, Domain.encodeValues,
             Domain.Value.encode, Domain.Payload.ofValue, Ty.isService, GkrOriginalOutput.carried,
             OriginalLayer.producerCarried, List.append_assoc, List.cons_append, List.nil_append]
           rfl))

end ZkcSecurity.Realizations.Gkr.OriginalCertificates
