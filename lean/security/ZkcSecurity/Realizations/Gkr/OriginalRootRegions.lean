module

public import ZkcSecurity.Realizations.Gkr.OriginalRegions
public import ZkcExamples.Structured.GkrInputNormalForms

@[expose] public section
/-! Exact source presentations at the root and terminal input application.
These equations retain the actual occurrence interpreter and all helper stops. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.OriginalRootRegions
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured GkrSourceCallbacks
open ZkcExamples.Construction GkrSourceRouting HonestProducerSource
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem root_body (self : Nat)
    (args : Values (Component (assignment F G)) GkrSourceBodies.gkrSignature.inputs) :
    Occurrence.participant (ringModel F G) GkrSourceViews.program self args =
      (gkrBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers self beforeRoot {} Occurrence.iterations)
        (maskValues self (({} : ProtocolContext).mapScopes GkrSourceViews.gkrDefinition.inputScopes) args).get).bind
        (fun result => .done (maskValues self
          (({} : ProtocolContext).mapScopes GkrSourceViews.gkrDefinition.outputScopes) result)) := by
  rw [participant_body]
  unfold CheckedProtocol.denoteWithOn
  erw [GkrSourceViews.gkrDefinition.body_eq_of_raw _ gkrBody_raw]
  rfl

theorem input_body (ctx : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) GkrSourceBodies.sourceProtocol80Signature.inputs) :
    invokeProtocol (beforeRoot (F := F) (G := G)) GkrSourceBodies.sourceProtocol80Signature ctx self args =
      (GkrInputNormalForms.inputBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers self beforeInput ctx Occurrence.iterations)
        (maskValues self (ctx.mapScopes GkrSourceBodies.sourceProtocol80Signature.inputScopes) args).get).bind
        (fun result => .done (maskValues self
          (ctx.mapScopes GkrSourceBodies.sourceProtocol80Signature.outputScopes) result)) := by
  unfold beforeRoot extendProtocolTableOn
  change invokeProtocol (⟨GkrSourceViews.sourceProtocol80Definition.signature, _⟩ :: _)
    GkrSourceViews.sourceProtocol80Definition.signature ctx self args = _
  rw [invokeProtocol_cons_same]
  unfold CheckedProtocol.denoteWithOn
  erw [GkrSourceViews.sourceProtocol80Definition.body_eq_of_raw _ GkrInputNormalForms.inputBody_raw]
  rfl

theorem validator_input (initial point : List F) (claim : F) :
    invokeProtocol (beforeRoot (F := F) (G := G)) GkrSourceBodies.sourceProtocol80Signature
      (({} : ProtocolContext).enter "label_696e707574" [1]) 1
      (.cons (some initial) (.cons (some point) (.cons (some claim) .nil))) =
    (invoke observedHelpers.closed GkrSourceBodies.sourceHelper84Helper
      (.cons initial (.cons point (.cons claim .nil)))).bind
      (fun result => .done result.present) := by
  rw [input_body]
  simp [GkrInputNormalForms.inputBody, Region.denote, participantMeaningWithOn,
    protocolOperationWithOn, Operands.eval, Regions.denote, Values.get,
    Environment.prepend, Environment.push, SiteObservations.silent, Participant.owned,
    Participant.restrict, ProtocolContext.roles, ProtocolContext.enter, ProtocolContext.mapScopes,
    GkrSourceBodies.sourceProtocol80Signature, roleSubstitution, maskValues,
    RoleFamily.sequence, Values.present, Values.absent, ProtocolOp.results,
    GkrSourceBodies.sourceHelper84Helper, PIR.Process.bind, PIR.Process.bind_assoc]
  apply congrArg (PIR.Process.bind _)
  funext result
  cases result with | cons value rest => cases rest; rfl

end ZkcSecurity.Realizations.Gkr.OriginalRootRegions
