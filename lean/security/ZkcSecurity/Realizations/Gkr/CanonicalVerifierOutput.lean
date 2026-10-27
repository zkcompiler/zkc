module

public import ZkcSecurity.Realizations.Gkr.HonestProducerCurrentVerifier
public import ZkcSecurity.Realizations.Gkr.OccurrenceVerifier

@[expose] public section

/-! The actual root's output-point repeat and terminal input protocol preserve
the complete nominal process. The terminal decision uses independent input-table
mathematics; its source helper is discharged under shape and bounds only. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalVerifier
open Zkc Source Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcExamples.Structured GkrSourceCallbacks SumcheckVerifierHelpers
open HonestProducerSource HonestProducerObserved
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem output_reads (ctx : ProtocolContext) (handle : Nat) (point : List F) :
    (verifierOutputProcess (F := F) (G := G) ctx (some handle) (some point)).interpret Occurrence.actions =
      (((GkrVerifier.outputRound ctx handle point).interpret CommonAdapter.embed).interpret
        Occurrence.actions).bind (fun next => .done (some next)) := by
  simp only [verifierOutputProcess, GkrVerifier.outputRound, GkrVerifier.outputDelivery,
    PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions, PIR.Process.bind,
    GkrRoundsReading.append_plain]
  rfl

theorem output_repeat (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (site : String) (handle count : Nat) (bounded : count ≤ 4) (point : List F) :
    denoteRepeatOn (carriers := uniformCarriers F G) outputSpec ctx (ctx.roles 1) (some count)
      (verifierOutputState (some point)) (.cons (some handle) .nil)
      (fun args => outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
        Occurrence.actions observedHelpers (ctx.roles 1) [] ctx Occurrence.iterations) args.get)
      Occurrence.iterations site =
      (validatorOutput ctx handle (qualifyProtocolSite ctx.applicationPrefix site) 0 count point).bind
        (fun next => .done (verifierOutputState (some next))) := by
  have repeated := observed_repeat (F := F) (G := G) outputSpec ctx (ctx.roles 1) (by simp)
    (.cons (some handle) .nil)
    (fun args => outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
      Occurrence.actions observedHelpers (ctx.roles 1) [] ctx Occurrence.iterations) args.get)
    Occurrence.iterations site
    (fun point : List F => verifierOutputState (some point))
    (fun point => verifierOutputState_masked ctx _ rfl _)
    (fun point _ => (((GkrVerifier.outputRound ctx handle point).interpret CommonAdapter.embed).interpret
      Occurrence.actions)) (by
      intro point index
      rw [output_callback, verifierOutput_process ctx _ rfl separate,
        PIR.Process.interpret_bind, output_reads, PIR.Process.bind_assoc]
      rfl) count bounded _ point (verifierOutputState_masked ctx _ rfl _)
  rw [repeated]
  have folded (start count : Nat) (point : List F) :
      Finite.fold (fun point index => Occurrence.iterations.within
        (qualifyProtocolSite ctx.applicationPrefix site) index
        (((GkrVerifier.outputRound ctx handle point).interpret CommonAdapter.embed).interpret Occurrence.actions))
        (List.range' start count) point =
      validatorOutput (G := G) ctx handle (qualifyProtocolSite ctx.applicationPrefix site) start count point := by
    induction count generalizing start point with
    | zero => rfl
    | succ count ih =>
      rw [List.range'_succ, Finite.fold, validatorOutput]
      apply congrArg (PIR.Process.bind _)
      funext next
      exact ih (start + 1) next
  rw [folded]

/-- The actual single-role input application is silent and returns precisely
its checked multilinear-extension comparison. -/
theorem input_reads (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) (point : List F) (claim : F)
    (pointSize : point.length = encoding.width) :
    invokeProtocol (beforeRoot (F := F) (G := G)) GkrSourceBodies.sourceProtocol80Signature
      (({} : ProtocolContext).enter "label_696e707574" [1]) 1
      (.cons (some encoding.inputs) (.cons (some point) (.cons (some claim) .nil))) =
      .done (.cons (some (decide (extension encoding.width encoding.circuit.inputs
        (coordinates encoding.width point) = claim))) .nil) := by
  have body : invokeProtocol (beforeRoot (F := F) (G := G))
      GkrSourceBodies.sourceProtocol80Signature (({} : ProtocolContext).enter "label_696e707574" [1]) 1
      (.cons (some encoding.inputs) (.cons (some point) (.cons (some claim) .nil))) =
      GkrInputNormalForms.inputBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers
          1 beforeInput (({} : ProtocolContext).enter "label_696e707574" [1]) Occurrence.iterations)
        ((.cons (some encoding.inputs) (.cons (some point) (.cons (some claim) .nil))) :
          Values (Component (assignment F G)) GkrInputNormalForms.inputInputs).get := by
    change invokeProtocol (⟨GkrSourceViews.sourceProtocol80Definition.signature, _⟩ :: beforeInput)
      GkrSourceViews.sourceProtocol80Definition.signature _ _ _ = _
    rw [invokeProtocol_cons_same]
    unfold CheckedProtocol.denoteWithOn
    erw [GkrSourceViews.sourceProtocol80Definition.body_eq_of_raw _ GkrInputNormalForms.inputBody_raw]
    change (GkrInputNormalForms.inputBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers
        1 beforeInput (({} : ProtocolContext).enter "label_696e707574" [1]) Occurrence.iterations)
        ((.cons (some encoding.inputs) (.cons (some point) (.cons (some claim) .nil))) :
          Values (Component (assignment F G)) GkrInputNormalForms.inputInputs).get).bind
        (fun result => .done (maskValues 1 [[1]] result)) = _
    have out (result : Values (Component (assignment F G)) [.boolean]) :
        maskValues 1 [[1]] result = result := by
      cases result with | cons value rest => cases rest; rfl
    simp only [out, PIR.Process.bind_done]
  rw [body]
  have small : encoding.width < 64 := by have := admitted.2.2.1; omega
  have inputBound : encoding.inputs.length < indexLimit := by
    rw [admitted.1.1]
    exact Nat.pow_lt_pow_right (by decide) small
  unfold GkrInputNormalForms.inputBody
  simp only [Region.denote, participantMeaningWithOn, protocolOperationWithOn,
    Operands.eval, Regions.denote, Values.get_cons, Environment.prepend, Environment.push,
    SiteObservations.silent, PIR.Process.bind, PIR.Process.bind_done, Participant.owned,
    ProtocolContext.roles, ProtocolContext.enter, roleSubstitution, RoleFamily.sequence,
    observed_helper, GkrSourceVerifier.terminal_plain encoding.width encoding.inputs point
      encoding.circuit.inputs claim (encoding.inputs_decode admitted.1) pointSize small inputBound,
    PIR.Process.interpret, Values.present, Values.get, Values.split, ProtocolOp.results,
    maskValues, Participant.restrict, ProtocolContext.mapScopes, Function.comp_apply,
    id_eq, roleSubstitution, List.getElem?_cons_zero, Option.getD_some, ite_true, Option.bind_some, Option.pure_def, bind, pure]
  rfl

end ZkcSecurity.Realizations.Gkr.CanonicalVerifier
