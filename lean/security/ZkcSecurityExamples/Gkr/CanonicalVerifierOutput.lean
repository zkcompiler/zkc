module

public import ZkcSecurityExamples.Gkr.HonestProducerCurrent
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import Zkc.Protocols.Gkr.Source.VerifierProcess
public import ZkcExamples.Structured.GkrSourceVerifier
public import ZkcSecurityExamples.Gkr.OccurrenceVerifier

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
open ZkcExamples.Structured Generated.Presentations.Gkr.Root SumcheckVerifierHelpers
open HonestProducerSource HonestProducerObserved
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

theorem output_reads (ctx : ProtocolContext) (handle : Nat) (point : List F) :
    (verifierOutputProcess (F := F) (G := G) ctx (some handle) (some point)).interpret Occurrence.actions =
      (((GkrVerifier.outputRound ctx handle point).interpret CommonAdapter.embed).interpret
        Occurrence.actions).bind (fun next => .done (some next)) := by
  simp only [verifierOutputProcess, Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
    Generated.Presentations.Gkr.program, GkrSourceViews.program, GkrVerifier.outputRound, GkrVerifier.outputDelivery,
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
  have repeated := Zkc.Source.Structured.LoopPresentation.present (carriers := uniformCarriers F G) outputSpec ctx (ctx.roles 1) (by simp)
    (.cons (some handle) .nil)
    (fun args => outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
      Occurrence.actions observedHelpers (ctx.roles 1) [] ctx Occurrence.iterations) args.get)
    Occurrence.iterations site
    (fun point : List F => verifierOutputState (some point))
    (fun point => verifierOutputState_masked ctx _ rfl _)
    (fun point _ => (((GkrVerifier.outputRound ctx handle point).interpret CommonAdapter.embed).interpret
      Occurrence.actions)) (by
      intro point index
      erw [output_occurrence (F := F) (G := G) ctx (ctx.roles 1) []
        (.cons (some index) ((verifierOutputState (some point)).append (.cons (some handle) .nil))), verifierOutput_process ctx _ rfl (.ofSeparate separate (by decide)),
        PIR.Process.interpret_bind, output_reads, PIR.Process.bind_assoc]) count bounded _ point (verifierOutputState_masked ctx _ rfl _)
  rw [repeated]
  rw [Zkc.Source.Structured.LoopPresentation.foldCounted _
    (validatorOutput (G := G) ctx handle (qualifyProtocolSite ctx.applicationPrefix site))
    (fun _ _ => rfl) (fun _ _ _ => rfl)]

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
      Generated.Presentations.Gkr.Input.inputBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers
          1 beforeInput (({} : ProtocolContext).enter "label_696e707574" [1]) Occurrence.iterations)
        ((.cons (some encoding.inputs) (.cons (some point) (.cons (some claim) .nil))) :
          Values (Component (assignment F G)) Generated.Presentations.Gkr.Input.inputInputs).get := by
    change invokeProtocol (⟨GkrSourceViews.sourceProtocol80Definition.signature, _⟩ :: beforeInput)
      GkrSourceViews.sourceProtocol80Definition.signature _ _ _ = _
    rw [invokeProtocol_cons_same]
    unfold CheckedProtocol.denoteWithOn
    erw [GkrSourceViews.sourceProtocol80Definition.body_eq_of_raw _ Generated.Presentations.Gkr.Input.inputBody_raw]
    change (Generated.Presentations.Gkr.Input.inputBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers
        1 beforeInput (({} : ProtocolContext).enter "label_696e707574" [1]) Occurrence.iterations)
        ((.cons (some encoding.inputs) (.cons (some point) (.cons (some claim) .nil))) :
          Values (Component (assignment F G)) Generated.Presentations.Gkr.Input.inputInputs).get).bind
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
  have normalized := Generated.Presentations.Gkr.Input.verifier_observed (F := F) (G := G)
    (({} : ProtocolContext).enter "label_696e707574" [1]) (.only _) beforeInput beforeInput_masked
    (some encoding.inputs) (some point) (some claim)
  refine normalized.trans ?_
  simp only [Generated.Presentations.Gkr.Input.verifierForm, NormalForm.Form.denoteOn,
    NormalForm.Form.denoteWithOn, NormalForm.Comps.eval, NormalForm.Comp.eval,
    NormalForm.Term.eval, NormalForm.Terms.eval, NormalForm.entryAt,
    NormalForm.firstEntry, NormalForm.laterEntries, Op.evalTotal,
    Generated.Presentations.Gkr.payload, Generated.Presentations.Gkr.program, GkrSourceViews.program,
    Region.denote, participantMeaningWithOn, protocolOperationWithOn,
    Operands.eval, Regions.denote, Values.get_cons, Environment.prepend, Environment.push,
    SiteObservations.silent, PIR.Process.bind, PIR.Process.bind_done, Participant.owned,
    ProtocolContext.roles, ProtocolContext.enter, roleSubstitution, RoleFamily.sequence,
    OccurrencePresentation.closed_helper, GkrSourceVerifier.terminal_plain encoding.width encoding.inputs point
      encoding.circuit.inputs claim (encoding.inputs_decode admitted.1) pointSize small inputBound,
    PIR.Process.interpret, Values.present, Values.get, Values.split, ProtocolOp.results,
    maskValues, Participant.restrict, ProtocolContext.mapScopes, Function.comp_apply,
    id_eq, roleSubstitution, List.getElem?_cons_zero, Option.getD_some, ite_true, Option.bind_some, Option.pure_def, bind, pure]

end ZkcSecurity.Realizations.Gkr.CanonicalVerifier
