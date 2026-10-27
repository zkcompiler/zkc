module

public import ZkcSecurity.Realizations.Gkr.HonestProducerSource
public import ZkcExamples.Structured.GkrSourceContinuation

@[expose] public section

/-! The actual current validator with its original nested iteration effects.
Admission and pure helper computation are checked before the live source loops. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.OccurrenceVerifier
open Zkc Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured
open PrimitiveLibrary SumcheckVerifierHelpers
open ZkcExamples.Structured GkrSourceCallbacks HonestProducerSource
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem present_cons {ty : Ty} {types : List Ty}
    (value : assignment F G ty) (rest : Values (assignment F G) types) :
    (Values.cons value rest).present = Values.cons (some value) rest.present := rfl

theorem body (initial outputs add mul : List F) (layers selector width handle : Nat) :
    Occurrence.participant (ringModel F G) GkrSourceViews.program 1
      (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle) =
    GkrSourceBodies.gkrBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers 1 beforeRoot {} Occurrence.iterations)
      (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle).get := by
  rw [participant_body]
  unfold CheckedProtocol.denoteWithOn
  erw [GkrSourceViews.gkrDefinition.body_eq_of_raw _ GkrSourceViews.gkr_raw]
  have masked : maskValues 1 (({} : ProtocolContext).mapScopes GkrSourceViews.gkrDefinition.inputScopes)
      (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle) =
      GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle := by rfl
  rw [masked]
  have out (values : Values (Component (assignment F G)) [.boolean]) :
      maskValues 1 (({} : ProtocolContext).mapScopes GkrSourceViews.gkrDefinition.outputScopes) values = values := by
    cases values with | cons value rest => cases rest; rfl
  simp only [out, PIR.Process.bind_done]

def process (initial outputs add mul : List F) (layers selector width handle : Nat) :
    PIR.Process (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) [.boolean]) :=
  (invoke observedHelpers.closed GkrSourceBodies.emptyHelper .nil).bind fun empty =>
  (denoteRepeatOn (carriers := uniformCarriers F G) outputSpec {} 1 (some width)
    (.cons (some (empty.get .here)) (.cons none .nil)) (.cons (some handle) .nil)
    (fun args => outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 1 beforeRoot {} Occurrence.iterations) args.get) Occurrence.iterations "s37").bind fun output =>
  match output.get .here with
  | none => .halt .incomplete
  | some point =>
    (invoke observedHelpers.closed GkrSourceBodies.evaluateHelper (.cons outputs (.cons point .nil))).bind fun claim =>
    (invoke observedHelpers.closed GkrSourceBodies.sourceHelper19Helper
      (.cons point (.cons (claim.get .here) .nil))).bind fun packed =>
    (denoteRepeatOn (carriers := uniformCarriers F G) layerSpec {} 1 (some layers)
      (.cons (output.get (.there .here)) (.cons (some (packed.get .here))
        (.cons (some (packed.get (.there .here))) .nil)))
      (.cons (some initial) (.cons (some add) (.cons (some mul) (.cons (some layers)
        (.cons (some selector) (.cons (some width) (.cons (some handle) .nil)))))))
      (fun args => layerBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 1 beforeRoot {} Occurrence.iterations) args.get) Occurrence.iterations "s57").bind fun final =>
    invokeProtocol beforeRoot
      GkrSourceBodies.sourceProtocol80Signature
      (({} : ProtocolContext).enter "label_696e707574" [1]) 1
      (.cons (some initial) (.cons (final.get (.there .here))
        (.cons (final.get (.there (.there .here))) .nil)))


theorem admitted (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (initialShape : initial.length = 2 ^ width) (outputShape : outputs.length = 2 ^ width)
    (addShape : add.length = 2 ^ (selector + width + width + width))
    (mulShape : mul.length = 2 ^ (selector + width + width + width))
    (dimensions : selector + width + width + width < 64)
    (capacity : layers ≤ 2 ^ selector) :
    Occurrence.participant (ringModel F G) GkrSourceViews.program 1 (GkrSourceAdmission.inputs (G := G) initial outputs add mul layers selector width handle) =
      process initial outputs add mul layers selector width handle := by
  rw [body]
  have sameBody : GkrSourceBodies.gkrBody = GkrSourceCallbacks.gkrBody := by rfl
  rw [sameBody]
  have widthSmall : width < indexLimit := lt_of_le_of_lt widthBound (by decide)
  have layerSmall : layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have selectorSmall : selector < 64 := by omega
  have widthDimension : width < 64 := by omega
  have totalSmall : selector + width + width + width < indexLimit :=
    lt_trans dimensions (by decide)
  have selectorIndex : selector < indexLimit := lt_trans selectorSmall (by decide)
  have capacityBound : 2 ^ selector < indexLimit :=
    Nat.pow_lt_pow_right (by decide) selectorSmall
  have tableBound : 2 ^ width < indexLimit :=
    Nat.pow_lt_pow_right (by decide) widthDimension
  have wiringBound : 2 ^ (selector + width + width + width) < indexLimit :=
    Nat.pow_lt_pow_right (by decide) dimensions
  have inputBound : initial.length < indexLimit := by
    rw [initialShape]
    exact Nat.pow_lt_pow_right (by decide) widthDimension
  have outputBound : outputs.length < indexLimit := by
    rw [outputShape]
    exact Nat.pow_lt_pow_right (by decide) widthDimension
  have addBound : add.length < indexLimit := by
    rw [addShape]
    exact Nat.pow_lt_pow_right (by decide) dimensions
  have mulBound : mul.length < indexLimit := by
    rw [mulShape]
    exact Nat.pow_lt_pow_right (by decide) dimensions
  have widthCheck : ¬ 4 < width := by omega
  have layersCheck : ¬ 4 < layers := by omega
  have capacityCheck : ¬ 2 ^ selector < layers := by omega
  unfold GkrSourceCallbacks.gkrBody process
  repeat' (rw [Region.denote]; simp [participantMeaningWithOn,
    protocolOperationWithOn, Operands.eval, Regions.denote, Values.get, Values.get_cons,
    Environment.prepend, Environment.push, GkrSourceAdmission.inputs, PIR.Process.bind, PIR.Process.bind_done, PIR.Process.bind_assoc,
    SiteObservations.silent, observed_helper, GkrSourceContinuation.empty_plain, GkrSourceAdmission.comparison_plain,
    GkrSourceAdmission.shape_plain_values, GkrSourceAdmission.index_add_plain,
    GkrSourceAdmission.power_plain, Primitive.evaluate, primitiveOutcome,
    show 4 < indexLimit by decide, show 1 < indexLimit by decide,
    widthSmall, layerSmall, selectorIndex, widthDimension, selectorSmall,
    capacityBound, tableBound, wiringBound, inputBound, outputBound, addBound, mulBound, initialShape, outputShape,
    addShape, mulShape, dimensions, totalSmall, widthCheck, layersCheck, capacityCheck,
    show selector + width < indexLimit by omega,
    show selector + width + width < indexLimit by omega,
    Participant.restrict, ProtocolContext.roles,
    Evaluation.componentOperationOn, strictComponent, Participant.owned, Participant.guard,
    RoleFamily.sequence, Values.absent, ProtocolOp.results, Values.split,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    SumcheckHelperLaws.prepend_two, SumcheckHelperLaws.prepend_three,
    boolResult, present_cons, Values.present, PIR.Process.interpret, Occurrence.actions, participantActions,
    Evaluation.meaningOn, Evaluation.operationOn, Op.calculationRegions,
    GkrSourceBodies.gkrSignature, Op.results])
  congr 1
  funext output
  cases output with | cons point rest =>
    cases rest with | cons producerPoint rest =>
      cases rest
      cases point <;>
        simp [Region.denote, participantMeaningWithOn, protocolOperationWithOn,
          Operands.eval, Regions.denote, Values.get, Values.get_cons, Values.split,
          Environment.prepend, Environment.push, SiteObservations.silent, observed_helper,
          Participant.owned, Participant.restrict, Participant.guard,
          RoleFamily.sequence, Values.absent, ProtocolOp.results,
          PIR.Process.bind, PIR.Process.bind_assoc, PIR.Process.bind_done,
          present_cons, Values.present, participantActions,
          SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
          SumcheckHelperLaws.prepend_two, SumcheckHelperLaws.prepend_three,
          Evaluation.componentOperationOn, strictComponent, ProtocolContext.contains,
          ProtocolContext.enter, roleSubstitution, GkrSourceBodies.sourceProtocol80Signature,
          SumcheckHelperLaws.singleton_eta]

end ZkcSecurity.Realizations.Gkr.OccurrenceVerifier
