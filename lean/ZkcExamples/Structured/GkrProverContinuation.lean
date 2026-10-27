module

public import ZkcExamples.Structured.GkrSourceContinuation

@[expose] public section

/-! The complete current producer root as its actual source callbacks. This
structural equation supplies no honest success or circuit-computation premise. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Structured.GkrProverContinuation
open Zkc.Source Zkc.Source.Structured SumcheckVerifierHelpers GkrSourceCallbacks
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (initial add mul : List F) (layers selector width : Nat) :
    Values (Component (assignment F G)) GkrSourceBodies.gkrSignature.inputs :=
  .cons (some initial) (.cons none (.cons (some add) (.cons (some mul)
    (.cons (some layers) (.cons (some selector) (.cons (some width) (.cons none .nil)))))))

def process (initial add mul : List F) (layers selector width : Nat) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [.boolean]) :=
  (invoke GkrSourceContinuation.closed GkrSourceBodies.emptyHelper .nil).bind fun empty =>
  (denoteRepeat outputSpec {} 0 (some width)
    (.cons none (.cons (some (empty.get .here)) .nil)) (.cons none .nil)
    (outputFn {} 0)).bind fun output =>
  (denoteRepeat layerSpec {} 0 (some layers)
    (.cons (output.get (.there .here)) (.cons none (.cons none .nil)))
    (.cons (some initial) (.cons (some add) (.cons (some mul) (.cons (some layers)
      (.cons (some selector) (.cons (some width) (.cons none .nil)))))))
    (layerFn {} 0)).bind fun _ =>
  .done (.cons none .nil)

theorem participant (initial add mul : List F) (layers selector width : Nat) :
    GkrSourceViews.program.participant F G 0
      (inputs (G := G) initial add mul layers selector width) =
      process initial add mul layers selector width := by
  change (invokeProtocol (GkrSourceViews.unit.protocolTable F G)
    GkrSourceBodies.gkrSignature {} 0
    (inputs (G := G) initial add mul layers selector width)).interpret forgetSites = _
  rw [GkrSourceViews.unit.protocolTable_forgetSites (F := F) (G := G)]
  have view := protocol_invoke_body_view (.silent _) (participantActions F G)
    (plainHelpers (F := F) (G := G) GkrSourceViews.unit)
    GkrSourceViews.unit.protocols GkrSourceViews.unit.protocolsLinked
    GkrSourceViews.gkrDefinition GkrSourceViews.gkr_member gkrBody gkrBody_raw
    ({} : ProtocolContext) 0 (inputs (G := G) initial add mul layers selector width)
  have masked : maskValues 0 [[0, 1], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [1]]
      (inputs (G := G) initial add mul layers selector width) =
      inputs (G := G) initial add mul layers selector width := by
    simp [inputs, maskValues, Participant.restrict]
  change _ = (gkrBody.denote
    (participantMeaningWith (.silent _) (participantActions F G)
      (plainHelpers (F := F) (G := G) GkrSourceViews.unit) 0
      (GkrSourceViews.unit.plainProtocolTable F G) {})
    (maskValues 0 [[0, 1], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [1]]
      (inputs (G := G) initial add mul layers selector width)).get).bind
        (fun results => .done (maskValues 0 [[1]] results)) at view
  erw [view]
  rw [masked]
  unfold gkrBody process
  repeat' (rw [Region.denote]; simp [participantMeaningWith, protocolOperationWith,
    Operands.eval, Regions.denote, Values.get, Values.get_cons, Values.split,
    TypedABI.get_cons_here, TypedABI.get_cons_there,
    Environment.prepend, Environment.push, SiteObservations.silent,
    Participant.owned, Participant.restrict, Participant.guard,
    RoleFamily.sequence, Values.absent, ProtocolOp.results,
    PIR.Process.bind, PIR.Process.bind_assoc, PIR.Process.bind_done, PIR.Process.interpret,
    Values.present, participantActions, inputs, ProtocolContext.roles,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    SumcheckHelperLaws.prepend_two, SumcheckHelperLaws.prepend_three,
    Evaluation.componentOperation, strictComponent, Evaluation.meaning,
    Evaluation.operation, Op.calculationRegions, Primitive.evaluate, primitiveOutcome,
    show 4 < indexLimit by decide, show 1 < indexLimit by decide,
    Op.results, GkrSourceContinuation.empty_plain, GkrSourceContinuation.closed])
  congr 1
  funext output
  simp [Region.denote, participantMeaningWith, protocolOperationWith,
    Operands.eval, Regions.denote, Values.get, Values.get_cons, Values.split,
    TypedABI.get_cons_here, TypedABI.get_cons_there,
    Environment.prepend, Environment.push, SiteObservations.silent,
    Participant.owned, Participant.restrict, Participant.guard,
    RoleFamily.sequence, Values.absent, ProtocolOp.results,
    PIR.Process.bind, PIR.Process.bind_assoc, PIR.Process.bind_done, PIR.Process.interpret,
    Values.present, participantActions, inputs, ProtocolContext.roles,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    SumcheckHelperLaws.prepend_two, SumcheckHelperLaws.prepend_three,
    Evaluation.componentOperation, strictComponent, Evaluation.meaning,
    Evaluation.operation, Op.calculationRegions, ProtocolContext.contains,
    ProtocolContext.enter, roleSubstitution, GkrSourceBodies.sourceProtocol80Signature,
    SumcheckHelperLaws.singleton_eta, GkrSourceContinuation.closed, maskValues]
  all_goals rfl

end ZkcExamples.Structured.GkrProverContinuation
