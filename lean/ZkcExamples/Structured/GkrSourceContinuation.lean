module

public import ZkcExamples.Structured.GkrSourceAdmission
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import ZkcExamples.Structured.Generated.Presentations.Gkr
public import ZkcExamples.Structured.GkrInputInvocation
public import Zkc.Protocols.Sumcheck.Source.HelperExpansions

@[expose] public section

/-! The actual GKR validator after its admission prefix. The source's output
and layer callbacks retain their scopes; the terminal application is the actual
single-role input protocol. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Structured.GkrSourceContinuation
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary SumcheckVerifierHelpers
open Generated.Presentations.Gkr.Root
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem present_cons {ty : Ty} {types : List Ty}
    (value : assignment F G ty) (rest : Values (assignment F G) types) :
    (Values.cons value rest).present = Values.cons (some value) rest.present := rfl

abbrev closed : HelperTable (assignment F G) (participantInterface F G) :=
  (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed

theorem empty_plain : invoke (closed (F := F) (G := G)) GkrSourceBodies.emptyHelper .nil =
    .done (.cons [] .nil) := by kernel_rfl

/-- Actual dataflow after successful admission, before any reference circuit
or claim truth is chosen. -/
noncomputable def process (initial outputs add mul : List F) (layers selector width handle : Nat) :
    PIR.Process (participantInterface F G)
      (Values (Component (assignment F G)) [.boolean]) :=
  (invoke closed GkrSourceBodies.emptyHelper .nil).bind fun empty =>
  (denoteRepeat outputSpec {} 1 (some width)
    (.cons (some (empty.get .here)) (.cons none .nil)) (.cons (some handle) .nil)
    (outputFn {} 1)).bind fun output =>
  match output.get .here with
  | none => .halt .incomplete
  | some point =>
    (invoke closed GkrSourceBodies.evaluateHelper (.cons outputs (.cons point .nil))).bind fun claim =>
    (invoke closed GkrSourceBodies.sourceHelper19Helper
      (.cons point (.cons (claim.get .here) .nil))).bind fun packed =>
    (denoteRepeat layerSpec {} 1 (some layers)
      (.cons (output.get (.there .here)) (.cons (some (packed.get .here))
        (.cons (some (packed.get (.there .here))) .nil)))
      (.cons (some initial) (.cons (some add) (.cons (some mul) (.cons (some layers)
        (.cons (some selector) (.cons (some width) (.cons (some handle) .nil)))))))
      (layerFn {} 1)).bind fun final =>
    invokeProtocol (GkrSourceViews.unit.plainProtocolTable F G)
      GkrSourceBodies.sourceProtocol80Signature
      (({} : ProtocolContext).enter "label_696e707574" [1]) 1
      (.cons (some initial) (.cons (final.get (.there .here))
        (.cons (final.get (.there (.there .here))) .nil)))

/-- Successful source admission reduces to precisely this continuation. The
premises describe shape and bounds only; replies and output truth are free. -/
theorem participant (initial outputs add mul : List F) (layers selector width handle : Nat)
    (widthBound : width ≤ 4) (layersBound : layers ≤ 4)
    (initialShape : initial.length = 2 ^ width) (outputShape : outputs.length = 2 ^ width)
    (addShape : add.length = 2 ^ (selector + width + width + width))
    (mulShape : mul.length = 2 ^ (selector + width + width + width))
    (dimensions : selector + width + width + width < 64)
    (capacity : layers ≤ 2 ^ selector) :
    GkrSourceAdmission.participant (G := G) initial outputs add mul layers selector width handle =
      process initial outputs add mul layers selector width handle := by
  rw [GkrSourceAdmission.presentation]
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
  have input_call (values point : Option (List F)) (claim : Option F) :
      invokeProtocol (GkrSourceViews.unit.plainProtocolTable F G)
        GkrSourceBodies.sourceProtocol80Signature (({} : ProtocolContext).enter "label_696e707574" [1]) 1
        (.cons values (.cons point (.cons claim .nil))) =
      Generated.Presentations.Gkr.Input.verifierProcess values point claim :=
    GkrInputInvocation.invoke _ values point claim
  unfold Generated.Presentations.Gkr.Root.verifierProcess process
  simp [Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
    Generated.Presentations.Gkr.program, GkrSourceViews.program,
    PIR.Process.bind_assoc, PIR.Process.bind_done, PIR.Process.bind,
    Values.get, empty_plain, GkrSourceAdmission.comparison_plain,
    GkrSourceAdmission.shape_plain_values, GkrSourceAdmission.index_add_plain,
    GkrSourceAdmission.power_plain,
    show 4 < indexLimit by decide, show 1 < indexLimit by decide,
    widthSmall, layerSmall, selectorIndex, widthDimension, selectorSmall,
    capacityBound, tableBound, wiringBound, inputBound, outputBound, addBound, mulBound,
    initialShape, outputShape, addShape, mulShape, dimensions, totalSmall,
    widthCheck, layersCheck, capacityCheck,
    show selector + width < indexLimit by omega,
    show selector + width + width < indexLimit by omega,
    boolResult, input_call,
    Generated.Presentations.Gkr.Input.verifierView,
    Bindings.optionalPattern, NormalForm.InputPattern.environment,
    SumcheckHelperLaws.singleton_eta]
  rfl

end ZkcExamples.Structured.GkrSourceContinuation
