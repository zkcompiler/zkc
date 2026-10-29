module

public import ZkcExamples.Structured.GkrSourceContinuation
public import ZkcExamples.Structured.SumcheckVerifierHelpers

@[expose] public section

/-! The complete current producer root as its actual source callbacks. This
structural equation supplies no honest success or circuit-computation premise. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Structured.GkrProverContinuation
open Zkc.Source Zkc.Source.Structured SumcheckVerifierHelpers Generated.Presentations.Gkr.Root
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (initial add mul : List F) (layers selector width : Nat) :
    Values (Component (assignment F G)) GkrSourceBodies.gkrSignature.inputs :=
  .cons (some initial) (.cons none (.cons (some add) (.cons (some mul)
    (.cons (some layers) (.cons (some selector) (.cons (some width) (.cons none .nil)))))))

noncomputable def process (initial add mul : List F) (layers selector width : Nat) :
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
  rw [prover_participant]
  simp only [proverView, proverProcess, inputs, Values.get_cons,
    Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
    Generated.Presentations.Gkr.program, GkrSourceViews.program,
    PIR.Process.bind_assoc, PIR.Process.bind]
  rfl

end ZkcExamples.Structured.GkrProverContinuation
