module

public import ZkcExamples.NativePrograms.SumcheckData

public import Zkc.Protocols.Sumcheck.Common.Program
public import Mathlib.Tactic.FailIfNoProgress

@[expose] public section

/-! Actual exported two-round quadratic Sumcheck and its interactive game.

The public statement has nine coefficients. Received coefficients may be
arbitrary; the second message depends on the first challenge. The native byte
export and constructor rendering are tested edges. All theorems below concern
the admitted constructor data with an explicit field interpretation.
-/

set_option autoImplicit false

namespace ZkcExamples.NativePrograms.Sumcheck

open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open Zkc.Protocols.AlgebraicRounds (Message)
open Zkc.Polynomial Zkc.Probability

def imported : Imported := SumcheckData.snapshot.check.toOption.get (by decide +kernel)

export Zkc.Protocols.Sumcheck.Common
  (Coefficients rowPolynomial polynomial wireEvaluate wireBoundary wireEvaluate_eq wireBoundary_eq
    evaluate evaluate_eq actions)

variable {F : Type} [Field F] [DecidableEq F]

def verifierInputs (coefficients : Coefficients F) (claim : F) (service : Nat) :
    Values (fun ty => Option (ScalarValue F F ty)) SumcheckData.snapshot.inputs :=
  .cons (some coefficients.constant.constant)
  (.cons (some coefficients.constant.linear) (.cons (some coefficients.constant.quadratic)
  (.cons (some coefficients.linear.constant) (.cons (some coefficients.linear.linear)
  (.cons (some coefficients.linear.quadratic) (.cons (some coefficients.quadratic.constant)
  (.cons (some coefficients.quadratic.linear) (.cons (some coefficients.quadratic.quadratic)
  (.cons (some claim) (.cons (some service) .nil))))))))))

def wiring : Zkc.Protocols.Sumcheck.Common.Wiring :=
  ⟨0, "bls12-381.fr",
    ("label_666972737430_0", "label_666972737431_0", "label_666972737432_0"),
    ("label_7365636f6e6430_0", "label_7365636f6e6431_0", "label_7365636f6e6432_0"),
    "label_6472617730", "label_6472617731", "label_64656c6976657230_0", "label_64656c6976657231_0"⟩

abbrev experiment := Zkc.Protocols.Sumcheck.Common.experiment (F := F) wiring

set_option maxRecDepth 20000 in
def verifier (coefficients : Coefficients F) (claim : F) (service : Nat) :
    PIR.Process (actions (F := F)) (Option Bool) :=
  imported.denote (scalarMeaning F F) id 1 (verifierInputs coefficients claim service)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem verifier_correspondence (coefficients : Coefficients F) (claim : F) (service : Nat) :
    verifier coefficients claim service =
      experiment coefficients claim service := by
  change (imported.program.denote (scalarMeaning F F) id 1
    (verifierInputs coefficients claim service).get).bind PIR.Process.done = _
  rw [PIR.Process.bind_done]
  repeat' first
    | (apply PIR.Process.call_congr; intro reply)
    | (change (if _ then _ else _ : PIR.Process _ _).bind _ = _
       rw [PIR.Process.bind_ite]
       simp only [↓reduceIte])
    | rfl
    | fail_if_no_progress congr 1

set_option maxRecDepth 20000 in
/-- This certificate is independent of the later choice of property and game. -/
theorem contract : Zkc.Protocols.Sumcheck.Common.VerifierContract wiring (verifier (F := F)) :=
  ⟨fun coefficients claim service => ⟨verifier_correspondence coefficients claim service⟩⟩

end ZkcExamples.NativePrograms.Sumcheck
