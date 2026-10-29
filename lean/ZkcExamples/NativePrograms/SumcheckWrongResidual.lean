module

public import Aesop
public import Lean
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FailIfNoProgress
public import Mathlib.Tactic.Ring
public import Zkc.Protocols.Sumcheck.Common
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.NativePrograms.Variants.SumcheckWrongResidualView
public import ZkcTools.ProcessView

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
noncomputable section
namespace ZkcExamples.NativePrograms.SumcheckWrongResidual
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Sumcheck.Common

abbrev program := ZkcExamples.NativePrograms.Variants.SumcheckWrongResidualInputs.program
abbrev imported := ZkcExamples.NativePrograms.Variants.SumcheckWrongResidualInputs.imported

def wiring : Wiring := ⟨0, "bls12-381.fr", ("label_666972737430_0", "label_666972737431_0", "label_666972737432_0"), ("label_7365636f6e6430_0", "label_7365636f6e6431_0", "label_7365636f6e6432_0"), "label_6472617730", "label_6472617731", "label_64656c6976657230_0", "label_64656c6976657231_0"⟩
variable {F : Type} [Field F] [DecidableEq F]

def inputs (coefficients : Coefficients F) (claim : F) (service : Nat) : Values (Component (assignment F F)) program.payload.entry.inputs :=
  .cons (some coefficients.constant.constant) (.cons (some coefficients.constant.linear) (.cons (some coefficients.constant.quadratic) (.cons (some coefficients.linear.constant) (.cons (some coefficients.linear.linear) (.cons (some coefficients.linear.quadratic) (.cons (some coefficients.quadratic.constant) (.cons (some coefficients.quadratic.linear) (.cons (some coefficients.quadratic.quadratic) (.cons (some claim) (.cons (some service) (.nil)))))))))))

/-- The derived scalar observation of the actual typed Structured participant. -/
def verifier (coefficients : Coefficients F) (claim : F) (service : Nat) : PIR.Process (CommonAdapter.commonInterface F F) (Option Bool) :=
  ((program.participant F F 1 (inputs (F := F) coefficients claim service)).bind
    fun values => PIR.Process.done (values.get .here)).interpret CommonAdapter.project

noncomputable def processView (coefficients : Coefficients F) (claim : F) (service : Nat) : PIR.Process (CommonAdapter.commonInterface F F) (Option Bool) :=
  process_view% ((ZkcExamples.NativePrograms.Variants.SumcheckWrongResidualView.view (F := F) (G := F) (coefficients.constant.constant) (coefficients.constant.linear) (coefficients.constant.quadratic) (coefficients.linear.constant) (coefficients.linear.linear) (coefficients.linear.quadratic) (coefficients.quadratic.constant) (coefficients.quadratic.linear) (coefficients.quadratic.quadratic) (claim) (service)).bind
    fun values => PIR.Process.done (values.get .here)).interpret CommonAdapter.project

theorem process_view_eq (coefficients : Coefficients F) (claim : F) (service : Nat) :
    verifier (F := F) coefficients claim service = processView (F := F) coefficients claim service := by
  unfold verifier
  change ((program.participant F F 1
    (ZkcExamples.NativePrograms.Variants.SumcheckWrongResidualView.inputs (F := F) (G := F) (coefficients.constant.constant) (coefficients.constant.linear) (coefficients.constant.quadratic) (coefficients.linear.constant) (coefficients.linear.linear) (coefficients.linear.quadratic) (coefficients.quadratic.constant) (coefficients.quadratic.linear) (coefficients.quadratic.quadratic) (claim) (service))).bind _).interpret _ = _
  rw [ZkcExamples.NativePrograms.Variants.SumcheckWrongResidualView.source_equation]
  rfl

end ZkcExamples.NativePrograms.SumcheckWrongResidual
end
