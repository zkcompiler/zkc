module

public import Aesop
public import Lean
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FailIfNoProgress
public import Mathlib.Tactic.Ring
public import Zkc.Protocols.Sumcheck.Common
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.NativePrograms.Variants.SumcheckHelpersView
public import ZkcTools.ProcessView

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
noncomputable section
namespace ZkcExamples.NativePrograms.SumcheckHelpers
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Sumcheck.Common

abbrev program := ZkcExamples.NativePrograms.Variants.SumcheckHelpersInputs.program
abbrev imported := ZkcExamples.NativePrograms.Variants.SumcheckHelpersInputs.imported

def wiring : Wiring := ⟨0, "bls12-381.fr", ("label_666972737430_0", "label_666972737431_0", "label_666972737432_0"), ("label_7365636f6e6430_0", "label_7365636f6e6431_0", "label_7365636f6e6432_0"), "label_6472617730", "label_6472617731", "label_64656c6976657230_0", "label_64656c6976657231_0"⟩
variable {F : Type} [Field F] [DecidableEq F]

def inputs (coefficients : Coefficients F) (claim : F) (service : Nat) : Values (Component (assignment F F)) program.payload.entry.inputs :=
  .cons (some coefficients.constant.constant) (.cons (some coefficients.constant.linear) (.cons (some coefficients.constant.quadratic) (.cons (some coefficients.linear.constant) (.cons (some coefficients.linear.linear) (.cons (some coefficients.linear.quadratic) (.cons (some coefficients.quadratic.constant) (.cons (some coefficients.quadratic.linear) (.cons (some coefficients.quadratic.quadratic) (.cons (some claim) (.cons (some service) (.nil)))))))))))

/-- The derived scalar observation of the actual typed Structured participant. -/
def verifier (coefficients : Coefficients F) (claim : F) (service : Nat) : PIR.Process (CommonAdapter.commonInterface F F) (Option Bool) :=
  ((program.participant F F 1 (inputs (F := F) coefficients claim service)).bind
    fun values => PIR.Process.done (values.get .here)).interpret CommonAdapter.project

noncomputable def processView (coefficients : Coefficients F) (claim : F) (service : Nat) : PIR.Process (CommonAdapter.commonInterface F F) (Option Bool) :=
  process_view% ((ZkcExamples.NativePrograms.Variants.SumcheckHelpersView.view (F := F) (G := F) (coefficients.constant.constant) (coefficients.constant.linear) (coefficients.constant.quadratic) (coefficients.linear.constant) (coefficients.linear.linear) (coefficients.linear.quadratic) (coefficients.quadratic.constant) (coefficients.quadratic.linear) (coefficients.quadratic.quadratic) (claim) (service)).bind
    fun values => PIR.Process.done (values.get .here)).interpret CommonAdapter.project

theorem process_view_eq (coefficients : Coefficients F) (claim : F) (service : Nat) :
    verifier (F := F) coefficients claim service = processView (F := F) coefficients claim service := by
  unfold verifier
  change ((program.participant F F 1
    (ZkcExamples.NativePrograms.Variants.SumcheckHelpersView.inputs (F := F) (G := F) (coefficients.constant.constant) (coefficients.constant.linear) (coefficients.constant.quadratic) (coefficients.linear.constant) (coefficients.linear.linear) (coefficients.linear.quadratic) (coefficients.quadratic.constant) (coefficients.quadratic.linear) (coefficients.quadratic.quadratic) (claim) (service))).bind _).interpret _ = _
  rw [ZkcExamples.NativePrograms.Variants.SumcheckHelpersView.source_equation]
  rfl

theorem correspondence (coefficients : Coefficients F) (claim : F) (service : Nat) :
    processView (F := F) coefficients claim service = experiment (F := F) wiring coefficients claim service := by
  aesop (rule_sets := [-builtin, -default]) (config := { enableSimp := false })
    (add norm tactic (by fail_if_no_progress dsimp +instances [processView, wiring, Zkc.Protocols.Sumcheck.Common.experiment, Zkc.Protocols.Sumcheck.Common.experimentWith, Zkc.Protocols.Sumcheck.Common.standardArithmetic, Zkc.Protocols.Sumcheck.Common.wireBoundary, Zkc.Protocols.Sumcheck.Common.wireEvaluate, Zkc.Protocols.Sumcheck.Common.evaluate, PIR.Process.bind]))
    (add norm tactic (by rw [PIR.Process.bind_ite]))
    (add norm tactic (by fail_if_no_progress simp only [apply_ite]))
    (add norm tactic (by fail_if_no_progress ring_nf))
    (add norm tactic (by fail_if_no_progress simp_all only [ite_true, ite_false, decide_true, decide_false, Bool.false_eq_true, not_false_eq_true, not_true_eq_false]))
    (add safe tactic (by split_ifs))
    (add safe tactic (by apply PIR.Process.call_congr; intro reply))
    (add safe tactic (by rfl))
    (add safe tactic (by apply funext; intro reply))
    (add safe tactic (by ring1))

    (add 50% tactic (by fail_if_no_progress congr 1))

theorem contract : VerifierContract wiring (verifier (F := F)) :=
  ⟨fun coefficients claim service => ⟨(process_view_eq (F := F) coefficients claim service).trans
    (correspondence (F := F) coefficients claim service)⟩⟩

end ZkcExamples.NativePrograms.SumcheckHelpers
end
