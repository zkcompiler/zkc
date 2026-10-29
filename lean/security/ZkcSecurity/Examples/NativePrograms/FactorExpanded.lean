module

public import Aesop
public import Lean
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FailIfNoProgress
public import Mathlib.Tactic.Ring
public import Zkc.Protocols.Sumcheck.FactorOpening.Execution
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.NativePrograms.Variants.FactorExpandedView
public import ZkcTools.ProcessView

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
noncomputable section
namespace ZkcExamples.NativePrograms.FactorExpanded
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Sumcheck.FactorOpening

abbrev program := ZkcExamples.NativePrograms.Variants.FactorExpandedInputs.program
abbrev imported := ZkcExamples.NativePrograms.Variants.FactorExpandedInputs.imported

def wiring : Wiring := ⟨⟨0, "bls12-381.fr", ("label_666972737430_0", "label_666972737431_0", "label_666972737432_0"), ("label_7365636f6e6430_0", "label_7365636f6e6431_0", "label_7365636f6e6432_0"), "label_6472617730", "label_6472617731", "label_64656c6976657230_0", "label_64656c6976657231_0"⟩, "label_6c656674_0", "label_7269676874_0"⟩
variable {F : Type} [Field F] [DecidableEq F]

def inputs (statement : Statement F) (claim : F) (service : Nat) : Values (Component (assignment F F)) program.payload.entry.inputs :=
  .cons (some statement.left.constant) (.cons (some statement.left.second) (.cons (some statement.left.first) (.cons (some statement.left.mixed) (.cons (some statement.right.constant) (.cons (some statement.right.second) (.cons (some statement.right.first) (.cons (some statement.right.mixed) (.cons (some claim) (.cons (some service) (.nil))))))))))

/-- The derived scalar observation of the actual typed Structured participant. -/
def verifier (statement : Statement F) (claim : F) (service : Nat) : PIR.Process (CommonAdapter.commonInterface F F) (Option Bool) :=
  ((program.participant F F 1 (inputs (F := F) statement claim service)).bind
    fun values => PIR.Process.done (values.get .here)).interpret CommonAdapter.project

noncomputable def processView (statement : Statement F) (claim : F) (service : Nat) : PIR.Process (CommonAdapter.commonInterface F F) (Option Bool) :=
  process_view% ((ZkcExamples.NativePrograms.Variants.FactorExpandedView.view (F := F) (G := F) (statement.left.constant) (statement.left.second) (statement.left.first) (statement.left.mixed) (statement.right.constant) (statement.right.second) (statement.right.first) (statement.right.mixed) (claim) (service)).bind
    fun values => PIR.Process.done (values.get .here)).interpret CommonAdapter.project

theorem process_view_eq (statement : Statement F) (claim : F) (service : Nat) :
    verifier (F := F) statement claim service = processView (F := F) statement claim service := by
  unfold verifier
  change ((program.participant F F 1
    (ZkcExamples.NativePrograms.Variants.FactorExpandedView.inputs (F := F) (G := F) (statement.left.constant) (statement.left.second) (statement.left.first) (statement.left.mixed) (statement.right.constant) (statement.right.second) (statement.right.first) (statement.right.mixed) (claim) (service))).bind _).interpret _ = _
  rw [ZkcExamples.NativePrograms.Variants.FactorExpandedView.source_equation]
  rfl

theorem correspondence (statement : Statement F) (claim : F) (service : Nat) :
    processView (F := F) statement claim service = experiment (F := F) wiring statement claim service := by
  aesop (rule_sets := [-builtin, -default]) (config := { enableSimp := false })
    (add norm tactic (by fail_if_no_progress dsimp +instances [processView, wiring, Zkc.Protocols.Sumcheck.FactorOpening.experiment, Zkc.Protocols.Sumcheck.FactorOpening.experimentWith, Zkc.Protocols.Sumcheck.FactorOpening.terminal, Zkc.Protocols.Sumcheck.FactorOpening.publicChecks, Zkc.Protocols.Sumcheck.FactorOpening.value, Zkc.Protocols.Sumcheck.Common.rounds, Zkc.Protocols.Sumcheck.Common.roundsWith, Zkc.Protocols.Sumcheck.Common.standardArithmetic, Zkc.Protocols.Sumcheck.Common.wireBoundary, Zkc.Protocols.Sumcheck.Common.wireEvaluate, PIR.Process.bind]))
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

theorem contract : VerifierContract wiring publicChecks (verifier (F := F)) :=
  ⟨fun statement claim service => ⟨(process_view_eq (F := F) statement claim service).trans
    (correspondence (F := F) statement claim service)⟩⟩

end ZkcExamples.NativePrograms.FactorExpanded
end
