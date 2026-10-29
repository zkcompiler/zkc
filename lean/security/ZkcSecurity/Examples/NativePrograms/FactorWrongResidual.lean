module

public import Aesop
public import Lean
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FailIfNoProgress
public import Mathlib.Tactic.Ring
public import Zkc.Protocols.Sumcheck.FactorOpening.Execution
public import Zkc.Source.Structured.CommonAdapter
public import ZkcExamples.NativePrograms.Variants.FactorWrongResidualView
public import ZkcTools.ProcessView

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
noncomputable section
namespace ZkcExamples.NativePrograms.FactorWrongResidual
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Sumcheck.FactorOpening

abbrev program := ZkcExamples.NativePrograms.Variants.FactorWrongResidualInputs.program
abbrev imported := ZkcExamples.NativePrograms.Variants.FactorWrongResidualInputs.imported

def wiring : Wiring := ⟨⟨0, "bls12-381.fr", ("label_666972737430_0", "label_666972737431_0", "label_666972737432_0"), ("label_7365636f6e6430_0", "label_7365636f6e6431_0", "label_7365636f6e6432_0"), "label_6472617730", "label_6472617731", "label_64656c6976657230_0", "label_64656c6976657231_0"⟩, "label_6c656674_0", "label_7269676874_0"⟩
variable {F : Type} [Field F] [DecidableEq F]

def inputs (statement : Statement F) (claim : F) (service : Nat) : Values (Component (assignment F F)) program.payload.entry.inputs :=
  .cons (some statement.left.constant) (.cons (some statement.left.second) (.cons (some statement.left.first) (.cons (some statement.left.mixed) (.cons (some statement.right.constant) (.cons (some statement.right.second) (.cons (some statement.right.first) (.cons (some statement.right.mixed) (.cons (some claim) (.cons (some service) (.nil))))))))))

/-- The derived scalar observation of the actual typed Structured participant. -/
def verifier (statement : Statement F) (claim : F) (service : Nat) : PIR.Process (CommonAdapter.commonInterface F F) (Option Bool) :=
  ((program.participant F F 1 (inputs (F := F) statement claim service)).bind
    fun values => PIR.Process.done (values.get .here)).interpret CommonAdapter.project

noncomputable def processView (statement : Statement F) (claim : F) (service : Nat) : PIR.Process (CommonAdapter.commonInterface F F) (Option Bool) :=
  process_view% ((ZkcExamples.NativePrograms.Variants.FactorWrongResidualView.view (F := F) (G := F) (statement.left.constant) (statement.left.second) (statement.left.first) (statement.left.mixed) (statement.right.constant) (statement.right.second) (statement.right.first) (statement.right.mixed) (claim) (service)).bind
    fun values => PIR.Process.done (values.get .here)).interpret CommonAdapter.project

theorem process_view_eq (statement : Statement F) (claim : F) (service : Nat) :
    verifier (F := F) statement claim service = processView (F := F) statement claim service := by
  unfold verifier
  change ((program.participant F F 1
    (ZkcExamples.NativePrograms.Variants.FactorWrongResidualView.inputs (F := F) (G := F) (statement.left.constant) (statement.left.second) (statement.left.first) (statement.left.mixed) (statement.right.constant) (statement.right.second) (statement.right.first) (statement.right.mixed) (claim) (service))).bind _).interpret _ = _
  rw [ZkcExamples.NativePrograms.Variants.FactorWrongResidualView.source_equation]
  rfl

end ZkcExamples.NativePrograms.FactorWrongResidual
end
