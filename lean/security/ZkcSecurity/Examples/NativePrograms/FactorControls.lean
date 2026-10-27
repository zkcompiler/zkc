module

public import ZkcSecurity.Examples.NativePrograms.FactorExpanded
public import ZkcSecurity.Examples.NativePrograms.FactorWrongPoint
public import ZkcSecurity.Examples.NativePrograms.FactorWrongResidual

public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! Actual native exports that cannot implement the selected composed contract.
These are contract counterexamples, not a blanket insecurity claim. -/
set_option autoImplicit false
namespace ZkcExamples.NativePrograms.FactorControls
open Zkc.Protocols.Sumcheck.FactorOpening

abbrev F := ZMod 97
instance : Fact (Nat.Prime 97) := ⟨by decide⟩

/-- Product X · 1, with Boolean sum 2. Swapping coordinates changes its opening. -/
def xStatement : Statement F := ⟨⟨0,0,1,0⟩, ⟨1,0,0,0⟩⟩
def xStrategy : Strategy F := ⟨⟨⟨0,2,0⟩, fun x => ⟨x,0,0⟩⟩, fun x _ => x, fun _ _ _ => 1⟩

/-- Product Y · 1, whose second-round residual depends on the second challenge. -/
def yStatement : Statement F := ⟨⟨0,1,0,0⟩, ⟨1,0,0,0⟩⟩
def yStrategy : Strategy F := ⟨⟨⟨1,0,0⟩, fun _ => ⟨0,1,0⟩⟩, fun _ y => y, fun _ _ _ => 1⟩

theorem correct_point_accepts :
    (run (experiment FactorExpanded.wiring) xStatement 2 7 xStrategy 1 0).outcome =
      .returned (some true) := rfl

theorem swapped_point_rejects :
    (run FactorWrongPoint.verifier xStatement 2 7 xStrategy 1 0).outcome = .stopped .reject := by
  unfold run
  rw [FactorWrongPoint.process_view_eq]
  rfl

theorem wrong_point_no_contract :
    ¬ VerifierContract FactorExpanded.wiring publicChecks (FactorWrongPoint.verifier (F := F)) := by
  intro certificate
  have same := congrArg PIR.Execution.outcome
    ((certificate.realizes xStatement 2 7).run_eq (transcriptHandler xStrategy 1 0) 0)
  change (run FactorWrongPoint.verifier xStatement 2 7 xStrategy 1 0).outcome =
    (run (experiment FactorExpanded.wiring) xStatement 2 7 xStrategy 1 0).outcome at same
  rw [correct_point_accepts, swapped_point_rejects] at same
  cases same

theorem correct_residual_accepts :
    (run (experiment FactorExpanded.wiring) yStatement 2 7 yStrategy 3 5).outcome =
      .returned (some true) := rfl

theorem forged_residual_false :
    (run FactorWrongResidual.verifier yStatement 2 7 yStrategy 3 5).outcome = .returned (some false) := by
  unfold run
  rw [FactorWrongResidual.process_view_eq]
  rfl

theorem wrong_residual_no_contract :
    ¬ VerifierContract FactorExpanded.wiring publicChecks (FactorWrongResidual.verifier (F := F)) := by
  intro certificate
  have same := congrArg PIR.Execution.outcome
    ((certificate.realizes yStatement 2 7).run_eq (transcriptHandler yStrategy 3 5) 0)
  change (run FactorWrongResidual.verifier yStatement 2 7 yStrategy 3 5).outcome =
    (run (experiment FactorExpanded.wiring) yStatement 2 7 yStrategy 3 5).outcome at same
  rw [correct_residual_accepts, forged_residual_false] at same
  cases same

end ZkcExamples.NativePrograms.FactorControls
