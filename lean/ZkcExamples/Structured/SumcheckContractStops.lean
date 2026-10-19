module

public import ZkcExamples.Structured.SumcheckContractControls
public import ZkcExamples.Structured.SumcheckSourceVerifier
public import ZkcExamples.Structured.SumcheckReduceVerifier

@[expose] public section

/-! Count and stop controls over the actual maintained imported V participants.
These reuse the exact process equations, preserving refusal, incompleteness and
returned residuals as distinct observations. -/
namespace ZkcExamples.Structured.SumcheckContractStops
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Sumcheck.Multilinear
open SumcheckContractBindings SumcheckContractControls

/-- One above each unit's own retained maximum is refused, not only in the unrestricted family. -/
theorem public_excess_refuses :
    SumcheckSourceViews.imported.program.participant F F 1
      (SumcheckSourceVerifier.sourceRootInputs (some [0, 0]) (some 1) (some (SumcheckSourceNormalForms.reduceMaximum + 1)) none) =
      .halt .refused :=
  SumcheckSourceVerifier.verifier_excess _ _ _ _ (Nat.lt_succ_self _)

theorem reduction_excess_refuses :
    SumcheckReduceViews.imported.program.participant F F 1
      (SumcheckReduceVerifier.reduceRootInputs none none (some 1) (some (SumcheckReductionNormalForms.reduceMaximum + 1)) none) =
      .halt .refused :=
  SumcheckReduceVerifier.verifier_excess _ _ _ _ (Nat.lt_succ_self _) _

theorem missing_count_is_incomplete :
    SumcheckSourceViews.imported.program.participant F F 1
      (SumcheckSourceVerifier.sourceRootInputs (some [0]) (some 1) none none) =
      .halt .incomplete :=
  SumcheckSourceVerifier.verifier_missing _ _ _

/-- A zero-round reduction returns its initial claim without a terminal checker.
Successful return alone therefore cannot be an acceptance certificate. -/
theorem zero_reduction_returns_without_terminal :
    SumcheckReduceViews.imported.program.participant F F 1
      (SumcheckReduceVerifier.reduceRootInputs none none (some 1) (some 0) none) =
      .done (SumcheckReduceVerifier.reduceRootResults (some [], some 1)) :=
  SumcheckReduceVerifier.verifier_zero _ _ _ _

theorem zero_residual_is_false :
    ¬ Residual 0 0 (fun _ => (0 : F)) [] 1 := by
  rintro ⟨coordinates, _, truth⟩
  rw [residualClaim_complete_iff] at truth
  exact (by decide : (0 : F) ≠ 1) truth

end ZkcExamples.Structured.SumcheckContractStops
