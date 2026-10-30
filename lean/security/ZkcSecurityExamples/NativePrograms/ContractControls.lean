module

public import ZkcExamples.NativePrograms.SchnorrVariants
public import ZkcSecurityExamples.NativePrograms.SumcheckVariants
public import ZkcExamples.NativePrograms.SchnorrEarlyChallenge
public import ZkcExamples.NativePrograms.SumcheckWrongResidual

public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! Negative contract controls on actual native DSL exports.
Failure to implement this contract is distinct from proving a protocol insecure.
-/
set_option autoImplicit false
noncomputable section

namespace ZkcExamples.NativePrograms.ContractControls
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native

abbrev F := ZMod 97
instance : Fact (Nat.Prime 97) := ⟨by decide⟩

abbrev earlyVerifier := SchnorrEarlyChallenge.verifier (F := F) (G := F)
abbrev wrongResidual := SumcheckWrongResidual.verifier (F := F)

/-- Stop immediately, retaining whether the reached first action is a query. -/
def firstAction : PIR.Handler (Schnorr.actions (F := F) (G := F)) Unit Bool :=
  fun action state => ⟨.stopped .abort, state, [match action with | .query .. => true | _ => false]⟩

/-- Acceptance/outcome equality alone misses a challenge moved before commitment. -/
theorem early_same_outcome :
    ((earlyVerifier 1 1 7).run firstAction ()).outcome =
      ((Schnorr.experiment (F := F) 1 1 7).run firstAction ()).outcome := by
  unfold earlyVerifier
  rw [SchnorrEarlyChallenge.process_view_eq]
  rfl

theorem early_different_events :
    ((earlyVerifier 1 1 7).run firstAction ()).events ≠
      ((Schnorr.experiment (F := F) 1 1 7).run firstAction ()).events := by
  unfold earlyVerifier
  rw [SchnorrEarlyChallenge.process_view_eq]
  change [true] ≠ [false]
  decide

theorem early_no_contract :
    ¬ Zkc.Protocols.Schnorr.Common.VerifierContract Schnorr.wiring earlyVerifier := by
  intro certificate
  exact early_different_events (congrArg PIR.Execution.events
    ((certificate.realizes 1 1 7).run_eq firstAction ()))

/-- The polynomial X, with true Boolean sum 2. -/
def coefficients : Sumcheck.Coefficients F := ⟨⟨0,0,0⟩, ⟨1,0,0⟩, ⟨0,0,0⟩⟩
def prover : Sumcheck.Strategy F := ⟨⟨0,2,0⟩, fun x => ⟨x,0,0⟩⟩

theorem correct_residual_accepts :
    ((Sumcheck.experiment coefficients 2 7).run (Sumcheck.transcriptHandler prover 1 0) 0).outcome =
      .returned (some true) := by rfl

set_option maxRecDepth 20000 in
theorem wrong_residual_rejects :
    ((wrongResidual coefficients 2 7).run (Sumcheck.transcriptHandler prover 1 0) 0).outcome =
      .stopped .reject := by
  unfold wrongResidual
  rw [SumcheckWrongResidual.process_view_eq]
  rfl

set_option maxRecDepth 20000 in
/-- A changed residual cannot borrow the same Sumcheck security theorem. -/
theorem residual_no_contract :
    ¬ Zkc.Protocols.Sumcheck.Common.VerifierContract Sumcheck.wiring wrongResidual := by
  intro certificate
  have same := congrArg PIR.Execution.outcome
    ((certificate.realizes coefficients 2 7).run_eq (Sumcheck.transcriptHandler prover 1 0) 0)
  rw [correct_residual_accepts, wrong_residual_rejects] at same
  cases same

end ZkcExamples.NativePrograms.ContractControls

end
