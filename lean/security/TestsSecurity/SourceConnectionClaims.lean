import ZkcSecurityExamples.Generated.SmallSumcheckCompletenessClaims
import ZkcSecurityExamples.Generated.TwoSumsCompletenessClaims

/-! The actual canonical receipt retains a fixed source correspondence goal.
Removing its proof opens the same claim; neither property mathematics nor an
attribution string can replace the required implementation link. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section
namespace TestsSecurity.SourceConnectionClaims
open Zkc.Claims
open ZkcSecurity.Examples.Generated.SmallSumcheckCompletenessClaims

private def missingValidator :=
  { ZkcSecurity.Examples.Generated.SmallSumcheck.subject with validatorConnection := none }

-- Removing proof data does not change any request-side proposition.
example : missingValidator.stageLinks =
    ZkcSecurity.Examples.Generated.SmallSumcheck.subject.stageLinks := rfl

example : (missingValidator.stageLinkProofs ⟨5, by decide +kernel⟩).isNone = true := rfl

private def withoutValidatorLink :=
  { completeReceipt with receipt :=
      { completeReceipt.receipt with linkProofs := fun index =>
          if index.val = 5 then none else completeReceipt.receipt.linkProofs index } }

example : completeReceipt.receipt.status = .certified := by decide +kernel
example : withoutValidatorLink.receipt.status = .open := by decide +kernel

-- The scalar/charged soundness owner inherits the very same validator proof.
example : ZkcSecurity.Examples.Generated.SmallSumcheck.validatorCompiled.sourceConnection =
    ZkcSecurity.Examples.Generated.SmallSumcheck.subject.validatorConnection := rfl

private def withoutProducerLink :=
  { completeReceipt with receipt :=
      { completeReceipt.receipt with linkProofs := fun index =>
          if index.val = 4 then none else completeReceipt.receipt.linkProofs index } }

example : withoutProducerLink.receipt.status = .open := by decide +kernel

namespace Two
open ZkcSecurity.Examples.Generated.TwoSumsCompletenessClaims
private def missingValidator :=
  { ZkcSecurity.Examples.Generated.TwoSums.subject with validatorConnection := none }
example : missingValidator.stageLinks = ZkcSecurity.Examples.Generated.TwoSums.subject.stageLinks := rfl
example : (missingValidator.stageLinkProofs ⟨5, by decide +kernel⟩).isNone = true := rfl
private def withoutLink (position : Nat) :=
  { ZkcSecurity.Examples.Generated.TwoSumsCompletenessClaims.completeReceipt with receipt :=
      { ZkcSecurity.Examples.Generated.TwoSumsCompletenessClaims.completeReceipt.receipt with
        linkProofs := fun index => if index.val = position then none else
          ZkcSecurity.Examples.Generated.TwoSumsCompletenessClaims.completeReceipt.receipt.linkProofs index } }
example : ZkcSecurity.Examples.Generated.TwoSumsCompletenessClaims.completeReceipt.receipt.status = .certified := by decide +kernel
example : (withoutLink 4).receipt.status = .open := by decide +kernel
example : (withoutLink 5).receipt.status = .open := by decide +kernel
example : ZkcSecurity.Examples.Generated.TwoSums.validatorCompiled.sourceConnection =
    ZkcSecurity.Examples.Generated.TwoSums.subject.validatorConnection := rfl
end Two
end TestsSecurity.SourceConnectionClaims
