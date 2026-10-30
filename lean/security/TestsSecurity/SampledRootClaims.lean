import ZkcSecurityExamples.Generated.SchnorrRandomizedCompletenessClaims
import ZkcSecurityExamples.Generated.SchnorrAndRandomizedCompletenessClaims
import ZkcSecurityExamples.Generated.SchnorrAndAliasedCompletenessClaims
import ZkcSecurityExamples.Generated.SampledAbortCompletenessClaims
import ZkcSecurityExamples.Generated.SequentialSigmaCompletenessClaims

/-! The actual admitted sampled roots use one canonical receipt path. Changing
only the aborting source's error to zero must resolve its meaning successfully
and then fail proof checking with the same theorem and author library. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
noncomputable section
namespace TestsSecurity.SampledRootClaims
open Zkc.Claims ZkcSecurity.Claims
open ZkcSecurity.Examples.Generated

example : SchnorrRandomizedCompletenessClaims.completeEvaluated.proposition :=
  SchnorrRandomizedCompletenessClaims.completeReceipt.receipt.proof
example : SchnorrAndRandomizedCompletenessClaims.completeEvaluated.proposition :=
  SchnorrAndRandomizedCompletenessClaims.completeReceipt.receipt.proof
example : SchnorrAndAliasedCompletenessClaims.completeEvaluated.proposition :=
  SchnorrAndAliasedCompletenessClaims.completeReceipt.receipt.proof
example : SequentialSigmaCompletenessClaims.completeEvaluated.proposition :=
  SequentialSigmaCompletenessClaims.completeReceipt.receipt.proof

example : SampledAbortCompletenessClaims.completeEvaluated.proposition :=
  SampledAbortCompletenessClaims.completeReceipt.receipt.proof

example : SampledAbortCompletenessClaims.completeData.quantity =
    .scalar (.binary .div (.natural 1)
      (.application "cardinality" none [(none, .reference "bls12-381.fr")])) := rfl

namespace ZeroError
def completeData : Wire.Request :=
  { SampledAbortCompletenessClaims.completeData with quantity := .scalar (.natural 0) }

claim_request completeData using SampledAbortCompletenessClaims.library method
  (some (⟨⟨"fs.honest_completeness", 0⟩, []⟩ : Wire.Application))

run_cmd do
  let environment ← Lean.getEnv
  unless environment.contains `TestsSecurity.SampledRootClaims.ZeroError.completeEvaluated do
    throwError "the zero-error request failed before semantic evaluation"
  if environment.contains `TestsSecurity.SampledRootClaims.ZeroError.completeReceipt then
    throwError "a nonzero-error theorem produced a zero-error receipt"
end ZeroError

#print axioms SchnorrRandomizedCompletenessClaims.completeReceipt
#print axioms SchnorrAndRandomizedCompletenessClaims.completeReceipt
#print axioms SchnorrAndAliasedCompletenessClaims.completeReceipt
#print axioms SampledAbortCompletenessClaims.completeReceipt
#print axioms SequentialSigmaCompletenessClaims.completeReceipt
end TestsSecurity.SampledRootClaims
