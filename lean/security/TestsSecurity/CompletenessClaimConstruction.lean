import ZkcSecurityExamples.Generated.SmallSumcheckCompletenessClaims
import ZkcSecurityExamples.Generated.TwoSumsCompletenessClaims
import TestsSecurity.ClaimClosedData

/-! The real closed requests produce canonical receipts. Wrong theorem, target,
and unsupported-parameter controls must never leave a receipt declaration behind. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
noncomputable section
namespace TestsSecurity.CompletenessClaimConstruction
open Zkc.Claims ZkcSecurity.Claims
open ZkcSecurity.Examples.Generated

example : SmallSumcheckCompletenessClaims.completeEvaluated.proposition := SmallSumcheckCompletenessClaims.completeReceipt.receipt.proof
example : TwoSumsCompletenessClaims.completeEvaluated.proposition := TwoSumsCompletenessClaims.completeReceipt.receipt.proof
example : SmallSumcheckCompletenessClaims.completeData.quantity = .scalar (.natural 0) := rfl
example : TwoSumsCompletenessClaims.completeData.quantity = .scalar (.natural 0) := rfl
example : SmallSumcheckCompletenessClaims.completeData.parameters = none := rfl
example : TwoSumsCompletenessClaims.completeData.parameters = none := rfl

namespace WrongTheorem
theorem unrelated : True := trivial
def completeData := SmallSumcheckCompletenessClaims.completeData
def library : ZkcSecurity.Tools.ClaimConstruction.Library := {
  SmallSumcheckCompletenessClaims.library with theoremMethods := [(⟨"fs.honest_completeness", 0⟩, ``unrelated)] }
claim_request completeData using library method
  (some (⟨⟨"fs.honest_completeness", 0⟩, []⟩ : Wire.Application))
run_cmd do
  let env ← Lean.getEnv
  unless env.contains `TestsSecurity.CompletenessClaimConstruction.WrongTheorem.completeEvaluated do
    throwError "the unrelated theorem did not reach proof checking"
  if env.contains `TestsSecurity.CompletenessClaimConstruction.WrongTheorem.completeReceipt then
    throwError "an unrelated theorem produced a completeness receipt"
end WrongTheorem

namespace WrongTarget
def completeData : Wire.Request := { SmallSumcheckCompletenessClaims.completeData with target := TwoSumsCompletenessClaims.completeData.target }
claim_request completeData using SmallSumcheckCompletenessClaims.library method
  (some (⟨⟨"fs.honest_completeness", 0⟩, []⟩ : Wire.Application))
run_cmd do
  if (← Lean.getEnv).contains `TestsSecurity.CompletenessClaimConstruction.WrongTarget.completeReceipt then
    throwError "a crossed target produced a completeness receipt"
end WrongTarget

namespace UnsupportedParameters
def completeData : Wire.Request := { SmallSumcheckCompletenessClaims.completeData with
  parameters := some (.application "honest.input_policy" (some 0) []) }
claim_request completeData using SmallSumcheckCompletenessClaims.library method
  (some (⟨⟨"fs.honest_completeness", 0⟩, []⟩ : Wire.Application))
run_cmd do
  if (← Lean.getEnv).contains `TestsSecurity.CompletenessClaimConstruction.UnsupportedParameters.completeReceipt then
    throwError "an unsupported input-policy parameter produced a completeness receipt"
end UnsupportedParameters

#print axioms SmallSumcheckCompletenessClaims.completeReceipt
#print axioms TwoSumsCompletenessClaims.completeReceipt
end TestsSecurity.CompletenessClaimConstruction
