import TestsSecurity.CompletenessClaimConstruction
import ZkcSecurityExamples.Generated.SmallSumcheckSoundnessClaims
import ZkcSecurityExamples.Generated.TwoSumsSoundnessClaims

/-! Final clients share one admitted pair and its actual validator projection.
Adaptive scalar and charged receipts retain the designated application binder.
-/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace TestsSecurity.SumcheckCanonicalClaims
open Zkc.Claims ZkcSecurity.Claims ZkcSecurity.Examples.Generated

example : SmallSumcheckCompletenessClaims.subject.down.validatorSubject
    SmallSumcheck.validatorSites = SmallSumcheckSoundnessRegistration.subject := rfl
example : TwoSumsCompletenessClaims.subject.down.validatorSubject
    TwoSums.validatorSites = TwoSumsSoundnessRegistration.subject := rfl

example (application : String) :
    Receipt (SmallSumcheckSoundnessClaims.request0Evaluated application) :=
  (SmallSumcheckSoundnessClaims.request0Receipt application).receipt
example (application : String) :
    Receipt (SmallSumcheckSoundnessClaims.request1Evaluated application) :=
  (SmallSumcheckSoundnessClaims.request1Receipt application).receipt
example (application : String) :
    Receipt (TwoSumsSoundnessClaims.request0Evaluated application) :=
  (TwoSumsSoundnessClaims.request0Receipt application).receipt
example (application : String) :
    Receipt (TwoSumsSoundnessClaims.request1Evaluated application) :=
  (TwoSumsSoundnessClaims.request1Receipt application).receipt

example (application : String) :
    runMethod (SmallSumcheckSoundnessClaims.request1Methods application)
      ⟨⟨"fs.keyed_charged", 0⟩, []⟩ =
        .ok (.proved (SmallSumcheckSoundnessClaims.request1Receipt application).receipt) :=
  SmallSumcheckSoundnessClaims.request1MethodExecuted application
example (application : String) :
    runMethod (TwoSumsSoundnessClaims.request1Methods application)
      ⟨⟨"fs.keyed_charged", 0⟩, []⟩ =
        .ok (.proved (TwoSumsSoundnessClaims.request1Receipt application).receipt) :=
  TwoSumsSoundnessClaims.request1MethodExecuted application

namespace WrongBound
def soundData : Wire.Request := {
  SmallSumcheckSoundnessClaims.request0Data with quantity := .scalar (.natural 0) }
def library : ZkcSecurity.Tools.ClaimConstruction.Library := {
  SmallSumcheckSoundnessRegistration.library with
    normalization := SmallSumcheckSoundnessRegistration.library.normalization ++
      [``SmallSumcheckSoundnessClaims.request0Data] }
claim_request soundData using library method
  (some (⟨⟨"fs.keyed_soundness", 0⟩, []⟩ : Wire.Application))
run_cmd do
  let env ← Lean.getEnv
  unless env.contains `TestsSecurity.SumcheckCanonicalClaims.WrongBound.soundEvaluated do
    throwError "the bound mutation did not reach theorem checking"
  if env.contains `TestsSecurity.SumcheckCanonicalClaims.WrongBound.soundReceipt then
    throwError "a theorem for a larger error produced a zero-error receipt"
end WrongBound

namespace WrongPrice
def soundData : Wire.Request := {
  SmallSumcheckSoundnessClaims.request1Data with
    quantity := .charged [("reduce.challenge", .natural 0)] }
def library : ZkcSecurity.Tools.ClaimConstruction.Library := {
  SmallSumcheckSoundnessRegistration.library with
    normalization := SmallSumcheckSoundnessRegistration.library.normalization ++
      [``SmallSumcheckSoundnessClaims.request1Data] }
claim_request soundData using library method
  (some (⟨⟨"fs.keyed_charged", 0⟩, []⟩ : Wire.Application))
run_cmd do
  let env ← Lean.getEnv
  unless env.contains `TestsSecurity.SumcheckCanonicalClaims.WrongPrice.soundEvaluated do
    throwError "the price mutation did not reach theorem checking"
  if env.contains `TestsSecurity.SumcheckCanonicalClaims.WrongPrice.soundReceipt then
    throwError "a charged theorem was reused at an unproved site price"
end WrongPrice

#print axioms SmallSumcheckCompletenessClaims.completeReceipt
#print axioms TwoSumsCompletenessClaims.completeReceipt
#print axioms SmallSumcheckSoundnessClaims.request0Receipt
#print axioms SmallSumcheckSoundnessClaims.request1Receipt
#print axioms TwoSumsSoundnessClaims.request0Receipt
#print axioms TwoSumsSoundnessClaims.request1Receipt
end TestsSecurity.SumcheckCanonicalClaims
