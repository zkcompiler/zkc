import ZkcSecurity.Realizations.Gkr.Generated.SubjectCompletenessClaims
import ZkcSecurity.Realizations.Gkr.Generated.SubjectSoundnessClaims

/-! The same actual source pair and fixed registered circuit-output target
supply universal soundness and actual-producer completeness receipts. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace TestsSecurity.GkrCanonicalClaims
open Zkc.Claims ZkcSecurity.Claims ZkcSecurity.Realizations.Gkr.Generated

example : SubjectCompletenessClaims.subject.down.validatorSubject Subject.validatorSites =
    SubjectSoundnessRegistration.subject := rfl

example : Receipt SubjectCompletenessClaims.completeEvaluated :=
  SubjectCompletenessClaims.completeReceipt.receipt

example (application : String) : Receipt (SubjectSoundnessClaims.request0Evaluated application) :=
  (SubjectSoundnessClaims.request0Receipt application).receipt

example (application : String) : Receipt (SubjectSoundnessClaims.request1Evaluated application) :=
  (SubjectSoundnessClaims.request1Receipt application).receipt

example (application : String) :
    runMethod (SubjectSoundnessClaims.request1Methods application) ⟨⟨"fs.keyed_charged", 0⟩, []⟩ =
      .ok (.proved (SubjectSoundnessClaims.request1Receipt application).receipt) :=
  SubjectSoundnessClaims.request1MethodExecuted application

namespace WrongBound
def soundData : Wire.Request := {
  SubjectSoundnessClaims.request0Data with quantity := .scalar (.natural 0) }
def library : ZkcSecurity.Tools.ClaimConstruction.Library := {
  SubjectSoundnessRegistration.library with
    normalization := SubjectSoundnessRegistration.library.normalization ++
      [``SubjectSoundnessClaims.request0Data] }
claim_request soundData using library method
  (some (⟨⟨"fs.keyed_soundness", 0⟩, []⟩ : Wire.Application))
run_cmd do
  let env ← Lean.getEnv
  unless env.contains `TestsSecurity.GkrCanonicalClaims.WrongBound.soundEvaluated do
    throwError "the bound mutation did not reach theorem checking"
  if env.contains `TestsSecurity.GkrCanonicalClaims.WrongBound.soundReceipt then
    throwError "a larger-error theorem produced a zero-error receipt"
end WrongBound

namespace WrongTarget
def completeData : Wire.Request := {
  SubjectCompletenessClaims.completeData with
    target := .retained "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2" 0 "circuit_outputs" }
claim_request completeData using SubjectCompletenessClaims.library method
  (some (⟨⟨"fs.honest_completeness", 0⟩, []⟩ : Wire.Application))
run_cmd do
  if (← Lean.getEnv).contains `TestsSecurity.GkrCanonicalClaims.WrongTarget.completeReceipt then
    throwError "a different retained clause produced a completeness receipt"
end WrongTarget

#print axioms SubjectCompletenessClaims.completeReceipt
#print axioms SubjectSoundnessClaims.request0Receipt
#print axioms SubjectSoundnessClaims.request1Receipt
end TestsSecurity.GkrCanonicalClaims
