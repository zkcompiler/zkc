import ZkcSecurity.Examples.RootProperties.SmallSumcheck.Soundness
import ZkcSecurity.Examples.RootProperties.TwoSums.Soundness
import ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessClaims
import ZkcSecurity.Examples.Generated.TwoSumsSoundnessClaims

/- Full imports keep theorem bodies available to the dependency audit. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace TestsSecurity.OriginalSecurityMeanings
open ZkcSecurity.Examples.Generated
open ZkcSecurity.Examples.RootProperties

/-- This is the existing evaluated request, with its original subject,
artifact, retained target, application binder, and scalar quantity. -/
theorem small_scalar (application : String) :
    (SmallSumcheckSoundnessClaims.request0Evaluated application).proposition := by
  dsimp only [SmallSumcheckSoundnessClaims.request0Evaluated]
  claim_apply_theorem SmallSumcheck.Soundness.scalar_meaning normalizing
    [SmallSumcheck.Soundness.scalarBound, SmallSumcheck.Soundness.validatorCost, SmallSumcheck.Soundness.price, SmallSumcheck.Soundness.budget]

/-- No receipt or registration is replaced: the original charged proposition
is proved directly by the new all-input artifact consumer. -/
theorem small_charged (application : String) :
    (SmallSumcheckSoundnessClaims.request1Evaluated application).proposition := by
  dsimp only [SmallSumcheckSoundnessClaims.request1Evaluated]
  claim_apply_theorem SmallSumcheck.Soundness.charged_meaning normalizing
    [SmallSumcheck.Soundness.scalarBound, SmallSumcheck.Soundness.validatorCost, SmallSumcheck.Soundness.price, SmallSumcheck.Soundness.budget, SmallSumcheck.Soundness.priceBound, SmallSumcheck.Soundness.schedule,
      ZkcSecurity.Claims.CompiledSoundness.uniformSchedule]

theorem two_scalar (application : String) :
    (TwoSumsSoundnessClaims.request0Evaluated application).proposition := by
  dsimp only [TwoSumsSoundnessClaims.request0Evaluated]
  claim_apply_theorem TwoSums.Soundness.scalar_meaning normalizing
    [TwoSums.Soundness.scalarBound, TwoSums.Soundness.validatorCost, TwoSums.Soundness.price, TwoSums.Soundness.budget]

theorem two_charged (application : String) :
    (TwoSumsSoundnessClaims.request1Evaluated application).proposition := by
  dsimp only [TwoSumsSoundnessClaims.request1Evaluated]
  claim_apply_theorem TwoSums.Soundness.charged_meaning normalizing
    [TwoSums.Soundness.scalarBound, TwoSums.Soundness.validatorCost, TwoSums.Soundness.price, TwoSums.Soundness.budget, TwoSums.Soundness.priceBound, TwoSums.Soundness.schedule,
      ZkcSecurity.Claims.CompiledSoundness.uniformSchedule]

#print axioms ZkcSecurity.FiatShamir.RootConnection.losslessBridge
#print axioms ZkcSecurity.Source.Installation.rejected
#print axioms SmallSumcheck.Soundness.reductionExport
#print axioms TwoSums.Soundness.reductionExport
#print axioms small_scalar
#print axioms small_charged
#print axioms two_scalar
#print axioms two_charged


end TestsSecurity.OriginalSecurityMeanings
