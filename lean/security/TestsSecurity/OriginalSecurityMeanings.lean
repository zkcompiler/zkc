import ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness
import ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Soundness
import ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessClaims
import ZkcSecurity.Examples.Generated.TwoSumsSoundnessClaims

/- Full imports keep theorem bodies available to the dependency audit. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace TestsSecurity.OriginalSecurityMeanings
open ZkcSecurity.Examples.Generated
open ZkcSecurity.Examples.Generated.OriginalSecurity

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

#print axioms SmallSumcheck.Installation.bridgeInputs
#print axioms TwoSums.Installation.bridgeInputs
#print axioms SmallSumcheck.Soundness.reductionExport
#print axioms TwoSums.Soundness.reductionExport
#print axioms small_scalar
#print axioms small_charged
#print axioms two_scalar
#print axioms two_charged

/- Audit the proof dependencies, rather than module imports: the table proof
engine is owned by TableComponent.Execution. None of these four new
proofs imports or depends on the old compiled binding authority. -/
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let forbidden : List Lean.Name :=
    [`ZkcSecurity.Families.Sumcheck.CompiledRound.block,
      `ZkcSecurity.Families.Sumcheck.CompiledRound.reading,
      `ZkcSecurity.Families.Sumcheck.CompiledValidator.RoundConnection,
      `ZkcSecurity.Families.Sumcheck.CompiledValidator.round_reading,
      ``ZkcSecurity.Examples.Generated.Components.SmallSumcheckSoundness.reductionExport,
      ``ZkcSecurity.Examples.Generated.Components.TwoSumsSoundness.reductionExport]
  let mut seen : Lean.NameSet := {}
  let mut pending := [``SmallSumcheck.Soundness.scalar_meaning, ``SmallSumcheck.Soundness.charged_meaning,
    ``TwoSums.Soundness.scalar_meaning, ``TwoSums.Soundness.charged_meaning]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if forbidden.contains name then
      throwError "original consumer depends on the old compiled matcher/export: {name}"
    if name.toString.startsWith "ZkcSecurity." || name.toString.startsWith "TestsSecurity." ||
        name.toString.startsWith "_private.ZkcSecurity." ||
        name.toString.startsWith "_private.TestsSecurity." then
      if let some info := env.find? name then
        pending := info.type.getUsedConstants.toList ++ pending
        if let some value := info.value? (allowOpaque := true) then
          pending := value.getUsedConstants.toList ++ pending
  for required in [``ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.validator,
      ``ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSumsValidatorRoot.validator,
      ``ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources.source_root,
      ``ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Sources.source_root,
      ``ZkcSecurity.FiatShamir.Original.Claims.Installation.losslessChargedExport] do
    unless seen.contains required do
      throwError "original consumer audit did not reach its required certificate: {required}"

end TestsSecurity.OriginalSecurityMeanings
