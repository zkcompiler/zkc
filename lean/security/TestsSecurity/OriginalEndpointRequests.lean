import ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessClaims
import ZkcSecurity.Examples.Generated.TwoSumsSoundnessClaims
import ZkcSecurity.Examples.Generated.SmallSumcheckCompletenessClaims
import ZkcSecurity.Examples.Generated.TwoSumsCompletenessClaims

/-! This non-module audit loads private theorem bodies transitively.
Exact retained requests, using the actual registered receipt proofs. The
charged proposition includes its full ordinary compiled reduction witness. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace TestsSecurity.OriginalEndpointRequests
open ZkcSecurity.Examples.Generated
open Zkc.Source.Structured Zkc.Construction

local instance : ∀ event : Zkc.Construction.Domain.Event ZkcSecurity.Domains.PrimeField.blsScalarModel.toCarriers,
    SampleableType (Zkc.Construction.Domain.Raw event) := ZkcSecurity.Domains.PrimeField.rawSampleable blsModulus

theorem small_scalar (application : String) :
    (SmallSumcheckSoundnessClaims.request0Evaluated application).proposition :=
  (SmallSumcheckSoundnessClaims.request0Receipt application).receipt.proof

theorem small_charged (application : String) :
    (SmallSumcheckSoundnessClaims.request1Evaluated application).proposition :=
  (SmallSumcheckSoundnessClaims.request1Receipt application).receipt.proof

theorem two_scalar (application : String) :
    (TwoSumsSoundnessClaims.request0Evaluated application).proposition :=
  (TwoSumsSoundnessClaims.request0Receipt application).receipt.proof

theorem two_charged (application : String) :
    (TwoSumsSoundnessClaims.request1Evaluated application).proposition :=
  (TwoSumsSoundnessClaims.request1Receipt application).receipt.proof

theorem small_complete : SmallSumcheckCompletenessClaims.completeEvaluated.proposition :=
  SmallSumcheckCompletenessClaims.completeReceipt.receipt.proof

theorem two_complete : TwoSumsCompletenessClaims.completeEvaluated.proposition :=
  TwoSumsCompletenessClaims.completeReceipt.receipt.proof

example (queries : Nat) :
    ZkcSecurity.Claims.Domain.ChargedExport SmallSumcheck.validatorSubject
      Components.SmallSumcheckSoundness.schedule queries
      (Components.SmallSumcheckSoundness.budget • Components.SmallSumcheckSoundness.price) :=
  Components.SmallSumcheckSoundness.reductionExport queries

example (queries : Nat) :
    ZkcSecurity.Claims.Domain.ChargedExport TwoSums.validatorSubject
      Components.TwoSumsSoundness.schedule queries
      (Components.TwoSumsSoundness.budget • Components.TwoSumsSoundness.price) :=
  Components.TwoSumsSoundness.reductionExport queries

#print axioms SmallSumcheckSoundnessClaims.request0Receipt
#print axioms SmallSumcheckSoundnessClaims.request1Receipt
#print axioms TwoSumsSoundnessClaims.request0Receipt
#print axioms TwoSumsSoundnessClaims.request1Receipt
#print axioms SmallSumcheckCompletenessClaims.completeReceipt
#print axioms TwoSumsCompletenessClaims.completeReceipt

/- Traverse proof terms and types, not imports. Pure table mathematics shares
some modules with the retired matcher; those imports grant no binding authority. -/
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let forbidden : List Lean.Name :=
    [`ZkcSecurity.Families.Sumcheck.CompiledRound.block,
      `ZkcSecurity.Families.Sumcheck.CompiledRound.reading,
      `ZkcSecurity.Families.Sumcheck.CompiledValidator.RoundConnection,
      `ZkcSecurity.Families.Sumcheck.CompiledValidator.round_reading]
  let mut seen : Lean.NameSet := {}
  let mut pending := [``SmallSumcheckSoundnessClaims.request0Receipt,
    ``SmallSumcheckSoundnessClaims.request1Receipt,
    ``TwoSumsSoundnessClaims.request0Receipt, ``TwoSumsSoundnessClaims.request1Receipt,
    ``SmallSumcheckCompletenessClaims.completeReceipt, ``TwoSumsCompletenessClaims.completeReceipt]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if forbidden.contains name || name == ``sorryAx then
      throwError "production receipt depends on forbidden binding or unfinished proof: {name}"
    let spelling := name.toString
    for retired in ["SmallSumcheckRounds", "TwoSumsRounds",
        "SmallSumcheckValidatorView", "TwoSumsValidatorView"] do
      if spelling.contains retired then
        throwError "production receipt depends on retired generated binding: {name}"
    for handwritten in ["ZkcSecurity.Examples.Components.OriginalRaw.",
        "ZkcSecurity.Examples.Components.OriginalSecurity.", "ZkcSecurity.Examples.Components.OriginalHonest.",
        "ZkcSecurity.Examples.Components.ArtifactBinding.Small.",
        "ZkcSecurity.Examples.Components.ArtifactBinding.Two.",
        "ZkcSecurity.Examples.Components.OriginalProducer.Small.",
        "ZkcSecurity.Examples.Components.OriginalProducer.Two.",
        "ZkcExamples.Structured.OriginalSumcheckInstances.Small.",
        "ZkcExamples.Structured.OriginalSumcheckInstances.Two.",
        "ZkcExamples.Structured.OriginalSumcheckRoots.Small.",
        "ZkcExamples.Structured.OriginalSumcheckRoots.Two."] do
      if spelling.contains handwritten then
        throwError "production receipt still depends on handwritten security structure: {name}"
    if spelling.startsWith "Zkc" || spelling.startsWith "TestsSecurity." ||
        spelling.startsWith "_private.Zkc" || spelling.startsWith "_private.TestsSecurity." then
      if let some info := env.find? name then
        pending := info.type.getUsedConstants.toList ++ pending
        if let some value := info.value? (allowOpaque := true) then
          pending := value.getUsedConstants.toList ++ pending
  for required in [``ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.validator,
      ``ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSumsValidatorRoot.validator,
      ``ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources.source_root,
      ``ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Sources.source_root,
      ``ZkcSecurity.FiatShamir.Original.Claims.Installation.losslessChargedExport,
      ``ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Completeness.compiled_ideal_complete,
      ``ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Completeness.compiled_ideal_complete,
      ``ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot.producer,
      ``ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSumsProducerRoot.producer] do
    unless seen.contains required do
      throwError "production receipt did not reach required original-source evidence: {required}"
  Lean.logInfo s!"PASS six production receipts: original-source evidence, full exports, no retired bindings ({seen.size} declarations visited)"

end TestsSecurity.OriginalEndpointRequests
