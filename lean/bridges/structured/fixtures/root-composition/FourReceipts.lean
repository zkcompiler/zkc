import ZkcSecurity.Examples.Generated.FourSumsSoundnessClaims
import ZkcSecurity.Examples.Generated.FourSumsCompletenessClaims

/-! Exact source requests and independent proof-dependency checks. Loading this
as a non-module audit makes private theorem bodies available to the traversal. -/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace TestsSecurity.RootComposition.Four.Receipts
open ZkcSecurity.Examples.Generated
open Zkc.Source.Structured

local instance : ∀ event : Zkc.Construction.Domain.Event ZkcSecurity.Domains.PrimeField.blsScalarModel.toCarriers,
    SampleableType (Zkc.Construction.Domain.Raw event) := ZkcSecurity.Domains.PrimeField.rawSampleable blsModulus

theorem scalar (application : String) :
    (FourSumsSoundnessClaims.request0Evaluated application).proposition :=
  (FourSumsSoundnessClaims.request0Receipt application).receipt.proof

theorem charged (application : String) :
    (FourSumsSoundnessClaims.request1Evaluated application).proposition :=
  (FourSumsSoundnessClaims.request1Receipt application).receipt.proof

theorem complete : FourSumsCompletenessClaims.completeEvaluated.proposition :=
  FourSumsCompletenessClaims.completeReceipt.receipt.proof

#print axioms FourSumsSoundnessClaims.request0Receipt
#print axioms FourSumsSoundnessClaims.request1Receipt
#print axioms FourSumsCompletenessClaims.completeReceipt

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for (receipt, required) in [
      (``FourSumsSoundnessClaims.request0Receipt,
        [``ZkcExamples.Structured.Generated.Connections.FourSums.validator,
         ``TestsSecurity.RootComposition.Four.Source.rejected,
         ``TestsSecurity.RootComposition.Four.Source.costs,
         ``ZkcSecurity.Source.Installation.rejected,
         ``ZkcSecurity.FiatShamir.RootConnection.losslessChargedExport]),
      (``FourSumsSoundnessClaims.request1Receipt,
        [``ZkcExamples.Structured.Generated.Connections.FourSums.validator,
         ``TestsSecurity.RootComposition.Four.Source.rejected,
         ``TestsSecurity.RootComposition.Four.Source.costs,
         ``ZkcSecurity.Source.Installation.rejected]),
      (``FourSumsCompletenessClaims.completeReceipt,
        [``ZkcExamples.Structured.Generated.Connections.FourSums.producer,
         ``ZkcExamples.Structured.Generated.Connections.FourSums.validator,
         ``TestsSecurity.RootComposition.Four.Source.paired,
         ``ZkcSecurity.Source.Pair.bind,
         ``ZkcSecurity.Source.Installation.accepted])] do
    let mut seen : Lean.NameSet := {}
    let mut pending := [receipt]
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if seen.contains name then continue
      seen := seen.insert name
      if name == ``sorryAx then throwError "unfinished FourSums receipt: {receipt}"
      let spelling := name.toString
      for retired in ["CompiledRound", "CompiledValidator", "OriginalSumcheckRoots",
          "SourcePublicInstallations", "SourcePairInstallations"] do
        if spelling.contains retired then
          throwError "fresh receipt depends on a retained root implementation: {name}"
      if spelling.startsWith "Zkc" || spelling.startsWith "TestsSecurity." ||
          spelling.startsWith "_private.Zkc" || spelling.startsWith "_private.TestsSecurity." then
        if let some info := env.find? name then
          pending := info.type.getUsedConstants.toList ++ pending
          if let some value := info.value? (allowOpaque := true) then
            pending := value.getUsedConstants.toList ++ pending
    for name in required do
      unless seen.contains name do throwError "FourSums receipt missed required evidence: {name}"
    Lean.logInfo s!"PASS {receipt}: actual shared source composition and checked roots ({seen.size} declarations)"

end TestsSecurity.RootComposition.Four.Receipts
