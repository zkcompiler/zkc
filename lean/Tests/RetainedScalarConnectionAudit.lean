import ZkcExamples.Construction.SchnorrProof
import ZkcExamples.Construction.SchnorrAndProof
import ZkcExamples.Construction.ChaumPedersenProof
import ZkcExamples.Construction.OkamotoProof
import ZkcExamples.Construction.GuessProof
import ZkcExamples.Construction.SumcheckProof
import ZkcExamples.Construction.ComposedSumcheckProof
import ZkcExamples.Executable.SumcheckCompleteness
import ZkcExamples.Executable.SchnorrProof
import ZkcTools.DeclarationAudit

/-! Proof-body dependency controls for retained scalar transport. Header imports
alone cannot satisfy the positive checks or trip the retired-authority check. -/
set_option autoImplicit false

run_cmd ZkcTools.DeclarationAudit.check [
  `Zkc.Construction.ScalarConnection,
  `Zkc.Construction.Uniform.ScalarSupport,
  `Zkc.Construction.Uniform.ScalarFragment,
  `Zkc.Construction.Uniform.ScalarProjection,
  `Zkc.Construction.Uniform.ScalarObservation,
  `Zkc.Construction.Uniform.ScalarPresentation,
  `Zkc.Construction.Uniform.ScalarHandles,
  `ZkcExamples.Construction.SchnorrDomainConnection,
  `ZkcExamples.Construction.SchnorrAndDomainConnection,
  `ZkcExamples.Construction.ChaumPedersenDomainConnection,
  `ZkcExamples.Construction.OkamotoDomainConnection,
  `ZkcExamples.Construction.GuessDomainConnection,
  `ZkcExamples.Construction.SumcheckSourceConnection,
  `ZkcExamples.Construction.ComposedSumcheckScalarConnection,
  `ZkcExamples.Construction.ComposedSumcheckSourceHandles,
  `Zkc.Construction.Uniform.ScalarCheckedFrames,
  `Zkc.Construction.Uniform.ScalarSourceCost,
  `Zkc.Construction.Uniform.ScalarCheckedBytes,
  `ZkcExamples.Executable.SumcheckCheckedRound,
  `ZkcExamples.Executable.SumcheckSourceHonest,
  `ZkcExamples.Executable.SumcheckDomainHonest,
  `ZkcExamples.Executable.SumcheckCharges,
  `ZkcExamples.Executable.SumcheckCompleteness] "RETAINED-SCALAR-AXIOMS-PASS" true

run_cmd ZkcTools.DeclarationAudit.checkRegistry [
  ("scalar-message-support", some `Zkc.Construction.Uniform.ScalarSupport.Message, true),
  ("scalar-action-support", some `Zkc.Construction.Uniform.ScalarSupport.Action, true),
  ("scalar-process-support", some `Zkc.Construction.Uniform.ScalarSupport.Supported, true),
  ("scalar-source-operation", some `Zkc.Construction.Uniform.ScalarFragment.sourceOperation, true),
  ("scalar-captured-protocols", some `Zkc.Construction.Uniform.ScalarFragment.Protocols, true)] [`Zkc.Construction.ScalarConnection, `Zkc.Construction.Uniform.ScalarSupport,
   `Zkc.Construction.Uniform.ScalarFragment, `Zkc.Construction.Uniform.ScalarObservation,
   `Zkc.Construction.Uniform.ScalarPresentation, `Zkc.Construction.Uniform.ScalarHandles] "RETAINED-SCALAR-PREMISES-PASS"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := [``ZkcExamples.Construction.SchnorrProof.compiled_transform,
    ``ZkcExamples.Construction.SchnorrAndProof.compiled_transform,
    ``ZkcExamples.Construction.ChaumPedersenProof.compiled_transform,
    ``ZkcExamples.Construction.OkamotoProof.compiled_transform,
    ``ZkcExamples.Construction.GuessProof.compiled_transform,
    ``ZkcExamples.Construction.SumcheckProof.compiled_transform,
    ``ZkcExamples.Construction.ComposedSumcheckProof.compiled_transform]
  let retired := [`Zkc.Construction.Uniform.OccurrenceSourceProcess,
    `ZkcExamples.Construction.SumcheckDomainConnection,
    `ZkcExamples.Construction.SumcheckDomainControls,
    `ZkcExamples.Construction.SumcheckDomainRound,
    `ZkcExamples.Construction.SumcheckDomainLoop,
    `ZkcExamples.Construction.SumcheckDomainRoot,
    `ZkcExamples.Construction.SumcheckScalarProtocol,
    `ZkcExamples.Construction.SumcheckScalarRound,
    `ZkcExamples.Construction.SumcheckDomainVerifier,
    `ZkcExamples.Construction.ComposedSumcheckSourceRouting,
    `ZkcExamples.Construction.ComposedSumcheckDomainConnection,
    `ZkcExamples.Structured.OriginalArtifacts.TwoSums,
    `ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot,
    `ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding,
    `ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingHelpers,
    `ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingLoop,
    `ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates,
    `ZkcExamples.Structured.SumcheckArtifacts.ArtifactRoot,
    `ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs,
    `ZkcExamples.Executable.SumcheckFamilySource,
    `ZkcExamples.Executable.SumcheckFamilyResources,
    `ZkcExamples.Executable.SumcheckFamily]
  let required := [``Zkc.Construction.SourceConnection.Connected.simulation,
    ``Zkc.Construction.SourceConnection.Connected.coverage,
    ``Zkc.Construction.ScalarConnection.transform,
    ``Zkc.Construction.Uniform.ScalarFragment.participant_supported]
  for root in roots do
    let mut pending := [root]
    let mut seen : Std.HashSet Name := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if seen.contains name then continue
      seen := seen.insert name
      if let some owner := ZkcTools.DeclarationAudit.moduleOf env name then
        if retired.contains owner then
          throwError "retained execution uses retired authority: {root} reaches {name} in {owner}"
      let some info := env.find? name | throwError "missing dependency: {name}"
      let values := (info.value? true).map Expr.getUsedConstants |>.getD #[]
      pending := (info.type.getUsedConstants ++ values).toList ++ pending
    for name in required do
      unless seen.contains name do throwError "{root} does not consume generic connection evidence {name}"
    if root == ``ZkcExamples.Construction.ComposedSumcheckProof.compiled_transform then
      unless seen.contains ``ZkcExamples.Construction.ComposedSumcheckSourceHandles.participant_handle do
        throwError "TwoSums execution does not consume full source capability naturality"
    logInfo m!"RETAINED-SCALAR-TRANSPORT-PASS root={root} dependencies={seen.size}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let checks := [
    (``ZkcExamples.Executable.SumcheckCharges.sufficient, [``Zkc.Construction.Uniform.ScalarSourceCost.fits,
      ``Zkc.Construction.ConnectionCertificate.Alignment.librarySimulation]),
    (``ZkcExamples.Executable.SumcheckCompleteness.honest_accepted,
      [``Zkc.Construction.SourceConnection.Connected.simulation,
        ``Zkc.Construction.Uniform.ScalarCheckedBytes.connected,
        ``Zkc.Construction.Uniform.ScalarSourceCost.fits]),
    (``ZkcExamples.Executable.SumcheckProof.executable_transform_prunes,
      [``Zkc.Construction.SourceConnection.Connected.simulation])]
  let retired := [`ZkcExamples.Construction.SumcheckDomainConnection,
    `ZkcExamples.Construction.SumcheckDomainRound, `ZkcExamples.Construction.SumcheckDomainLoop,
    `ZkcExamples.Construction.SumcheckDomainRoot, `ZkcExamples.Construction.SumcheckScalarRound,
    `ZkcExamples.Construction.SumcheckScalarProtocol, `ZkcExamples.Construction.SumcheckDomainVerifier,
    `ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding,
    `ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingHelpers,
    `ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingLoop,
    `ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates,
    `ZkcExamples.Structured.SumcheckArtifacts.ArtifactRoot,
    `ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs,
    `ZkcExamples.Executable.SumcheckFamilySource, `ZkcExamples.Executable.SumcheckFamilyResources,
    `ZkcExamples.Executable.SumcheckFamily, `Zkc.Construction.Uniform.OccurrenceSourceProcess]
  for (root, required) in checks do
    let mut pending := [root]
    let mut seen : Std.HashSet Name := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      if seen.contains name then continue
      seen := seen.insert name
      if let some owner := ZkcTools.DeclarationAudit.moduleOf env name then
        if retired.contains owner then throwError "retained byte/cost proof reaches manual authority: {root} reaches {name}"
      let some info := env.find? name | throwError "missing dependency: {name}"
      let values := (info.value? true).map Expr.getUsedConstants |>.getD #[]
      pending := (info.type.getUsedConstants ++ values).toList ++ pending
    for name in required do
      unless seen.contains name do throwError "{root} does not consume {name}"
    logInfo m!"RETAINED-SCALAR-BYTE-COST-PASS root={root} dependencies={seen.size}"

#print axioms Zkc.Construction.ScalarConnection.runK
#print axioms Zkc.Construction.ScalarConnection.transform
#print axioms Zkc.Construction.Uniform.ScalarPresentation.connected
#print axioms ZkcExamples.Executable.SchnorrProof.executable_transform
