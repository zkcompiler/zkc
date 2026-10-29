import TestsSecurity.OriginalPairExecution
import TestsSecurity.OriginalProducerBinding
import TestsSecurity.SourceReading
import TestsSecurity.ConnectionABI
import TestsSecurity.ConnectionMetadata
import Tests.ConnectionContracts
import ZkcTools.DeclarationAudit
import Lean.Util.FoldConsts

/-! Strict assumption and dependency checks for the migrated controls. The
sharing check inspects stored declarations only for provenance; it neither
constructs a simulation nor changes the fixed connection meaning. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace TestsSecurity.ConnectionRetirementAudit

run_cmd ZkcTools.DeclarationAudit.check [
  `TestsSecurity.OriginalPairExecution, `TestsSecurity.OriginalProducerBinding,
  `TestsSecurity.SourceReading, `TestsSecurity.ConnectionABI,
  `TestsSecurity.ConnectionMetadata, `Tests.ConnectionContracts] "CONNECTION-RETIREMENT-AXIOMS-PASS" true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let shared := [``Zkc.Construction.SourceConnection.ofRootCertificate,
    ``Zkc.Construction.ConnectionRoot.RootCertificate.simulation,
    ``Zkc.Construction.ConnectionRoot.RootCertificate.routeCoverage]
  let retired := ["ZkcExamples.Structured.OriginalArtifacts.",
    "ZkcExamples.Structured.Generated.OriginalArtifacts.",
    "ZkcExamples.Structured.SumcheckArtifacts.Artifact",
    "ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer",
    "ZkcSecurity.Generation.ConstructionBindings",
    "ZkcSecurity.Realizations.Sumcheck.OriginalHonest",
    "ZkcSecurity.Realizations.Sumcheck.OriginalRoot",
    "ZkcTools.ConstructionBindings.Source"]
  let constructors := [``Zkc.Construction.Original.Simulation.done,
    ``Zkc.Construction.Original.Simulation.halt,
    ``Zkc.Construction.Original.Simulation.call,
    ``Zkc.Construction.Original.Simulation.checkpoint]
  for root in [
      ``ZkcExamples.Structured.Generated.Connections.SmallSumcheck.producerConnected,
      ``ZkcExamples.Structured.Generated.Connections.SmallSumcheck.validatorConnected,
      ``ZkcExamples.Structured.Generated.Connections.TwoSums.producerConnected,
      ``ZkcExamples.Structured.Generated.Connections.TwoSums.validatorConnected] do
    let mut pending := [root]
    let mut seen : NameSet := {}
    while let name :: rest := pending do
      pending := rest
      if seen.contains name then continue
      seen := seen.insert name
      let some owner := ZkcTools.DeclarationAudit.moduleOf env name | continue
      if retired.any (fun retiredModule => owner.toString.startsWith retiredModule) then
        throwError "retired connection authority below {root}: {name} in {owner}"
      let info ← getConstInfo name
      let used := info.type.getUsedConstants ++ ((info.value? true).map Expr.getUsedConstants).getD #[]
      if owner.toString.startsWith "ZkcExamples.Structured.Generated.Connections." &&
          used.any constructors.contains then
        throwError "instance simulation construction below {root}: {name}"
      pending := used.toList ++ pending
    for name in shared do
      unless seen.contains name do throwError "missing shared connection fact below {root}: {name}"
    logInfo m!"CONNECTION-RETIREMENT-SHARING-PASS root={root} declarations={seen.size}"

end TestsSecurity.ConnectionRetirementAudit
