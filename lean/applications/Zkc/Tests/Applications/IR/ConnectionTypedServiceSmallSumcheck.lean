import Zkc.Applications.IR.Structured.Generated.Connections.SmallSumcheck

/-! Audit the actual producer, validator and installed families. This check
requires their existing certificates and preserves the repeated source body. -/
set_option autoImplicit false
namespace Tests.ConnectionTypedServiceSmallSumcheck
open Lean Meta Elab Command
open Zkc.Construction ZkcTools.ConstructionBindings

run_cmd liftTermElabM do
  let owner := `ZkcExamples.Structured.Generated.Connections.SmallSumcheck
  let families := (TargetPlacement.checkedBodies.getState (← getEnv)).filter owner.isPrefixOf
  unless families.size ≥ 2 do throwError "missing-actual-service-families"
  for name in families do
    let info ← getConstInfo name
    Interface.auditFamilyType info.type
    if info.value!.hasSorry || info.value!.hasMVar then throwError "unfinished-actual-family"
  for name in families.toList ++ [
      ``ZkcExamples.Structured.Generated.Connections.SmallSumcheck.producer,
      ``ZkcExamples.Structured.Generated.Connections.SmallSumcheck.validator,
      ``ZkcExamples.Structured.Generated.Connections.SmallSumcheck.producerConnected,
      ``ZkcExamples.Structured.Generated.Connections.SmallSumcheck.validatorConnected] do
    for axiomName in ← collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected-actual-service-axiom: {name}: {axiomName}"
  let mut repeated := false
  let mut queried := false
  let mut reused := false
  for (name, info) in (← getEnv).constants.toList do
    unless owner.isPrefixOf name do continue
    unless families.contains name ||
        [``ConnectionCertificate.Alignment, ``ConnectionCertificate.Certificate,
        ``ConnectionTargetPlacement.CheckedBody, ``ConnectionRoot.RootCertificate].any
        info.type.isAppOf do continue
    if let some value := info.value? then
      repeated := repeated || (value.find? fun expression =>
        expression.isAppOf ``ConnectionCertificate.Alignment.repeat ||
        expression.isAppOf ``ConnectionCertificate.Alignment.projectedRepeat).isSome
      queried := queried || (value.find?
        (·.isAppOf ``ConnectionCertificate.Alignment.publicQuery)).isSome
      reused := reused || (value.find? fun expression =>
        expression.isAppOfArity ``ConnectionTargetPlacement.CheckedBody.alignment 7 &&
        expression.getAppArgs.back!.getAppFn.constName?.any families.contains).isSome
  unless repeated && queried && reused do
    throwError "missing-actual-family-use: repeat={repeated}; query={queried}; reuse={reused}"
  logInfo m!"ACTUAL-SERVICE-FAMILIES {families.size}; endpoints=2; repeated-query; standard-axioms"

end Tests.ConnectionTypedServiceSmallSumcheck
