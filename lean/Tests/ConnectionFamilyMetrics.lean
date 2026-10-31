import ZkcTools.ConstructionBindings.Alignment
import Lean.Util.NumObjs

/-! Audits actual root consumers without unfolding family bodies. Primitive
root operations are allowed; application bodies must be compact references. -/
public meta section
namespace Tests.ConnectionFamilyMetrics
open Lean Meta Elab Command
open ZkcTools.ConstructionBindings

private def rootPhase (message : String) : CoreM Unit := do
  if !(← getOptions).getBool `zkc.connection.trace false then return
  let destination := (← getOptions).get `zkc.connection.traceFile ("" : String)
  unless destination.isEmpty do
    IO.FS.withFile destination .append fun handle => do
      handle.putStrLn s!"{← IO.monoMsNow} {message}"

syntax "measured_family_root " ident " : " term " := " term : command
elab_rules : command
  | `(measured_family_root $identifier:ident : $type:term := $proof:term) => liftTermElabM do
    let start ← IO.monoNanosNow
    let expected ← Term.elabType type
    let value ← Term.elabTermEnsuringType proof expected
    rootPhase "root term elaborated"
    Term.synthesizeSyntheticMVarsNoPostponing
    let expected ← instantiateMVars expected
    let value ← instantiateMVars value
    if value.hasMVar || value.hasSorry then throwError "unfinished family root"
    rootPhase "root sharing"
    let (expected, value) := _root_.ShareCommon.shareCommon' (expected, value)
    let name := (← getCurrNamespace) ++ identifier.getId
    rootPhase "root declaration preparation"
    let declaration ← mkDefinitionValInferringUnsafe name [] expected value
      (.regular (getMaxHeight (← getEnv) value + 1))
    let proposed ← IO.monoNanosNow
    rootPhase "root kernel start"
    withOptions (Elab.async.set · false) <| addDecl (.defnDecl declaration)
    let checked ← IO.monoNanosNow
    modifyEnv (addNoncomputable · name)
    rootPhase "root kernel done"
    logInfo m!"FAMILY-ROOT-COST {name}: proposal_ns={proposed-start}; kernel_ns={checked-proposed}"

elab "audit_family_interfaces" : command => liftTermElabM do
  for name in TargetPlacement.checkedBodies.getState (← getEnv) do
    let info ← getConstInfo name
    if info.value!.hasSorry || info.value!.hasMVar then throwError "unfinished family"
    Interface.auditFamilyType info.type
    forallTelescopeReducing info.type fun parameters result => do
      unless result.isAppOf ``Zkc.Construction.ConnectionTargetPlacement.CheckedBody do
        throwError "unexpected checked family result"
      let mut heads : Array String := #[]
      for parameter in parameters do
        let type ← whnf (← inferType parameter)
        if type.isAppOf ``Zkc.Construction.ConnectionCertificate.Alignment then
          throwError "family requires an alignment"
        if type.isAppOf ``Eq then
          let head := toString type.getAppArgs[0]!.getAppFn.constName?
          unless heads.contains head do heads := heads.push head
      logInfo m!"FAMILY-INTERFACE-AUDIT {name}: parameters={parameters.size}; equality_types={heads}"

elab "audit_family_root " identifier:ident count:num : command => liftTermElabM do
  let name ← realizeGlobalConstNoOverloadWithInfo identifier
  let info ← getConstInfo name
  let value := info.value!
  if value.hasSorry || value.hasMVar then throwError "unfinished family root"
  let families := TargetPlacement.checkedBodies.getState (← getEnv)
  rootPhase "root reference audit start"
  let applications ← Family.applications value
  unless applications.size == count.getNat do throwError "unexpected application count"
  let mut counts := families.map fun family => (family, 0)
  for application in applications do
    let mut type := (← getConstInfo application.getAppFn.constName!).type
    for argument in application.getAppArgs do
      let .forallE field _ body _ := type | throwError "invalid application constructor"
      if field == `bodyCertificate || field == `physicalExtent then
        let projection := if field == `bodyCertificate then
            ``Zkc.Construction.ConnectionTargetPlacement.CheckedBody.alignment
          else ``Zkc.Construction.ConnectionTargetPlacement.CheckedBody.physicalExtent
        unless argument.isAppOf projection do throwError "application body was reconstructed"
        let reference := argument.getAppArgs.back!.getAppFn.constName!
        let family := reference
        unless families.contains family do throwError "placement is not a family application"
        counts := counts.map fun (name, count) => (name, count + if name == family then 1 else 0)
      type := body.instantiate1 argument
  let references := counts.foldl (fun total (_, count) => total + count) 0
  unless references == 2 * count.getNat do
    throwError "family-root-reference-count: expected {2 * count.getNat}, found {references}"
  rootPhase "root reference audit done"
  let serializedCounts := counts.map fun (name, count) => (name.toString, toJson count)
  logInfo m!"FAMILY-ROOT-AUDIT {Json.mkObj [
    ("root", toJson name.toString), ("applications", toJson count.getNat),
    ("family_references", Json.mkObj serializedCounts.toList),
    ("expression_objects", toJson (← value.numObjs)),
    ("retained_exact_bodies", toJson (0 : Nat))]}"

end Tests.ConnectionFamilyMetrics
