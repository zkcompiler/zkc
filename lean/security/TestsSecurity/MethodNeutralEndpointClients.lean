import TestsSecurity.MethodNeutralChargeAssembly
import ZkcSecurityTools.Generation.OriginalEndpoint
import Lean.Elab.Frontend

/-! Exercise the actual common printer and elaborate its declarations in an
isolated environment. Wrong declaration names fail at the owning dependent
boundary; no string selection is accepted as mathematical evidence. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.MethodNeutralEndpointClients
open ZkcSecurity.Generation ZkcSecurity.Examples.Generated
open Zkc.Source Zkc.Source.Structured Zkc.Construction

private def output : OriginalEndpoint.Output where
  moduleName := "GeneratedChargeClient"
  subjectModule := "ZkcSecurityExamples.Generated.TwoSums"
  subjectNamespace := "ZkcSecurity.Examples.Generated.TwoSums"
  methodModule := "TestsSecurity.MethodNeutralChargeAssembly"
  sampling := "ZkcSecurity.Domains.PrimeField.rawSampleable blsModulus"
  capabilities := "TestsSecurity.MethodNeutralChargeAssembly.Heterogeneous.capabilities"
  schedule := "TestsSecurity.MethodNeutralChargeAssembly.Heterogeneous.schedule"
  validatorCost := "TestsSecurity.MethodNeutralChargeAssembly.Heterogeneous.validatorCost"
  chargedExport := "TestsSecurity.MethodNeutralChargeAssembly.Heterogeneous.reductionExport"
  scalar := some ⟨"TestsSecurity.MethodNeutralChargeAssembly.Heterogeneous.scalarBound",
    "TestsSecurity.MethodNeutralChargeAssembly.Heterogeneous.scalar_bound"⟩

private meta def check (metadata : SubjectABI.Metadata) (validator : Participant) (name : String)
    (selection : OriginalEndpoint.Output) (refused : Bool) : Lean.Elab.Command.CommandElabM Unit := do
  let .ok source := OriginalEndpoint.soundnessSource metadata validator selection
    | Lean.throwError m!"printer refused declaration client {name}"
  -- Imports have already been loaded above. Elaborate exactly the printer's
  -- declaration body, retaining its local instances and dependent annotations.
  let [_, body] := source.splitOn "@[expose] public section\n"
    | Lean.throwError "printer header changed"
  let options := (← Lean.getOptions).setBool `Elab.async false
  let (_, messages) ← Lean.Elab.process body (← Lean.getEnv) options
  unless messages.hasErrors == refused do
    let details ← messages.toList.mapM (fun message => message.toString)
    Lean.throwError m!"unexpected elaboration result for {name}: {details}"

run_cmd do
  let metadata ← Lean.Elab.Command.liftTermElabM do
    let expression ← Lean.Elab.Term.elabTerm (← `(SubjectABI.metadata TwoSums.subject)) none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
    Lean.Meta.evalExpr SubjectABI.Metadata (Lean.mkConst ``SubjectABI.Metadata) reduced
  let validator ← Lean.Elab.Command.liftTermElabM do
    let expression ← Lean.Elab.Term.elabTerm (← `(TwoSums.validatorArtifacts.participant)) none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
    Lean.Meta.evalExpr Participant (Lean.mkConst ``Participant) reduced
  check metadata validator "heterogeneous scalar" output false
  check metadata validator "heterogeneous charged only" { output with scalar := none } false
  check metadata validator "wrong subject" { output with
    schedule := "Claims.Domain.ChargeSchedule.empty ZkcSecurity.Examples.Generated.SmallSumcheck.validatorSubject" } true
  check metadata validator "wrong schedule" { output with
    schedule := "Claims.Domain.ChargeSchedule.empty validatorSubject" } true
  check metadata validator "wrong cost" { output with validatorCost := "fun _ => 0" } true
  check metadata validator "wrong scalar conversion" { output with scalar := some ⟨"TestsSecurity.MethodNeutralChargeAssembly.Heterogeneous.scalarBound",
        "TestsSecurity.MethodNeutralChargeAssembly.Heterogeneous.costLaw"⟩ } true
  Lean.logInfo "PASS common printer: heterogeneous scalar/charged clients; wrong subject, schedule, cost and conversion refused"

end TestsSecurity.MethodNeutralEndpointClients
