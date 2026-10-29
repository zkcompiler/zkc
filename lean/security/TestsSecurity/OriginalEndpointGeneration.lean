module

import ZkcSecurity.Generation.Roots.Stages
meta import ZkcSecurity.Generation.Roots.Stages

/-! Production metadata, refusal and naming controls. No proof choice is
owned by this test; the one production catalogue supplies every selection. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.OriginalEndpointGeneration
open ZkcSecurity.Generation ZkcSecurity.Generation.Roots
open Zkc.Source Zkc.Source.Structured Zkc.Construction

private meta def refuses {α : Type} (code : String) (result : Except String α) :
    Lean.Elab.Command.CommandElabM Unit :=
  match result with
  | .error actual => unless actual == code do Lean.throwError m!"expected {code}, got {actual}"
  | .ok _ => Lean.throwError m!"generation accepted invalid input: {code}"

run_cmd do
  let roots ← evaluateSelections
  for root in roots do
    let metadata ← Lean.Elab.Command.liftTermElabM do
      let subject := Lean.mkIdent ((root.subjectModule ++ ".subject").toName)
      let expression ← Lean.Elab.Term.elabTerm (← `(SubjectABI.metadata $subject)) none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
      Lean.Meta.evalExpr SubjectABI.Metadata (Lean.mkConst ``SubjectABI.Metadata) reduced
    let validator := root.artifacts.validator
    let output := soundnessOutput root
    let .ok generated := OriginalEndpoint.soundnessSource metadata validator output
      | Lean.throwError "valid original endpoint refused"
    refuses "original-endpoint-validator-interface-mismatch"
      (OriginalEndpoint.soundnessSource metadata { validator with inputs := [] } output)
    let .ok emptySyntax := OriginalEndpoint.soundnessSource metadata { validator with instructions := [] } output
      | Lean.throwError "common endpoint refused zero syntactic queries"
    unless emptySyntax.contains "syntacticBudget : Nat := 0" do
      Lean.throwError "zero syntax budget metadata lost"
    let .ok chargedOnly := OriginalEndpoint.soundnessSource metadata validator { output with scalar := none }
      | Lean.throwError "charged-only endpoint refused"
    unless !chargedOnly.contains "scalar_meaning" && !chargedOnly.contains "scalarBound" do
      Lean.throwError "charged-only endpoint gained a scalar conversion"
    for forbidden in ["Fintype.card", "uniformSchedule", "priceBound", "schedule_prices", "1 /", "abbrev Scalar"] do
      if generated.contains forbidden || chargedOnly.contains forbidden then
        Lean.throwError "common endpoint still installs uniform pricing: {forbidden}"
    refuses "original-endpoint-private-target-requires-residual-contract"
      (OriginalEndpoint.soundnessSource { metadata with publicPositions := [] } validator output)
    let renamed := { root with name := "RenamedEndpoint" }
    let .ok renamedSource := OriginalEndpoint.soundnessSource metadata validator (soundnessOutput renamed)
      | Lean.throwError "root naming changed generation applicability"
    let renamedExpected := (generated.replace root.subjectModule renamed.subjectModule).replace
      (root.componentModule "Soundness") (renamed.componentModule "Soundness")
    unless renamedExpected.replace root.securityModule renamed.securityModule == renamedSource do
      Lean.throwError "root name changes behavior rather than output naming"
  unless stageSources.length == roots.length * 6 do
    Lean.throwError "production output inventory differs"
  unless stageSources.all (fun (stage, _, source) =>
      stage != "rounds" && stage != "views" && !source.contains "RoundDescriptors" &&
        !source.contains "ValidatorView" && !source.contains "pattern17" && !source.contains "pattern23") do
    Lean.throwError "retired matcher remains in production output"
  Lean.logInfo "PASS original endpoint metadata, refusals, naming and production inventory"

end TestsSecurity.OriginalEndpointGeneration
