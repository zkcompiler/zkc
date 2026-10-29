import ZkcSecurity.Generation.SumcheckAccounts
import ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessClaims
import ZkcSecurity.Examples.Generated.TwoSumsSoundnessClaims
import Tests.ProofAccount

/-! Private bodies remain available to the one shared application inspector.
This executable measures provenance; it computes no receipt acceptance status. -/
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
open Lean Elab Command

-- A type-only name mention supplies no application in the checked proof body.
theorem unrelatedMentions
    (_unused : ZkcSecurity.Realizations.Sumcheck.SourceRootReference.reductionAssociation
      ZkcExamples.Structured.SumcheckSourceSelections.Selection.twoSums =
      ZkcSecurity.Realizations.Sumcheck.SourceRootReference.reductionAssociation
        ZkcExamples.Structured.SumcheckSourceSelections.Selection.twoSums) : True := True.intro

run_cmd do
  let mut accounts := #[]
  let roots ← ZkcSecurity.Generation.Roots.evaluateSelections
  for root in roots do
    let receipt := (root.subjectModule ++ "SoundnessClaims.request1Receipt").toName
    accounts := accounts.push (← liftTermElabM <| ZkcSecurity.Generation.SumcheckAccounts.measure root receipt)
    liftTermElabM do
      Tests.ProofAccount.expectRefusal "stale source" "catalogue snapshot differs" <|
        ZkcSecurity.Generation.SumcheckAccounts.sourceAssociation
          { root with snapshot := { root.snapshot with source := "stale" } }
      Tests.ProofAccount.expectRefusal "changed body, unchanged identity" "catalogue snapshot differs" <|
        ZkcSecurity.Generation.SumcheckAccounts.sourceAssociation
          { root with snapshot := { root.snapshot with definitions := [] } }
      let graph ← ZkcTools.ProofAccount.reachable receipt
      let selection ← ZkcSecurity.Generation.SumcheckAccounts.sourceAssociation root
      Tests.ProofAccount.expectRefusal "wrong static bound" "typed association mismatch" <|
        ZkcSecurity.Generation.SumcheckAccounts.templateAssociation graph selection 3
      let .ok program := Zkc.Source.Structured.check root.snapshot | throwError "source admission"
      let .ok layout := ZkcTools.ConstructionBindings.analyze program root.artifacts.validator
        | throwError "source/artifact analysis"
      if let first :: second :: _ := layout.calls then
        Tests.ProofAccount.expectRefusal "sibling occurrence" "nominal source occurrence mismatch" <|
          ZkcSecurity.Generation.SumcheckAccounts.occurrenceAssociation first second
        Tests.ProofAccount.expectRefusal "changed query template" "nominal source occurrence mismatch" <|
          ZkcSecurity.Generation.SumcheckAccounts.occurrenceAssociation first { first with query := second.query }
        Tests.ProofAccount.expectRefusal "changed delivery template" "nominal source occurrence mismatch" <|
          ZkcSecurity.Generation.SumcheckAccounts.occurrenceAssociation first { first with delivery := second.delivery }
      Tests.ProofAccount.expectRefusal "wrong receipt root" "declaration is not reached" <|
        ZkcSecurity.Generation.SumcheckAccounts.measure root ``Tests.ProofAccount.dependent
  liftTermElabM do
    Tests.ProofAccount.expectRefusal "names only in a type" "missing application" <|
      ZkcTools.ProofAccount.account (← ZkcTools.ProofAccount.reachable ``unrelatedMentions) {
        identifier := "name-only", phase := "association", responsibility := "I"
        owner := ``unrelatedMentions
        callee := ``Zkc.Source.Structured.Template.Association.invoke, route := .generalRule }
  logInfo "DERIVATION-ASSOCIATION-CONTROLS-PASS"
  elabCommand (← `(def $(mkIdent `accountsJson) : String := $(quote (Json.arr accounts).compress)))

def main (arguments : List String) : IO Unit := do
  let [destination] := arguments | throw (IO.userError "expected output JSON path")
  IO.FS.writeFile destination (accountsJson ++ "\n")
