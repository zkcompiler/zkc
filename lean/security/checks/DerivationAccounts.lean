import ZkcSecurity.Generation.SumcheckAccounts
import ZkcSecurity.Examples.Generated.SmallSumcheckSoundnessClaims
import ZkcSecurity.Examples.Generated.TwoSumsSoundnessClaims
import Tests.ProofAccount

/-! Non-module executable: private theorem bodies are available to the
measurement inspector. No receipt status is computed by this executable. -/
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
open Lean Elab Command

-- Both names occur in this theorem, but it is not a call correspondence.
theorem unrelatedMentions
    (_unused : ZkcExamples.Structured.Generated.Original.TwoSums.step1Realized
      (F := Rat) (G := Rat) (some 0) (some 0) (.cons (some []) (.cons (some 0) .nil)) =
      ZkcExamples.Structured.Generated.Original.TwoSums.step1Realized
      (F := Rat) (G := Rat) (some 0) (some 0) (.cons (some []) (.cons (some 0) .nil))) :
    ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1 =
      ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1 := rfl

run_cmd do
  let mut accounts := #[]
  let roots ← ZkcSecurity.Generation.Roots.evaluateSelections
  for root in roots do
    let receipt := (root.subjectModule ++ "SoundnessClaims.request1Receipt").toName
    let account ← liftTermElabM <| ZkcSecurity.Generation.SumcheckAccounts.measure root receipt
    accounts := accounts.push account
    liftTermElabM do
      Tests.ProofAccount.expectRefusal "stale source" "catalogue snapshot differs" <|
        ZkcSecurity.Generation.SumcheckAccounts.sourceAssociation
          { root with snapshot := { root.snapshot with source := "stale" } }
      Tests.ProofAccount.expectRefusal "changed body, unchanged identity" "catalogue snapshot differs" <|
        ZkcSecurity.Generation.SumcheckAccounts.sourceAssociation
          { root with snapshot := { root.snapshot with definitions := [] } }
  liftTermElabM do
    let graph ← ZkcTools.ProofAccount.reachable
      ``ZkcSecurity.Examples.Generated.TwoSumsSoundnessClaims.request1Receipt
    Tests.ProofAccount.expectRefusal "sibling occurrence" "typed association mismatch" <|
      ZkcSecurity.Generation.SumcheckAccounts.occurrenceAssociation graph
        ``ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Sources.call0_raw
        ``ZkcExamples.Structured.Generated.Original.TwoSums.step1Realized
        ``ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1
        4
    Tests.ProofAccount.expectRefusal "wrong static bound" "typed association mismatch" <|
      ZkcSecurity.Generation.SumcheckAccounts.occurrenceAssociation graph
        ``ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Sources.call0_raw
        ``ZkcExamples.Structured.Generated.Original.TwoSums.step1Realized
        ``ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0
        3
    Tests.ProofAccount.expectRefusal "names in an unrelated statement" "typed association mismatch" <|
      ZkcSecurity.Generation.SumcheckAccounts.occurrenceAssociation
        (← ZkcTools.ProofAccount.reachable ``unrelatedMentions) ``unrelatedMentions
        ``ZkcExamples.Structured.Generated.Original.TwoSums.step1Realized
        ``ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1
        4
    -- The WP root consumes the terminal contract. The mathematical discharge
    -- is inside that reached contract, not a direct application in the root.
    Tests.ProofAccount.expectRefusal "stale direct terminal attribution" "missing application" <|
      ZkcTools.ProofAccount.account graph {
        identifier := "stale-terminal", phase := "terminal", responsibility := "M"
        owner := ``ZkcSecurity.Realizations.Sumcheck.OriginalRaw.composition_rejected
        callee := ``ZkcSecurity.Realizations.Sumcheck.OriginalRaw.terminal_rejected
        proofObjectHeads := [``Zkc.Obligations.Derivation], route := .familyPackage }
    let some root := roots.head? | throwError "missing root"
    Tests.ProofAccount.expectRefusal "wrong receipt root" "declaration is not reached" <|
      ZkcSecurity.Generation.SumcheckAccounts.measure root ``Tests.ProofAccount.dependent
  logInfo "DERIVATION-ASSOCIATION-CONTROLS-PASS"
  elabCommand (← `(def $(mkIdent `accountsJson) : String := $(quote (Json.arr accounts).compress)))

def main (arguments : List String) : IO Unit := do
  let [destination] := arguments | throw (IO.userError "expected output JSON path")
  IO.FS.writeFile destination (accountsJson ++ "\n")
