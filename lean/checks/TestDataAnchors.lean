import checks.DeclarationRecords
import Tests.ArtifactDataAnchors

open Lean Elab Command DeclarationRecords

-- A duplicate in a larger reporting environment must not enter the anchors
-- observed from the stored defining module of a request or receipt.
def unrelatedOriginal := Tests.ArtifactDataAnchors.original

run_cmd liftTermElabM do
  let source ← dataAnchors `Tests.ArtifactDataAnchors.pair
    `Zkc.Source.Structured.Snapshot (mkConst `Tests.ArtifactDataAnchors.selectedOriginal)
  let participant ← dataAnchors `Tests.ArtifactDataAnchors.pair
    `Zkc.Construction.Participant (mkConst `Tests.ArtifactDataAnchors.selectedParticipant)
  let names (value : Json) := ReceiptAudit.strings value
  unless (names source).contains "Tests.ArtifactDataAnchors.original" &&
      !(names source).contains "Tests.ArtifactDataAnchors.changedOriginal" &&
      !(names source).contains "unrelatedOriginal" do
    throwError "source anchor mismatch: {source.compress}"
  unless (names participant).contains "Tests.ArtifactDataAnchors.participant" &&
      !(names participant).contains "Tests.ArtifactDataAnchors.changedParticipant" &&
      !(names participant).contains "Tests.ArtifactDataAnchors.producer" do
    throwError "participant anchor mismatch: {participant.compress}"
  logInfo "PASS: generic projections; complete data equality; fixed module closure"
