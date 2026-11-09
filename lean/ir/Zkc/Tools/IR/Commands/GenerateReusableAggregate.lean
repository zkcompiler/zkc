import Zkc.Tests.IR.ReusableAggregateTwoBatchesArtifacts
import Zkc.Tools.IR.ConstructionBindings.Generate

/-! Data-only selection for the independently authored aggregate client.
The shared printer produces both constructed views and their root connection. -/
open ZkcTools.ConstructionBindings.Generate
open Tests.ReusableAggregateTwoBatchesArtifacts

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  let source : Selection := ⟨`Zkc.Tests.Applications.IR.ReusableAggregateTwoBatchesSource,
    `Tests.ReusableAggregateTwoBatchesSource.program⟩
  let roles : List (ParticipantSelection × Zkc.Construction.Participant) := [
    ({ mode := .producer, artifactModule := `Zkc.Tests.IR.ReusableAggregateTwoBatchesArtifacts
       artifact := `Tests.ReusableAggregateTwoBatchesArtifacts.Producer.participant
       viewModule := `Zkc.Tests.IR.ReusableAggregateTwoBatchesProducer
       viewNamespace := `Tests.ReusableAggregateTwoBatchesProducer }, Producer.participant),
    ({ mode := .validator, artifactModule := `Zkc.Tests.IR.ReusableAggregateTwoBatchesArtifacts
       artifact := `Tests.ReusableAggregateTwoBatchesArtifacts.Validator.participant
       viewModule := `Zkc.Tests.IR.ReusableAggregateTwoBatchesValidator
       viewNamespace := `Tests.ReusableAggregateTwoBatchesValidator }, Validator.participant)]
  let .ok sources := bundle source `Zkc.Tests.Applications.IR.ReusableAggregateTwoBatchesConnection roles
    `Tests.ReusableAggregateTwoBatchesConnection
    | throw (IO.userError "aggregate connection selection refused")
  for (name, text) in sources do
    let path := System.FilePath.mk directory / (name.toString.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path text
    IO.println s!"generated {name}"
