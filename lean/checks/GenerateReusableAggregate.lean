import Tests.ReusableAggregateTwoBatchesArtifacts
import ZkcTools.ConstructionBindings.Generate

/-! Data-only selection for the independently authored aggregate client.
The shared printer produces both constructed views and their root connection. -/
open ZkcTools.ConstructionBindings.Generate
open Tests.ReusableAggregateTwoBatchesArtifacts

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  let source : Selection := ⟨`Tests.ReusableAggregateTwoBatchesSource,
    `Tests.ReusableAggregateTwoBatchesSource.program⟩
  let roles : List (ParticipantSelection × Zkc.Construction.Participant) := [
    (⟨.producer, `Tests.ReusableAggregateTwoBatchesArtifacts,
      `Tests.ReusableAggregateTwoBatchesArtifacts.Producer.participant,
      `Tests.ReusableAggregateTwoBatchesProducer⟩, Producer.participant),
    (⟨.validator, `Tests.ReusableAggregateTwoBatchesArtifacts,
      `Tests.ReusableAggregateTwoBatchesArtifacts.Validator.participant,
      `Tests.ReusableAggregateTwoBatchesValidator⟩, Validator.participant)]
  let .ok sources := bundle source `Tests.ReusableAggregateTwoBatchesConnection roles
    | throw (IO.userError "aggregate connection selection refused")
  for (name, text) in sources do
    let path := System.FilePath.mk directory / (name.toString.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path text
    IO.println s!"generated {name}"
