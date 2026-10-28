import ZkcTools.ConstructionBindings.Generate

/-! Data-only selections for the common connection printer. The declarations
named here are checked when the generated modules are compiled. -/
set_option autoImplicit false
namespace Tests.ConnectionGeneration
open Lean ZkcTools.ConstructionBindings.Generate

def selections : List (Selection × Output) := [
  (⟨`ZkcExamples.Construction.BatchOpening, `ZkcExamples.Construction.BatchOpening.program,
      `ZkcExamples.Construction.BatchOpening.context⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.BatchOpening, [
      ⟨.producer, `ZkcExamples.Construction.BatchOpeningArtifacts,
        `ZkcExamples.Construction.BatchOpeningArtifacts.Producer.participant,
        `ZkcExamples.Structured.Generated.Constructed.BatchOpeningProducer⟩,
      ⟨.validator, `ZkcExamples.Construction.BatchOpeningArtifacts,
        `ZkcExamples.Construction.BatchOpeningArtifacts.Validator.participant,
        `ZkcExamples.Structured.Generated.Constructed.BatchOpeningValidator⟩]⟩),
  (⟨`ZkcExamples.Construction.SchnorrArtifact, `ZkcExamples.Construction.SchnorrProof.program,
      `ZkcExamples.Construction.SchnorrProof.context⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.SchnorrRandomized, [
      ⟨.producer, `ZkcExamples.Construction.Generated.SchnorrRandomizedPair,
        `ZkcExamples.Construction.Generated.SchnorrRandomizedPair.Producer.participant,
        `ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedProducer⟩,
      ⟨.validator, `ZkcExamples.Construction.Generated.SchnorrRandomizedPair,
        `ZkcExamples.Construction.Generated.SchnorrRandomizedPair.Validator.participant,
        `ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator⟩]⟩),
  (⟨`ZkcExamples.Construction.ChaumPedersenArtifact, `ZkcExamples.Construction.ChaumPedersenProof.program,
      `ZkcExamples.Construction.ChaumPedersenProof.context⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.ChaumPedersen, [
      ⟨.validator, `ZkcExamples.Construction.ChaumPedersenProofParticipant,
        `ZkcExamples.Construction.ChaumPedersenProofParticipant.participant,
        `ZkcExamples.Structured.Generated.Constructed.ChaumPedersenValidator⟩]⟩),
  (⟨`ZkcExamples.Construction.OkamotoArtifact, `ZkcExamples.Construction.OkamotoProof.program,
      `ZkcExamples.Construction.OkamotoProof.context⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.Okamoto, [
      ⟨.validator, `ZkcExamples.Construction.OkamotoProofParticipant,
        `ZkcExamples.Construction.OkamotoProofParticipant.participant,
        `ZkcExamples.Structured.Generated.Constructed.OkamotoValidator⟩]⟩)]

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for (selection, output) in selections do
    let .ok text := source selection output | throw (IO.userError "connection selection refused")
    let path := System.FilePath.mk directory / (output.moduleName.toString.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path text

end Tests.ConnectionGeneration
