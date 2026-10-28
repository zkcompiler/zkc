import ZkcTools.ConstructionBindings.Generate

/-! Data-only selections for the common connection printer. The declarations
named here are checked when the generated modules are compiled. -/
set_option autoImplicit false
namespace Tests.ConnectionGeneration
open Lean ZkcTools.ConstructionBindings.Generate

def selections : List (Selection × Output) := [
  (⟨`ZkcExamples.Construction.BatchOpening, `ZkcExamples.Construction.BatchOpening.program⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.BatchOpening, [
      ⟨.producer, `ZkcExamples.Construction.BatchOpeningArtifacts,
        `ZkcExamples.Construction.BatchOpeningArtifacts.Producer.participant,
        `ZkcExamples.Structured.Generated.Constructed.BatchOpeningProducer⟩,
      ⟨.validator, `ZkcExamples.Construction.BatchOpeningArtifacts,
        `ZkcExamples.Construction.BatchOpeningArtifacts.Validator.participant,
        `ZkcExamples.Structured.Generated.Constructed.BatchOpeningValidator⟩]⟩),
  (⟨`ZkcExamples.Construction.SchnorrArtifact, `ZkcExamples.Construction.SchnorrProof.program⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.SchnorrRandomized, [
      ⟨.producer, `ZkcExamples.Construction.Generated.SchnorrRandomizedPair,
        `ZkcExamples.Construction.Generated.SchnorrRandomizedPair.Producer.participant,
        `ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedProducer⟩,
      ⟨.validator, `ZkcExamples.Construction.Generated.SchnorrRandomizedPair,
        `ZkcExamples.Construction.Generated.SchnorrRandomizedPair.Validator.participant,
        `ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator⟩]⟩),
  (⟨`ZkcExamples.Construction.ChaumPedersenArtifact, `ZkcExamples.Construction.ChaumPedersenProof.program⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.ChaumPedersen, [
      ⟨.validator, `ZkcExamples.Construction.ChaumPedersenProofParticipant,
        `ZkcExamples.Construction.ChaumPedersenProofParticipant.participant,
        `ZkcExamples.Structured.Generated.Constructed.ChaumPedersenValidator⟩]⟩),
  (⟨`ZkcExamples.Construction.OkamotoArtifact, `ZkcExamples.Construction.OkamotoProof.program⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.Okamoto, [
      ⟨.validator, `ZkcExamples.Construction.OkamotoProofParticipant,
        `ZkcExamples.Construction.OkamotoProofParticipant.participant,
        `ZkcExamples.Structured.Generated.Constructed.OkamotoValidator⟩]⟩),
  (⟨`ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs,
      `ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.program⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.SmallSumcheck, [
      ⟨.producer, `ZkcExamples.Construction.Generated.SmallSumcheckPair,
        `ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant,
        `ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer⟩,
      ⟨.validator, `ZkcExamples.Construction.Generated.SmallSumcheckPair,
        `ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant,
        `ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator⟩]⟩),
  (⟨`ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs,
      `ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.program⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.TwoSums, [
      ⟨.producer, `ZkcExamples.Construction.Generated.TwoSumsPair,
        `ZkcExamples.Construction.Generated.TwoSumsPair.Producer.participant,
        `ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer⟩,
      ⟨.validator, `ZkcExamples.Construction.Generated.TwoSumsPair,
        `ZkcExamples.Construction.Generated.TwoSumsPair.Validator.participant,
        `ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator⟩]⟩)]

-- Context discovery has one source of authority and never inserts a default.
#guard source ⟨`Source, `Source.program⟩ ⟨`Output, []⟩ == .error "connection-output-empty"
#guard source ⟨`Source, `Source.program⟩ ⟨`Output,
  [⟨.producer, `Artifact, `Artifact.participant, `View⟩]⟩ ==
    .error "connection-validator-context-required"
#guard source ⟨`Source, `Source.program⟩ ⟨`Output,
  [⟨.validator, `Artifact, `Artifact.participant, `View⟩,
   ⟨.validator, `Artifact, `Artifact.participant, `View⟩]⟩ ==
    .error "connection-output-duplicate-role"

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for (selection, output) in selections do
    let .ok text := source selection output | throw (IO.userError "connection selection refused")
    let path := System.FilePath.mk directory / (output.moduleName.toString.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path text

end Tests.ConnectionGeneration
