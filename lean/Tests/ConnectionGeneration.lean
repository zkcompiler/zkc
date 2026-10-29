import ZkcTools.ConstructionBindings.Generate

/-! Data-only selections for the common connection printer. The declarations
named here are checked when the generated modules are compiled. -/
set_option autoImplicit false
namespace Tests.ConnectionGeneration
open Lean ZkcTools.ConstructionBindings.Generate

def selections : List (Selection × Output) := [
  (⟨`ZkcExamples.Construction.EmbeddingEqualityBinding, `ZkcExamples.Construction.EmbeddingEqualityBinding.program⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.EmbeddingEquality, [
      ⟨.validator, `ZkcExamples.Construction.EmbeddingEqualityParticipant,
        `ZkcExamples.Construction.EmbeddingEqualityParticipant.participant,
        `ZkcExamples.Structured.Generated.Constructed.EmbeddingEqualityValidator⟩]⟩),
  (⟨`ZkcExamples.Structured.GkrSourceViews, `ZkcExamples.Structured.GkrSourceViews.program⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.Gkr, [
      ⟨.producer, `ZkcExamples.Construction.Generated.GkrPair,
        `ZkcExamples.Construction.Generated.GkrPair.Producer.participant,
        `ZkcExamples.Structured.Generated.Constructed.GkrProducer⟩,
      ⟨.validator, `ZkcExamples.Construction.GkrProofParticipant,
        `ZkcExamples.Construction.GkrProofParticipant.participant,
        `ZkcExamples.Structured.Generated.Constructed.GkrValidator⟩]⟩),
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
  (⟨`ZkcExamples.Construction.SchnorrArtifact, `ZkcExamples.Construction.SchnorrProof.program⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.Schnorr, [
      ⟨.validator, `ZkcExamples.Construction.SchnorrProofParticipant,
        `ZkcExamples.Construction.SchnorrProofParticipant.participant,
        `ZkcExamples.Structured.Generated.Constructed.SchnorrValidator⟩]⟩),
  (⟨`ZkcExamples.Construction.SchnorrAndArtifact, `ZkcExamples.Construction.SchnorrAndProof.program⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.SchnorrAnd, [
      ⟨.validator, `ZkcExamples.Construction.SchnorrAndProofParticipant,
        `ZkcExamples.Construction.SchnorrAndProofParticipant.participant,
        `ZkcExamples.Structured.Generated.Constructed.SchnorrAndValidator⟩]⟩),
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
  (⟨`ZkcExamples.Construction.GuessArtifact, `ZkcExamples.Construction.GuessProof.program⟩,
    ⟨`ZkcExamples.Structured.Generated.Connections.Guess, [
      ⟨.validator, `ZkcExamples.Construction.GuessProofParticipant,
        `ZkcExamples.Construction.GuessProofParticipant.participant,
        `ZkcExamples.Structured.Generated.Constructed.GuessValidator⟩]⟩),
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

-- Namespace choice affects spelling only. Every retained selection uses the
-- same generic certificate and fixed semantic connection, with no proof hole.
#guard selections.all fun (selection, output) =>
  match source selection output,
      source selection { output with moduleName := `Renamed ++ output.moduleName } with
  | .ok original, .ok renamed =>
      original.replace output.moduleName.toString ("Renamed." ++ output.moduleName.toString) == renamed &&
      original.contains "derive_root_connection_with_library" &&
      original.contains "SourceConnection.ofRootCertificate" &&
      !original.contains "sorry" && !original.contains "\n  admit" &&
      !original.contains "native_decide"
  | _, _ => false

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  write directory selections

end Tests.ConnectionGeneration
