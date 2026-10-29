import ZkcTools.ConstructionBindings.Generate

/-! Data-only selections for the common connection printer. The declarations
named here are checked when the generated modules are compiled. -/
set_option autoImplicit false
namespace Tests.ConnectionGeneration
open Lean ZkcTools.ConstructionBindings.Generate

/-- Fixture pairs share the generated input, artifact and view naming scheme.
These names select declarations; the generated kernel proof checks their meaning. -/
def pairedSelection (stem : String) : Selection × Output :=
  let inputs := Name.str `ZkcExamples.Structured.Generated.Bindings (stem ++ "Inputs")
  let artifacts := Name.str `ZkcExamples.Construction.Generated (stem ++ "Pair")
  (⟨inputs, inputs ++ `program⟩,
    ⟨Name.str `ZkcExamples.Structured.Generated.Connections stem, [
      ⟨.producer, artifacts, artifacts ++ `Producer.participant,
        Name.str `ZkcExamples.Structured.Generated.Constructed (stem ++ "Producer")⟩,
      ⟨.validator, artifacts, artifacts ++ `Validator.participant,
        Name.str `ZkcExamples.Structured.Generated.Constructed (stem ++ "Validator")⟩]⟩)

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
        `ZkcExamples.Structured.Generated.Constructed.GuessValidator⟩]⟩)
] ++ ["SmallSumcheck", "TwoSums", "SchnorrRandomized", "SchnorrAndRandomized",
  "SchnorrAndAliased", "SequentialSigma", "SampledAbort"].map pairedSelection

#guard (selections.map fun entry => entry.2.moduleName).eraseDups.length == selections.length

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
