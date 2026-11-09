import Zkc.Tools.IR.ConstructionBindings.Generate

/-! Data-only selections for the common connection printer. The declarations
named here are checked when the generated modules are compiled. -/
set_option autoImplicit false
namespace Tests.ConnectionGeneration
open Lean ZkcTools.ConstructionBindings.Generate

/-- Fixture pairs share the generated input, artifact and view naming scheme.
These names select declarations; the generated kernel proof checks their meaning. -/
def pairedSelection (stem : String) : Selection × Output :=
  let inputsModule := Name.str `Zkc.Applications.IR.Structured.Generated.Bindings (stem ++ "Inputs")
  let inputsNamespace := Name.str `ZkcExamples.Structured.Generated.Bindings (stem ++ "Inputs")
  let artifactModule := Name.str `Zkc.Applications.IR.Construction.Generated (stem ++ "Pair")
  let artifactNamespace := Name.str `ZkcExamples.Construction.Generated (stem ++ "Pair")
  (⟨inputsModule, inputsNamespace ++ `program⟩,
    { moduleName := Name.str `Zkc.Applications.IR.Structured.Generated.Connections stem
      namespaceName := Name.str `ZkcExamples.Structured.Generated.Connections stem
      participants := [
        { mode := .producer, artifactModule, artifact := artifactNamespace ++ `Producer.participant
          viewModule := Name.str `Zkc.Applications.IR.Structured.Generated.Constructed (stem ++ "Producer")
          viewNamespace := Name.str `ZkcExamples.Structured.Generated.Constructed (stem ++ "Producer") },
        { mode := .validator, artifactModule, artifact := artifactNamespace ++ `Validator.participant
          viewModule := Name.str `Zkc.Applications.IR.Structured.Generated.Constructed (stem ++ "Validator")
          viewNamespace := Name.str `ZkcExamples.Structured.Generated.Constructed (stem ++ "Validator") }] })

def selections : List (Selection × Output) := [
  (⟨`Zkc.Applications.IR.Construction.EmbeddingEqualityBinding, `ZkcExamples.Construction.EmbeddingEqualityBinding.program⟩,
    { moduleName := `Zkc.Applications.IR.Structured.Generated.Connections.EmbeddingEquality
      namespaceName := `ZkcExamples.Structured.Generated.Connections.EmbeddingEquality
      participants := [
      { mode := .validator, artifactModule := `Zkc.Applications.IR.Construction.EmbeddingEqualityParticipant
        artifact := `ZkcExamples.Construction.EmbeddingEqualityParticipant.participant
        viewModule := `Zkc.Applications.IR.Structured.Generated.Constructed.EmbeddingEqualityValidator
        viewNamespace := `ZkcExamples.Structured.Generated.Constructed.EmbeddingEqualityValidator }] }),
  (⟨`Zkc.Applications.IR.Structured.GkrSourceViews, `ZkcExamples.Structured.GkrSourceViews.program⟩,
    { moduleName := `Zkc.Applications.IR.Structured.Generated.Connections.Gkr
      namespaceName := `ZkcExamples.Structured.Generated.Connections.Gkr
      participants := [
      { mode := .producer, artifactModule := `Zkc.Applications.IR.Construction.Generated.GkrPair
        artifact := `ZkcExamples.Construction.Generated.GkrPair.Producer.participant
        viewModule := `Zkc.Applications.IR.Structured.Generated.Constructed.GkrProducer
        viewNamespace := `ZkcExamples.Structured.Generated.Constructed.GkrProducer },
      { mode := .validator, artifactModule := `Zkc.Applications.IR.Construction.GkrProofParticipant
        artifact := `ZkcExamples.Construction.GkrProofParticipant.participant
        viewModule := `Zkc.Applications.IR.Structured.Generated.Constructed.GkrValidator
        viewNamespace := `ZkcExamples.Structured.Generated.Constructed.GkrValidator }] }),
  (⟨`Zkc.Applications.IR.Construction.BatchOpening, `ZkcExamples.Construction.BatchOpening.program⟩,
    { moduleName := `Zkc.Applications.IR.Structured.Generated.Connections.BatchOpening
      namespaceName := `ZkcExamples.Structured.Generated.Connections.BatchOpening
      participants := [
      { mode := .producer, artifactModule := `Zkc.Applications.IR.Construction.BatchOpeningArtifacts
        artifact := `ZkcExamples.Construction.BatchOpeningArtifacts.Producer.participant
        viewModule := `Zkc.Applications.IR.Structured.Generated.Constructed.BatchOpeningProducer
        viewNamespace := `ZkcExamples.Structured.Generated.Constructed.BatchOpeningProducer },
      { mode := .validator, artifactModule := `Zkc.Applications.IR.Construction.BatchOpeningArtifacts
        artifact := `ZkcExamples.Construction.BatchOpeningArtifacts.Validator.participant
        viewModule := `Zkc.Applications.IR.Structured.Generated.Constructed.BatchOpeningValidator
        viewNamespace := `ZkcExamples.Structured.Generated.Constructed.BatchOpeningValidator }] }),
  (⟨`Zkc.Applications.IR.Construction.SchnorrArtifact, `ZkcExamples.Construction.SchnorrProof.program⟩,
    { moduleName := `Zkc.Applications.IR.Structured.Generated.Connections.Schnorr
      namespaceName := `ZkcExamples.Structured.Generated.Connections.Schnorr
      participants := [
      { mode := .validator, artifactModule := `Zkc.Applications.IR.Construction.SchnorrProofParticipant
        artifact := `ZkcExamples.Construction.SchnorrProofParticipant.participant
        viewModule := `Zkc.Applications.IR.Structured.Generated.Constructed.SchnorrValidator
        viewNamespace := `ZkcExamples.Structured.Generated.Constructed.SchnorrValidator }] }),
  (⟨`Zkc.Applications.IR.Construction.SchnorrAndArtifact, `ZkcExamples.Construction.SchnorrAndProof.program⟩,
    { moduleName := `Zkc.Applications.IR.Structured.Generated.Connections.SchnorrAnd
      namespaceName := `ZkcExamples.Structured.Generated.Connections.SchnorrAnd
      participants := [
      { mode := .validator, artifactModule := `Zkc.Applications.IR.Construction.SchnorrAndProofParticipant
        artifact := `ZkcExamples.Construction.SchnorrAndProofParticipant.participant
        viewModule := `Zkc.Applications.IR.Structured.Generated.Constructed.SchnorrAndValidator
        viewNamespace := `ZkcExamples.Structured.Generated.Constructed.SchnorrAndValidator }] }),
  (⟨`Zkc.Applications.IR.Construction.ChaumPedersenArtifact, `ZkcExamples.Construction.ChaumPedersenProof.program⟩,
    { moduleName := `Zkc.Applications.IR.Structured.Generated.Connections.ChaumPedersen
      namespaceName := `ZkcExamples.Structured.Generated.Connections.ChaumPedersen
      participants := [
      { mode := .validator, artifactModule := `Zkc.Applications.IR.Construction.ChaumPedersenProofParticipant
        artifact := `ZkcExamples.Construction.ChaumPedersenProofParticipant.participant
        viewModule := `Zkc.Applications.IR.Structured.Generated.Constructed.ChaumPedersenValidator
        viewNamespace := `ZkcExamples.Structured.Generated.Constructed.ChaumPedersenValidator }] }),
  (⟨`Zkc.Applications.IR.Construction.OkamotoArtifact, `ZkcExamples.Construction.OkamotoProof.program⟩,
    { moduleName := `Zkc.Applications.IR.Structured.Generated.Connections.Okamoto
      namespaceName := `ZkcExamples.Structured.Generated.Connections.Okamoto
      participants := [
      { mode := .validator, artifactModule := `Zkc.Applications.IR.Construction.OkamotoProofParticipant
        artifact := `ZkcExamples.Construction.OkamotoProofParticipant.participant
        viewModule := `Zkc.Applications.IR.Structured.Generated.Constructed.OkamotoValidator
        viewNamespace := `ZkcExamples.Structured.Generated.Constructed.OkamotoValidator }] }),
  (⟨`Zkc.Applications.IR.Construction.GuessArtifact, `ZkcExamples.Construction.GuessProof.program⟩,
    { moduleName := `Zkc.Applications.IR.Structured.Generated.Connections.Guess
      namespaceName := `ZkcExamples.Structured.Generated.Connections.Guess
      participants := [
      { mode := .validator, artifactModule := `Zkc.Applications.IR.Construction.GuessProofParticipant
        artifact := `ZkcExamples.Construction.GuessProofParticipant.participant
        viewModule := `Zkc.Applications.IR.Structured.Generated.Constructed.GuessValidator
        viewNamespace := `ZkcExamples.Structured.Generated.Constructed.GuessValidator }] })
] ++ ["SmallSumcheck", "TwoSums", "SchnorrRandomized", "SchnorrAndRandomized",
  "SchnorrAndAliased", "SequentialSigma", "SampledAbort"].map pairedSelection

#guard (selections.map fun entry => entry.2.moduleName).eraseDups.length == selections.length

-- Context discovery has one source of authority and never inserts a default.
#guard source ⟨`Source, `Source.program⟩ { moduleName := `Output, participants := [] } == .error "connection-output-empty"
#guard source ⟨`Source, `Source.program⟩ { moduleName := `Output, participants := [
    { mode := .producer, artifactModule := `Artifact, artifact := `Artifact.participant, viewModule := `View }] } ==
    .error "connection-validator-context-required"
#guard source ⟨`Source, `Source.program⟩ { moduleName := `Output, participants := [
    { mode := .validator, artifactModule := `Artifact, artifact := `Artifact.participant, viewModule := `View },
    { mode := .validator, artifactModule := `Artifact, artifact := `Artifact.participant, viewModule := `View }] } ==
    .error "connection-output-duplicate-role"

-- Module identity changes file placement, while declaration namespaces stay fixed.
#guard selections.all fun (selection, output) =>
  match source selection output,
      source selection { output with moduleName := `Relocated ++ output.moduleName } with
  | .ok original, .ok relocated =>
      original == relocated &&
      original.contains "derive_root_connection_with_library" &&
      original.contains "set_option zkc.connection.generateReusableBodies true" &&
      original.contains "set_option zkc.connection.requireReusableBodies true" &&
      original.contains "SourceConnection.ofRootCertificate" &&
      !original.contains "sorry" && !original.contains "\n  admit" &&
      !original.contains "native_decide"
  | _, _ => false

-- Namespace changes affect declaration spelling independently of module imports.
#guard selections.all fun (selection, output) =>
  match source selection output,
      source selection { output with namespaceName := `Renamed ++ output.namespaceName } with
  | .ok original, .ok renamed =>
      original.replace output.namespaceName.toString ("Renamed." ++ output.namespaceName.toString) == renamed
  | _, _ => false

-- Relocating a view import preserves its artifact and correspondence expressions.
#guard selections.all fun (selection, output) =>
  let relocated : Output := { output with participants := output.participants.map fun participant =>
    { participant with viewModule := `Relocated ++ participant.viewModule } }
  match source selection output, source selection relocated with
  | .ok original, .ok moved =>
      output.participants.foldl (fun text participant => text.replace
        ("public import " ++ participant.viewModule.toString ++ "\n")
        ("public import Relocated." ++ participant.viewModule.toString ++ "\n")) original == moved
  | _, _ => false

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  write directory selections

end Tests.ConnectionGeneration
