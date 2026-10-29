import ZkcTools.StructuredSource.Constructed
import ZkcExamples.Construction.Generated.SmallSumcheckPair
import ZkcExamples.Construction.Generated.TwoSumsPair
import ZkcExamples.Construction.Generated.GkrPair
import ZkcExamples.Construction.GkrProofParticipant
import ZkcExamples.Construction.SchnorrProofParticipant
import ZkcExamples.Construction.SchnorrAndProofParticipant
import ZkcExamples.Construction.ChaumPedersenProofParticipant
import ZkcExamples.Construction.OkamotoProofParticipant
import ZkcExamples.Construction.GuessProofParticipant
import ZkcExamples.Construction.BatchOpeningArtifacts
import ZkcExamples.Construction.EmbeddingEqualityParticipant

namespace Tests.Constructed.Generate

/-! Regenerate literal compositional views from the actual native artifacts.
This file supplies only module/artifact selections, with no protocol pipelines. -/
set_option autoImplicit false
open ZkcTools.StructuredSource.Constructed

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: Generate.lean OUTPUT_DIRECTORY")
  for (name, artifactModule, expression, artifact) in
      [("EmbeddingEqualityValidator", "ZkcExamples.Construction.EmbeddingEqualityParticipant",
          "ZkcExamples.Construction.EmbeddingEqualityParticipant.participant",
          ZkcExamples.Construction.EmbeddingEqualityParticipant.participant),
       ("GkrProducer", "ZkcExamples.Construction.Generated.GkrPair", "ZkcExamples.Construction.Generated.GkrPair.Producer.participant",
          ZkcExamples.Construction.Generated.GkrPair.Producer.participant),
       ("GkrValidator", "ZkcExamples.Construction.GkrProofParticipant", "ZkcExamples.Construction.GkrProofParticipant.participant",
          ZkcExamples.Construction.GkrProofParticipant.participant),
       ("SmallSumcheckProducer", "ZkcExamples.Construction.Generated.SmallSumcheckPair", "ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant",
          ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant),
       ("SmallSumcheckValidator", "ZkcExamples.Construction.Generated.SmallSumcheckPair", "ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant",
          ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant),
       ("TwoSumsProducer", "ZkcExamples.Construction.Generated.TwoSumsPair", "ZkcExamples.Construction.Generated.TwoSumsPair.Producer.participant",
          ZkcExamples.Construction.Generated.TwoSumsPair.Producer.participant),
       ("TwoSumsValidator", "ZkcExamples.Construction.Generated.TwoSumsPair", "ZkcExamples.Construction.Generated.TwoSumsPair.Validator.participant",
          ZkcExamples.Construction.Generated.TwoSumsPair.Validator.participant),
       ("SchnorrValidator", "ZkcExamples.Construction.SchnorrProofParticipant", "ZkcExamples.Construction.SchnorrProofParticipant.participant",
          ZkcExamples.Construction.SchnorrProofParticipant.participant),
       ("SchnorrAndValidator", "ZkcExamples.Construction.SchnorrAndProofParticipant", "ZkcExamples.Construction.SchnorrAndProofParticipant.participant",
          ZkcExamples.Construction.SchnorrAndProofParticipant.participant),
       ("ChaumPedersenValidator", "ZkcExamples.Construction.ChaumPedersenProofParticipant", "ZkcExamples.Construction.ChaumPedersenProofParticipant.participant",
          ZkcExamples.Construction.ChaumPedersenProofParticipant.participant),
       ("OkamotoValidator", "ZkcExamples.Construction.OkamotoProofParticipant", "ZkcExamples.Construction.OkamotoProofParticipant.participant",
          ZkcExamples.Construction.OkamotoProofParticipant.participant),
       ("GuessValidator", "ZkcExamples.Construction.GuessProofParticipant", "ZkcExamples.Construction.GuessProofParticipant.participant",
          ZkcExamples.Construction.GuessProofParticipant.participant),
       ("BatchOpeningProducer", "ZkcExamples.Construction.BatchOpeningArtifacts", "ZkcExamples.Construction.BatchOpeningArtifacts.Producer.participant",
          ZkcExamples.Construction.BatchOpeningArtifacts.Producer.participant),
       ("BatchOpeningValidator", "ZkcExamples.Construction.BatchOpeningArtifacts", "ZkcExamples.Construction.BatchOpeningArtifacts.Validator.participant",
          ZkcExamples.Construction.BatchOpeningArtifacts.Validator.participant)] do
    let output : Output := ⟨"ZkcExamples.Structured.Generated.Constructed." ++ name,
      artifactModule, expression⟩
    match source artifact output with
    | .error error => throw (IO.userError error)
    | .ok text => IO.FS.writeFile (System.FilePath.mk directory / (name ++ ".lean")) text

end Tests.Constructed.Generate
