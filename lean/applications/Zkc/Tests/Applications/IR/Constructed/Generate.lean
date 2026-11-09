import Zkc.Tools.IR.StructuredSource.Constructed
import Zkc.Applications.IR.Construction.Generated.SmallSumcheckPair
import Zkc.Applications.IR.Construction.Generated.TwoSumsPair
import Zkc.Applications.IR.Construction.Generated.GkrPair
import Zkc.Applications.IR.Construction.GkrProofParticipant
import Zkc.Applications.IR.Construction.SchnorrProofParticipant
import Zkc.Applications.IR.Construction.SchnorrAndProofParticipant
import Zkc.Applications.IR.Construction.ChaumPedersenProofParticipant
import Zkc.Applications.IR.Construction.OkamotoProofParticipant
import Zkc.Applications.IR.Construction.GuessProofParticipant
import Zkc.Applications.IR.Construction.BatchOpeningArtifacts
import Zkc.Applications.IR.Construction.EmbeddingEqualityParticipant

namespace Tests.Constructed.Generate

/-! Regenerate literal compositional views from the actual native artifacts.
This file supplies only module/artifact selections, with no protocol pipelines. -/
set_option autoImplicit false
open ZkcTools.StructuredSource.Constructed

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: Generate.lean OUTPUT_DIRECTORY")
  for (name, artifactModule, expression, artifact) in
      [("EmbeddingEqualityValidator", "Zkc.Applications.IR.Construction.EmbeddingEqualityParticipant",
          "ZkcExamples.Construction.EmbeddingEqualityParticipant.participant",
          ZkcExamples.Construction.EmbeddingEqualityParticipant.participant),
       ("GkrProducer", "Zkc.Applications.IR.Construction.Generated.GkrPair", "ZkcExamples.Construction.Generated.GkrPair.Producer.participant",
          ZkcExamples.Construction.Generated.GkrPair.Producer.participant),
       ("GkrValidator", "Zkc.Applications.IR.Construction.GkrProofParticipant", "ZkcExamples.Construction.GkrProofParticipant.participant",
          ZkcExamples.Construction.GkrProofParticipant.participant),
       ("SmallSumcheckProducer", "Zkc.Applications.IR.Construction.Generated.SmallSumcheckPair", "ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant",
          ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant),
       ("SmallSumcheckValidator", "Zkc.Applications.IR.Construction.Generated.SmallSumcheckPair", "ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant",
          ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant),
       ("TwoSumsProducer", "Zkc.Applications.IR.Construction.Generated.TwoSumsPair", "ZkcExamples.Construction.Generated.TwoSumsPair.Producer.participant",
          ZkcExamples.Construction.Generated.TwoSumsPair.Producer.participant),
       ("TwoSumsValidator", "Zkc.Applications.IR.Construction.Generated.TwoSumsPair", "ZkcExamples.Construction.Generated.TwoSumsPair.Validator.participant",
          ZkcExamples.Construction.Generated.TwoSumsPair.Validator.participant),
       ("SchnorrValidator", "Zkc.Applications.IR.Construction.SchnorrProofParticipant", "ZkcExamples.Construction.SchnorrProofParticipant.participant",
          ZkcExamples.Construction.SchnorrProofParticipant.participant),
       ("SchnorrAndValidator", "Zkc.Applications.IR.Construction.SchnorrAndProofParticipant", "ZkcExamples.Construction.SchnorrAndProofParticipant.participant",
          ZkcExamples.Construction.SchnorrAndProofParticipant.participant),
       ("ChaumPedersenValidator", "Zkc.Applications.IR.Construction.ChaumPedersenProofParticipant", "ZkcExamples.Construction.ChaumPedersenProofParticipant.participant",
          ZkcExamples.Construction.ChaumPedersenProofParticipant.participant),
       ("OkamotoValidator", "Zkc.Applications.IR.Construction.OkamotoProofParticipant", "ZkcExamples.Construction.OkamotoProofParticipant.participant",
          ZkcExamples.Construction.OkamotoProofParticipant.participant),
       ("GuessValidator", "Zkc.Applications.IR.Construction.GuessProofParticipant", "ZkcExamples.Construction.GuessProofParticipant.participant",
          ZkcExamples.Construction.GuessProofParticipant.participant),
       ("BatchOpeningProducer", "Zkc.Applications.IR.Construction.BatchOpeningArtifacts", "ZkcExamples.Construction.BatchOpeningArtifacts.Producer.participant",
          ZkcExamples.Construction.BatchOpeningArtifacts.Producer.participant),
       ("BatchOpeningValidator", "Zkc.Applications.IR.Construction.BatchOpeningArtifacts", "ZkcExamples.Construction.BatchOpeningArtifacts.Validator.participant",
          ZkcExamples.Construction.BatchOpeningArtifacts.Validator.participant)] do
    let output : Output := {
      moduleName := "Zkc.Applications.IR.Structured.Generated.Constructed." ++ name
      namespaceName := "ZkcExamples.Structured.Generated.Constructed." ++ name
      artifactModule, artifactExpression := expression }
    match source artifact output with
    | .error error => throw (IO.userError error)
    | .ok text =>
      let .ok relocated := source artifact { output with moduleName := "Relocated." ++ output.moduleName }
        | throw (IO.userError "constructed-module-relocation-refused")
      unless text == relocated do
        throw (IO.userError "constructed-module-relocation-changed-declarations")
      IO.FS.writeFile (System.FilePath.mk directory / (name ++ ".lean")) text

end Tests.Constructed.Generate
