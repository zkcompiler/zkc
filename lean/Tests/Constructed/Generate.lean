import ZkcTools.StructuredSource.Constructed
import ZkcExamples.Construction.Generated.SmallSumcheckPair
import ZkcExamples.Construction.Generated.TwoSumsPair

namespace Tests.Constructed.Generate

/-! Regenerate literal compositional views from the actual native artifacts.
This file supplies only module/artifact selections, with no protocol pipelines. -/
set_option autoImplicit false
open ZkcTools.StructuredSource.Constructed

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: Generate.lean OUTPUT_DIRECTORY")
  for (name, artifactModule, expression, artifact) in
      [("SmallSumcheckProducer", "ZkcExamples.Construction.Generated.SmallSumcheckPair", "ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant",
          ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant),
       ("SmallSumcheckValidator", "ZkcExamples.Construction.Generated.SmallSumcheckPair", "ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant",
          ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant),
       ("TwoSumsProducer", "ZkcExamples.Construction.Generated.TwoSumsPair", "ZkcExamples.Construction.Generated.TwoSumsPair.Producer.participant",
          ZkcExamples.Construction.Generated.TwoSumsPair.Producer.participant),
       ("TwoSumsValidator", "ZkcExamples.Construction.Generated.TwoSumsPair", "ZkcExamples.Construction.Generated.TwoSumsPair.Validator.participant",
          ZkcExamples.Construction.Generated.TwoSumsPair.Validator.participant)] do
    let output : Output := ⟨"ZkcExamples.Structured.Generated.Constructed." ++ name,
      artifactModule, expression⟩
    match source artifact output with
    | .error error => throw (IO.userError error)
    | .ok text => IO.FS.writeFile (System.FilePath.mk directory / (name ++ ".lean")) text

end Tests.Constructed.Generate
