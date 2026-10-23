import ZkcSecurity.Generation.SumcheckViews
import ZkcExamples.Construction.Generated.SmallSumcheckPair
import ZkcExamples.Construction.Generated.TwoSumsPair

namespace TestsSecurity.GenerateSumcheckViews
open Zkc.Construction ZkcSecurity.Generation.SumcheckViews

/-! Pair/module selection only. Input ABI, occurrence selection and the entire
source presentation are supplied by discovery and checked construction. -/

def selections : List (Participant × Participant × Output) :=
  [(ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant,
    ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant, "SmallSumcheck"),
   (ZkcExamples.Construction.Generated.TwoSumsPair.Producer.participant,
    ZkcExamples.Construction.Generated.TwoSumsPair.Validator.participant, "TwoSums")].map fun (producer, validator, name) =>
      (producer, validator, {
        moduleName := "ZkcSecurity.Examples.Generated.Components." ++ name ++ "ValidatorView"
        subjectModule := "ZkcSecurity.Examples.Generated." ++ name
        validatorModule := "ZkcExamples.Structured.Generated.Constructed." ++ name ++ "Validator"
        roundsModule := "ZkcSecurity.Examples.Generated.Components." ++ name ++ "Rounds" })

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for (producer, validator, output) in selections do
    let .ok text := source producer validator output | throw (IO.userError "view selection failed")
    let path := System.FilePath.mk directory /
      (output.moduleName.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path text
    IO.println s!"generated {output.moduleName}"

end TestsSecurity.GenerateSumcheckViews
