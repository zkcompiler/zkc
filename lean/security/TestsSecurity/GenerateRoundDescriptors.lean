import ZkcSecurity.Generation.RoundDescriptors
import ZkcExamples.Construction.Generated.SmallSumcheckPair
import ZkcExamples.Construction.Generated.TwoSumsPair

namespace TestsSecurity.GenerateRoundDescriptors
open Zkc.Construction ZkcSecurity.Generation.RoundDescriptors

/-! Configuration is only actual pair/module selection. There are no selected
instruction indices, schema offsets, helper names, sites, or theorem scripts. -/
def selections : List (Participant × Participant × Output) :=
  [(ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant,
    ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant,
    "SmallSumcheck"),
   (ZkcExamples.Construction.Generated.TwoSumsPair.Producer.participant,
    ZkcExamples.Construction.Generated.TwoSumsPair.Validator.participant,
    "TwoSums")].map fun (producer, validator, name) =>
      (producer, validator, {
        moduleName := "ZkcSecurity.Examples.Generated.Components." ++ name ++ "Rounds"
        producerModule := "ZkcExamples.Structured.Generated.Constructed." ++ name ++ "Producer"
        validatorModule := "ZkcExamples.Structured.Generated.Constructed." ++ name ++ "Validator"
        contextModule := "ZkcSecurity.Examples.Generated." ++ name
        contextExpression := "ZkcSecurity.Examples.Generated." ++ name ++ ".subject.selection.context" })

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for (producer, validator, output) in selections do
    let .ok text := source producer validator output |
      throw (IO.userError s!"round descriptor recognition failed: {output.moduleName}")
    let path := System.FilePath.mk directory / (output.moduleName.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path text
    IO.println s!"generated {output.moduleName}"

end TestsSecurity.GenerateRoundDescriptors
