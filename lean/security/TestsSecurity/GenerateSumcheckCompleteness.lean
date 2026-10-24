import ZkcSecurity.Generation.SumcheckCompleteness.Command
import ZkcSecurity.Examples.Generated.SmallSumcheck
import ZkcSecurity.Examples.Generated.TwoSums
import ZkcExamples.Construction.Generated.SmallSumcheckPair
import ZkcExamples.Construction.Generated.TwoSumsPair

/-! Configuration supplies subject/pair identities, installed domain mathematics
and the selected formula proof. It supplies no arity, bound, capture, loop
occurrence, return projection, or root-specific proof script. -/
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace TestsSecurity.GenerateSumcheckCompleteness
open ZkcSecurity.Generation.SumcheckCompleteness

def output (name : String) : Output where
  moduleName := "ZkcSecurity.Examples.Generated.Components." ++ name ++ "Completeness"
  subjectModule := "ZkcSecurity.Examples.Generated." ++ name
  producerModule := "ZkcExamples.Structured.Generated.Constructed." ++ name ++ "Producer"
  validatorModule := "ZkcExamples.Structured.Generated.Constructed." ++ name ++ "Validator"
  roundsModule := "ZkcSecurity.Examples.Generated.Components." ++ name ++ "Rounds"
  validatorViewModule := "ZkcSecurity.Examples.Generated.Components." ++ name ++ "ValidatorView"
  abiModule := "ZkcSecurity.Examples.Generated.Components." ++ name ++ "ABI"
  mathematicsModule := "ZkcSecurity.Examples.Components." ++ name ++ "Formula"
  formulaLaw := "ZkcSecurity.Examples.Components." ++ name ++ ".Formula.equation"
  nonvacuityLaw := "ZkcSecurity.Examples.Components." ++ name ++ ".Formula.nonvacuous"
  fieldType := "ZMod blsModulus"
  groupType := "ZMod blsModulus"
  sampling := "rawSampleable blsModulus"

derive_sumcheck_completeness smallSource from {
  metadata := ZkcSecurity.Generation.SubjectABI.metadata ZkcSecurity.Examples.Generated.SmallSumcheck.subject
  producer := ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant
  validator := ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant
  output := output "SmallSumcheck" }

derive_sumcheck_completeness twoSource from {
  metadata := ZkcSecurity.Generation.SubjectABI.metadata ZkcSecurity.Examples.Generated.TwoSums.subject
  producer := ZkcExamples.Construction.Generated.TwoSumsPair.Producer.participant
  validator := ZkcExamples.Construction.Generated.TwoSumsPair.Validator.participant
  output := output "TwoSums" }

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for (name, text) in [("SmallSumcheck", smallSource), ("TwoSums", twoSource)] do
    let path := System.FilePath.mk directory /
      ((output name).moduleName.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path text
    IO.println s!"generated {(output name).moduleName}"

end TestsSecurity.GenerateSumcheckCompleteness
