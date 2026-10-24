import ZkcSecurity.Generation.SumcheckSoundness.Command
import ZkcSecurity.Examples.Generated.SmallSumcheck
import ZkcSecurity.Examples.Generated.TwoSums
import ZkcExamples.Construction.Generated.SmallSumcheckPair
import ZkcExamples.Construction.Generated.TwoSumsPair

/-! Configuration supplies subject/pair identities, installed domain mathematics
and the selected formula evaluation proof. It supplies no arity, bound, capture, loop
occurrence, return projection, or root-specific proof script. -/
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace TestsSecurity.GenerateSumcheckSoundness
open ZkcSecurity.Generation.SumcheckSoundness

def output (name : String) : Output where
  moduleName := "ZkcSecurity.Examples.Generated.Components." ++ name ++ "Soundness"
  subjectModule := "ZkcSecurity.Examples.Generated." ++ name
  roundsModule := "ZkcSecurity.Examples.Generated.Components." ++ name ++ "Rounds"
  validatorViewModule := "ZkcSecurity.Examples.Generated.Components." ++ name ++ "ValidatorView"
  abiModule := "ZkcSecurity.Examples.Generated.Components." ++ name ++ "ABI"
  mathematicsModule := "ZkcSecurity.Examples.Components." ++ name ++ "Formula"
  formulaLaw := "ZkcSecurity.Examples.Components." ++ name ++ ".Formula.equation"
  modulus := "blsModulus"
  capabilities := "blsCapabilities original (by decide +kernel)"
  fieldType := "ZMod blsModulus"
  groupType := "ZMod blsModulus"
  sampling := "rawSampleable blsModulus"

derive_sumcheck_soundness smallSource from {
  metadata := ZkcSecurity.Generation.SubjectABI.metadata ZkcSecurity.Examples.Generated.SmallSumcheck.subject
  producer := ZkcExamples.Construction.Generated.SmallSumcheckPair.Producer.participant
  validator := ZkcExamples.Construction.Generated.SmallSumcheckPair.Validator.participant
  output := output "SmallSumcheck" }

derive_sumcheck_soundness twoSource from {
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

end TestsSecurity.GenerateSumcheckSoundness
