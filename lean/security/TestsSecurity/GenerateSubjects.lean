import ZkcTools.StructuredSource.Root

namespace TestsSecurity.GenerateSubjects

/-! Generate the two request-owned pair subjects. These descriptors choose the
model, retained target, honest-input policy and exact exported artifacts. They
contain no structural proof fields or mathematical/security proof scripts. -/

open ZkcTools.StructuredSource.Root

def descriptors : List FixedSubjectOutput := [
  { moduleName := "ZkcSecurity.Examples.Generated.SmallSumcheck"
    sourceModule := "ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs"
    originalExpression := "ZkcExamples.Structured.SumcheckSourceData.snapshot"
    importedExpression := "ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.imported"
    pairModule := "ZkcExamples.Construction.Generated.SmallSumcheckPair"
    artifactsExpression := "ZkcExamples.Construction.Generated.SmallSumcheckPair.artifacts"
    modelModule := "ZkcSecurity.Domains.PrimeField"
    modelExpression := "ZkcSecurity.Domains.PrimeField.blsScalarModel"
    targetName := "public_sum"
    inputPolicyExpression := "⟨[.cubeTable .here (.there (.there .here)) 1, .boundedIndex (.there (.there .here)) 2]⟩"
    originalExportExpression := "\"sha256:e3ae53d4706b17e7f5a468996a1dbf8cc57a06576986392388b288fffe1a99af\""
    producerExportExpression := "\"sha256:e9afef0c1e7775fed0f4d1abdf389d52495e5ae66efdf60a8a0394321461f7fa\""
    validatorExportExpression := "\"sha256:ea0efdd843435f477577106f7c7bcb9df6b2a19067491b95530c5cc154875bcd\""
    chargeSites := ["reduce.challenge"] },
  { moduleName := "ZkcSecurity.Examples.Generated.TwoSums"
    sourceModule := "ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs"
    originalExpression := "ZkcExamples.Structured.Generated.Bindings.TwoSumsData.snapshot"
    importedExpression := "ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.imported"
    pairModule := "ZkcExamples.Construction.Generated.TwoSumsPair"
    artifactsExpression := "ZkcExamples.Construction.Generated.TwoSumsPair.artifacts"
    modelModule := "ZkcSecurity.Domains.PrimeField"
    modelExpression := "ZkcSecurity.Domains.PrimeField.blsScalarModel"
    targetName := "public_sums"
    inputPolicyExpression := "⟨[.cubeTable .here (.there (.there (.there (.there .here)))) 1, .cubeTable (.there .here) (.there (.there (.there (.there .here)))) 1, .boundedIndex (.there (.there (.there (.there .here)))) 4]⟩"
    originalExportExpression := "\"sha256:ff5b4060dd0ad94db9061d59d7560152b8db7dc820b1d25f3b358433a6e78732\""
    producerExportExpression := "\"sha256:0bd526cfbc6d29aef756e4b0389d9fb6fe40d3ba76c557aab569266471957942\""
    validatorExportExpression := "\"sha256:f1110f3e53e1ab652a83adb2c5e4311a42961b4c21b4ed6c9ed6cbda3efe9fe0\""
    chargeSites := ["left.challenge", "right.challenge"] }]

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for descriptor in descriptors do
    let path := System.FilePath.mk directory /
      (descriptor.moduleName.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path (fixedSubjectSource descriptor)
    IO.println s!"generated {descriptor.moduleName}"

end TestsSecurity.GenerateSubjects
