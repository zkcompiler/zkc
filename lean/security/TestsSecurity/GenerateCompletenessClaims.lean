import ZkcTools.StructuredSource.Bindings.Subject

namespace TestsSecurity.GenerateCompletenessClaims

/-! Select existing closed subjects and proved endpoint theorems. The printer
supplies uniform structural/receipt assembly for each descriptor. -/
open ZkcTools.StructuredSource.Bindings

def descriptors : List FixedCompletenessOutput :=
  ["SmallSumcheck", "TwoSums"].map fun name => {
    moduleName := "ZkcSecurity.Examples.Generated." ++ name ++ "CompletenessClaims"
    subjectModule := "ZkcSecurity.Examples.Generated." ++ name
    subjectNamespace := "ZkcSecurity.Examples.Generated." ++ name
    proofModule := "ZkcSecurity.Examples.Components." ++ name ++ "Completeness"
    proofName := "ZkcSecurity.Examples.Components." ++ name ++ ".compiled_ideal_complete"
    capabilitiesExpression := "ZkcSecurity.Domains.PrimeField.blsCapabilities original (by decide +kernel)" }

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for descriptor in descriptors do
    let path := System.FilePath.mk directory /
      (descriptor.moduleName.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path (fixedCompletenessSource descriptor)
    IO.println s!"generated {descriptor.moduleName}"

end TestsSecurity.GenerateCompletenessClaims
