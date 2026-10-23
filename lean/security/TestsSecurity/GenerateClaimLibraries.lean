import ZkcTools.StructuredSource.Bindings.Subject

namespace TestsSecurity.GenerateClaimLibraries
open ZkcTools.StructuredSource.Bindings

/-! Protocol choices are source subject and installed theorem exports. No
selected-model record, error expression, proof script or schedule is repeated. -/
def descriptors : List DomainClaimLibraryOutput :=
  [("SmallSumcheck", "Small"), ("TwoSums", "Two")].map fun (name, endpoint) =>
    let subject := "ZkcSecurity.Examples.Generated." ++ name
    let roots := "ZkcSecurity.Examples.Components.SumcheckSoundnessRoots"
    let proofs := roots ++ "." ++ endpoint
    { moduleName := subject ++ "SoundnessRegistration"
      imports := [subject, roots]
      subjectExpression := subject ++ ".validatorSubject"
      artifactsExpression := subject ++ ".validatorArtifacts"
      capabilitiesExpression := proofs ++ ".capabilities"
      applicationParameter := some "application"
      theoremMethods := [("fs.keyed_soundness", 0, proofs ++ ".scalar_meaning"),
        ("fs.keyed_charged", 0, proofs ++ ".charged_meaning")]
      theoremNormalization := [roots ++ ".price", roots ++ ".priceBound", proofs ++ ".schedule",
        "ZkcSecurity.Claims.CompiledSoundness.uniformSchedule"] }

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for descriptor in descriptors do
    let path := System.FilePath.mk directory /
      (descriptor.moduleName.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path (domainClaimLibrarySource descriptor)
    IO.println s!"generated {descriptor.moduleName}"

end TestsSecurity.GenerateClaimLibraries
