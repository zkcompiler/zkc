import ZkcTools.StructuredSource.Root

namespace TestsSecurity.GenerateClaimLibraries
open ZkcTools.StructuredSource.Root

/-! Protocol choices are source subject and installed theorem exports. No
selected-model record, error expression, proof script or schedule is repeated. -/
def descriptors : List DomainClaimLibraryOutput :=
  ["SmallSumcheck", "TwoSums"].map fun name =>
    let subject := "ZkcSecurity.Examples.Generated." ++ name
    let proofs := "ZkcSecurity.Examples.Generated.Components." ++ name ++ "Soundness"
    { moduleName := subject ++ "SoundnessRegistration"
      imports := [subject, proofs]
      subjectExpression := subject ++ ".validatorSubject"
      artifactsExpression := subject ++ ".validatorArtifacts"
      capabilitiesExpression := proofs ++ ".capabilities"
      applicationParameter := some "application"
      theoremMethods := [("fs.keyed_soundness", 0, proofs ++ ".scalar_meaning"),
        ("fs.keyed_charged", 0, proofs ++ ".charged_meaning")]
      theoremNormalization := [proofs ++ ".price", proofs ++ ".priceBound", proofs ++ ".budget", proofs ++ ".schedule",
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
