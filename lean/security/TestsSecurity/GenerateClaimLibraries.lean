import ZkcSecurityExamples.Generation.Roots.Stages

/-! Executable driver; production root configuration owns all selections. -/
namespace TestsSecurity.GenerateClaimLibraries

def main (args : List String) : IO Unit := do
  ZkcSecurity.Generation.Roots.generateStage "claim-libraries" args

end TestsSecurity.GenerateClaimLibraries
