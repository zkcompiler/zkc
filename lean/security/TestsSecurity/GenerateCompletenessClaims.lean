import ZkcSecurityExamples.Generation.Roots.Stages

/-! Executable driver; production root configuration owns all selections. -/
namespace TestsSecurity.GenerateCompletenessClaims

def main (args : List String) : IO Unit := do
  ZkcSecurity.Generation.Roots.generateStage "completeness-claims" args

end TestsSecurity.GenerateCompletenessClaims
