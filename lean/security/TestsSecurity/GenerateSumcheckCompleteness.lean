import ZkcSecurityExamples.Generation.Roots.Stages

/-! Executable driver; production root configuration owns all selections. -/
namespace TestsSecurity.GenerateSumcheckCompleteness

def main (args : List String) : IO Unit := do
  ZkcSecurity.Generation.Roots.generateStage "completeness" args

end TestsSecurity.GenerateSumcheckCompleteness
