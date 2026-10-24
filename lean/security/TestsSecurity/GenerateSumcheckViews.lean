import ZkcSecurity.Generation.Roots.Stages

/-! Executable driver; production root configuration owns all selections. -/
namespace TestsSecurity.GenerateSumcheckViews

def main (args : List String) : IO Unit := do
  ZkcSecurity.Generation.Roots.generateStage "views" args

end TestsSecurity.GenerateSumcheckViews
