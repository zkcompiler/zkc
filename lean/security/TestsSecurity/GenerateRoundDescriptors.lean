import ZkcSecurity.Generation.Roots.Stages

/-! Executable driver; production root configuration owns all selections. -/
namespace TestsSecurity.GenerateRoundDescriptors

def main (args : List String) : IO Unit := do
  ZkcSecurity.Generation.Roots.generateStage "rounds" args

end TestsSecurity.GenerateRoundDescriptors
