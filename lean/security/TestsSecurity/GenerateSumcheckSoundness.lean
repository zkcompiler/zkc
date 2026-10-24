import ZkcSecurity.Generation.Roots.Stages

/-! Executable driver; production root configuration owns all selections. -/
namespace TestsSecurity.GenerateSumcheckSoundness

def main (args : List String) : IO Unit := do
  ZkcSecurity.Generation.Roots.generateStage "soundness" args

end TestsSecurity.GenerateSumcheckSoundness
