import ZkcSecurity.Generation.Roots.Stages

/-! Executable driver; production root configuration owns all selections. -/
namespace TestsSecurity.GenerateSubjectABI

def main (args : List String) : IO Unit := do
  ZkcSecurity.Generation.Roots.generateStage "abi" args

end TestsSecurity.GenerateSubjectABI
