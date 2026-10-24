import ZkcSecurity.Generation.Roots.Subjects

/-! Executable driver; production root configuration owns all selections. -/
namespace TestsSecurity.GenerateSubjects

def main (args : List String) : IO Unit := do
  ZkcSecurity.Generation.Roots.generateSubjects args

end TestsSecurity.GenerateSubjects
