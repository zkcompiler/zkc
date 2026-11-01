import Tests.SourceConfigurationSelection

/-! Executable driver for source-configuration generation and refusal controls. -/
def main (args : List String) : IO Unit :=
  Tests.SourceConfigurationSelection.checkGenerated args
