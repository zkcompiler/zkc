import TestsSecurity.GenerateRoundDescriptors

/-! Focused generator entry point, independent of the shared generator driver. -/
def main (args : List String) : IO Unit :=
  TestsSecurity.GenerateRoundDescriptors.main args
