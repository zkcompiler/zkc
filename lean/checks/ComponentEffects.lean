import Tests.ComponentEffects

/-- Standalone runner; the test module remains jointly importable. -/
def main (args : List String) : IO Unit := Tests.ComponentEffects.main args
