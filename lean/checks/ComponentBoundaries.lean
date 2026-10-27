import Tests.ComponentBoundaries

/-- Standalone runner; the test module remains jointly importable. -/
def main (args : List String) : IO Unit := Tests.ComponentBoundaries.main args
