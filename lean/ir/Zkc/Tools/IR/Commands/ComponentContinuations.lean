import Zkc.Tests.IR.ComponentContinuations

/-- Standalone runner; the test module remains jointly importable. -/
def main (args : List String) : IO Unit := Tests.ComponentContinuations.main args
