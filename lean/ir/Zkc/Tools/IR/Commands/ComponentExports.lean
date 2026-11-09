import Zkc.Tests.IR.ComponentExports

/-- Standalone runner; the test module remains jointly importable. -/
def main (args : List String) : IO Unit := Tests.ComponentExports.main args
