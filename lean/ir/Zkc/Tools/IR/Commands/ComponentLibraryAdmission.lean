import Zkc.Tests.IR.ComponentLibraryAdmission

/-- Standalone runner; the test module remains jointly importable. -/
def main (args : List String) : IO Unit := Tests.ComponentLibraryAdmission.main args
