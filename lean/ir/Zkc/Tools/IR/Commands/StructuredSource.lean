module

import Zkc.Tools.IR.StructuredSource

public def main (args : List String) : IO UInt32 := do
  try ZkcTools.StructuredSource.run args
  catch _ => Zkc.Tools.refused "structured-source-io"
