module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.ApplicationWrapperData
public import ZkcExamples.Structured.ServiceOrderViews

@[expose] public section

/-! Complete retained wrapper source with one exact admission theorem. Draw and
Run reuse their literal bodies; the wrapper retains its own complete snapshot. -/
namespace ZkcExamples.Structured.ApplicationWrapperViews
open Zkc.Source Zkc.Source.Structured ServiceOrderBodies

def outerSignature : ProtocolSignature where
  name := "s6h73616d706c655h4f75746572"
  roles := roles
  inputs := inputTypes
  outputs := resultTypes
  inputScopes := [[1], [1], [1]]
  outputScopes := [[0], [1]]

def outerBody : Region protocolDialect inputTypes resultTypes :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.protocolApply runSignature [0, 1] "s0")
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

set_option smartUnfolding false

structured_views ApplicationWrapperData.snapshot
  helpers []
  protocols [draw, run, outer]

end ZkcExamples.Structured.ApplicationWrapperViews
