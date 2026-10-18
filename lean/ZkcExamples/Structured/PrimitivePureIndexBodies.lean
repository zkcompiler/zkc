module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`ZkcExamples.Structured.PrimitivePureIndexData`. -/
namespace ZkcExamples.Structured.PrimitivePureIndexBodies
open Zkc.Source Zkc.Source.Structured

def pureIndexSignature : ProtocolSignature where
  name := "s18h7072696d69746976655f6578616d706c65739h50757265496e646578"
  roles := ["role00000000", "role00000001"]
  inputs := [.index]
  outputs := [.boolean]
  inputScopes := [[0]]
  outputScopes := [[0]]

def pureIndexBody : Region protocolDialect pureIndexSignature.inputs pureIndexSignature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 0) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Structured.PrimitivePureIndexBodies
