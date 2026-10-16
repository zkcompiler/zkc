module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal full signatures and typed bodies. The corresponding Views module
proves admission of the complete original snapshot. -/
namespace ZkcExamples.Structured.RepeatNestedBodies
open Zkc.Source Zkc.Source.Structured

abbrev runSignature : ProtocolSignature where
  name := "s6h73616d706c653h52756e"
  roles := ["role00000000"]
  inputs := [.index, .index, .field "bls12-381.fr"]
  outputs := [.field "bls12-381.fr"]
  inputScopes := [[0], [0], [0]]
  outputScopes := [[0]]

def runBody : Region protocolDialect [.index, .index, .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.repeat ⟨[.field "bls12-381.fr"], [.index, .field "bls12-381.fr"], [0], [[0]], 3⟩ "s3") (.cons .here (.cons (.there (.there .here)) (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) (.cons (
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.repeat ⟨[.field "bls12-381.fr"], [.field "bls12-381.fr"], [0], [[0]], 2⟩ "s5") (.cons (.there (.there .here)) (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) (.cons (
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .ret (.cons .here .nil)) .nil) <|
  .ret (.cons .here .nil)) .nil) <|
  .ret (.cons .here .nil)

end ZkcExamples.Structured.RepeatNestedBodies
