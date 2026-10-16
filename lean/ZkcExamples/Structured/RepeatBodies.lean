module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal full signatures and typed bodies. The corresponding Views module
proves admission of the complete original snapshot. -/
namespace ZkcExamples.Structured.RepeatBodies
open Zkc.Source Zkc.Source.Structured

abbrev runSignature : ProtocolSignature where
  name := "zkl_815724e04d3a27336a925a984d17bdc75b5a2cab63258eba5e870621d2b4b2fe"
  roles := ["role00000000", "role00000001"]
  inputs := [.index, .field "bls12-381.fr", .field "bls12-381.fr", .boolean, .service "random.bls12-381.fr/0"]
  outputs := [.field "bls12-381.fr", .field "bls12-381.fr"]
  inputScopes := [[0, 1], [0], [1], [1], [1]]
  outputScopes := [[0], [1]]

def roundSignature : ProtocolSignature where
  name := "zkl_477249e6aab42d11d39ecc6a67e0e99b7107d8f3e8f0d2bdcdad9431e8bc18b4"
  roles := ["role00000000", "role00000001"]
  inputs := [.field "bls12-381.fr", .field "bls12-381.fr", .service "random.bls12-381.fr/0"]
  outputs := [.field "bls12-381.fr", .field "bls12-381.fr"]
  inputScopes := [[0], [1], [1]]
  outputScopes := [[0], [1]]

def roundBody : Region protocolDialect [.field "bls12-381.fr", .field "bls12-381.fr", .service "random.bls12-381.fr/0"] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "s0") (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "s2_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 1 0 "s2_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

abbrev repeatSpec : RepeatSpec :=
  ⟨[.field "bls12-381.fr", .field "bls12-381.fr"],
    [.boolean, .service "random.bls12-381.fr/0"], [0, 1], [[0], [1]], 4⟩

def repeatBody : Region protocolDialect
    (.index :: (repeatSpec.state ++ repeatSpec.captures)) repeatSpec.state :=
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.guard 1 "s4") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.protocolApply roundSignature [0, 1] "s5") (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

def runBody : Region protocolDialect [.index, .field "bls12-381.fr", .field "bls12-381.fr", .boolean, .service "random.bls12-381.fr/0"] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.repeat repeatSpec "s3") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil))))) (.cons repeatBody .nil) <|
  .ret (.cons .here (.cons (.there .here) .nil))

end ZkcExamples.Structured.RepeatBodies
