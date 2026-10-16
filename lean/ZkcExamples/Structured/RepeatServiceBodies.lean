module

public import Zkc.Source.Structured.ProtocolOperations
public import ZkcExamples.Structured.ServiceOrderBodies

@[expose] public section

/-! Literal full signatures and typed bodies. The corresponding Views module
proves admission of the complete original snapshot. -/
namespace ZkcExamples.Structured.RepeatServiceBodies
open Zkc.Source Zkc.Source.Structured

abbrev runSignature : ProtocolSignature where
  name := "s6h73616d706c653h52756e"
  roles := ["role00000000", "role00000001"]
  inputs := [.index, .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"]
  outputs := [.field "bls12-381.fr", .field "bls12-381.fr"]
  inputScopes := [[0, 1], [1], [1]]
  outputScopes := [[0], [1]]

def drawSignature : ProtocolSignature where
  name := "s6h73616d706c654h44726177"
  roles := ["role00000000", "role00000001"]
  inputs := [.service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"]
  outputs := [.field "bls12-381.fr", .field "bls12-381.fr"]
  inputScopes := [[1], [1]]
  outputScopes := [[0], [1]]

abbrev drawBody := ServiceOrderBodies.drawBody

abbrev repeatSpec : RepeatSpec :=
  ⟨[.field "bls12-381.fr", .field "bls12-381.fr"],
    [.service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"],
    [0, 1], [[0], [1]], 3⟩

def repeatBody : Region protocolDialect
    (.index :: (repeatSpec.state ++ repeatSpec.captures)) repeatSpec.state :=
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.protocolApply drawSignature [0, 1] "s7") (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there .here)) .nil)) .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

def runBody : Region protocolDialect [.index, .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "s0") (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldConstant "bls12-381.fr" 0) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.repeat repeatSpec "s6") (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))))) (.cons repeatBody .nil) <|
  .letOp (.mark "s16") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "s16") (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there .here)) (.cons .here .nil))

end ZkcExamples.Structured.RepeatServiceBodies
