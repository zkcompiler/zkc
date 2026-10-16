module

public import Zkc.Source.Structured.ProtocolOperations
public import ZkcExamples.Structured.ServiceOrderBodies
public import ZkcExamples.Structured.RepeatServiceBodies

@[expose] public section

/-! Literal full signatures and typed bodies. The corresponding Views module
proves admission of the complete original snapshot. -/
namespace ZkcExamples.Structured.RepeatServiceWrapperBodies
open Zkc.Source Zkc.Source.Structured

def outerSignature : ProtocolSignature where
  name := "s6h73616d706c655h4f75746572"
  roles := ["role00000000", "role00000001", "role00000002"]
  inputs := [.index, .field "bls12-381.fr", .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"]
  outputs := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"]
  inputScopes := [[0, 2], [1], [0], [0]]
  outputScopes := [[0], [1], [2]]

def runSignature : ProtocolSignature where
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

abbrev runBody := RepeatServiceBodies.runBody

def outerBody : Region protocolDialect [.index, .field "bls12-381.fr", .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"] [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.protocolApply runSignature [2, 0] "s0") (.cons .here (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .ret (.cons (.there .here) (.cons (.there (.there (.there .here))) (.cons .here .nil)))

end ZkcExamples.Structured.RepeatServiceWrapperBodies
