module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal signatures and exact typed bodies for the complete service-order
source. Source authority is supplied by ServiceOrderViews.kernel_admission. -/
namespace ZkcExamples.Structured.ServiceOrderBodies
open Zkc.Source Zkc.Source.Structured

abbrev fieldType : Ty := .field "bls12-381.fr"
abbrev serviceType : Ty := .service "random.bls12-381.fr/0"
abbrev resultTypes : List Ty := [fieldType, fieldType]
abbrev serviceTypes : List Ty := [serviceType, serviceType]
abbrev inputTypes : List Ty := [.boolean, serviceType, serviceType]
abbrev roles : List String := ["role00000000", "role00000001"]

def drawSignature : ProtocolSignature where
  name := "s6h73616d706c654h44726177"
  roles := roles
  inputs := serviceTypes
  outputs := resultTypes
  inputScopes := [[1], [1]]
  outputScopes := [[0], [1]]

def runSignature : ProtocolSignature where
  name := "s6h73616d706c653h52756e"
  roles := roles
  inputs := inputTypes
  outputs := resultTypes
  inputScopes := [[1], [1], [1]]
  outputScopes := [[0], [1]]

def drawBody : Region protocolDialect serviceTypes resultTypes :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "s0") (.cons .here .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "s2")
    (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl)
    (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s5_0") .nil .nil <|
  .letOp (.exchange fieldType 1 0 "s5_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict fieldType [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl)
    (.cons (.there (.there (.there (.there .here))))
      (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

def runBody : Region protocolDialect inputTypes resultTypes :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "s0") (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.guard 1 "s2") (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.protocolApply drawSignature [0, 1] "s3")
    (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "s6")
    (.cons (.there (.there (.there (.there .here)))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl)
    (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl)
    (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons (.there (.there (.there .here))) (.cons .here .nil))

end ZkcExamples.Structured.ServiceOrderBodies
