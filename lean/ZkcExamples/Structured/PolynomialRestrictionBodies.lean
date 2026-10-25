module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`ZkcExamples.Structured.PolynomialRestrictionData`. -/
namespace ZkcExamples.Structured.PolynomialRestrictionBodies
open Zkc.Source Zkc.Source.Structured

abbrev restrictHelper : Helper :=
  ⟨"zkl_cc6a01baa45918f376cb6ffba1012908fa5bb9dc3dea3db7ae9aa4c1234e154e", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def restrictBody : Region dialect restrictHelper.inputs restrictHelper.outputs :=
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there .here)) (.cons .here .nil))

abbrev evaluateHelper : Helper :=
  ⟨"zkl_46b4d88e04a6cc2620fbb8d192b97f457501737e0adf33682df330fcdd974078", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def evaluateBody : Region dialect evaluateHelper.inputs evaluateHelper.outputs :=
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def callerSignature : ProtocolSignature where
  name := "s22h706f6c796e6f6d69616c5f7265737472696374696f6e11h5265737472696374696f6e"
  roles := ["role00000000"]
  inputs := [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]
  outputs := [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]
  inputScopes := [[0], [0], [0], [0], [0], [0], [0]]
  outputScopes := [[0], [0], [0], [0]]

def callerBody : Region protocolDialect callerSignature.inputs callerSignature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke {name := "zkl_cc6a01baa45918f376cb6ffba1012908fa5bb9dc3dea3db7ae9aa4c1234e154e", kind := .math, inputs := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr", .field "bls12-381.fr"]}) rfl) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil))))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke {name := "zkl_46b4d88e04a6cc2620fbb8d192b97f457501737e0adf33682df330fcdd974078", kind := .math, inputs := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr"]}) rfl) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))) .nil <|
  .ret (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil))))

def entryBody : Region dialect [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")] [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.invoke {name := "zkl_cc6a01baa45918f376cb6ffba1012908fa5bb9dc3dea3db7ae9aa4c1234e154e", kind := .math, inputs := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr", .field "bls12-381.fr"]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil))))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.invoke {name := "zkl_46b4d88e04a6cc2620fbb8d192b97f457501737e0adf33682df330fcdd974078", kind := .math, inputs := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr"]}) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))) .nil <|
  .ret (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil))))

end ZkcExamples.Structured.PolynomialRestrictionBodies
