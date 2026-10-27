module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`ZkcExamples.Structured.MapCombinationData`. -/
namespace ZkcExamples.Structured.MapCombinationBodies
open Zkc.Source Zkc.Source.Structured

abbrev scaleHelper : Helper :=
  ⟨"s12h6d61705f6578616d706c65735h7363616c65", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def scaleBody : Region dialect scaleHelper.inputs scaleHelper.outputs :=
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev formulaHelper : Helper :=
  ⟨"s12h6d61705f6578616d706c65736h6c696e656172", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def formulaBody : Region dialect formulaHelper.inputs formulaHelper.outputs :=
  .letOp (.invoke {name := "s12h6d61705f6578616d706c65735h7363616c65", kind := .math, inputs := [.field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr"]}) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.invoke {name := "s12h6d61705f6578616d706c65735h7363616c65", kind := .math, inputs := [.field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr"]}) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldConstant "bls12-381.fr" 3) .nil .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev formulaRealizationHelper : Helper :=
  ⟨"_mathematical_admission_1", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def formulaRealizationBody : Region dialect formulaRealizationHelper.inputs formulaRealizationHelper.outputs :=
  .letOp (.invoke {name := "s12h6d61705f6578616d706c65736h6c696e656172", kind := .math, inputs := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr"]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))) .nil <|
  .ret (.cons .here .nil)

abbrev mapCallbackHelper : Helper :=
  ⟨"zkl_map_40c6231bdcafed97eac948be749084ce0abec13b10621543e354f70698ea9db6_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def mapCallbackBody : Region dialect mapCallbackHelper.inputs mapCallbackHelper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke {name := "_mathematical_admission_1", kind := .local, inputs := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr"]}) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))))) .nil <|
  .ret (.cons .here .nil)

abbrev mapHelper : Helper :=
  ⟨"_finite_admission_0", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

abbrev collectSpec : CollectSpec :=
  {domain := {name := "zkl_map_40c6231bdcafed97eac948be749084ce0abec13b10621543e354f70698ea9db6_domain", inputs := [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"], items := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], body := DomainBody.letNode (DomainNode.elements (Collection.vector "bls12-381.fr") .here) (DomainBody.letNode (DomainNode.elements (Collection.vector "bls12-381.fr") (.there .here)) (DomainBody.letNode (DomainNode.zip [[.field "bls12-381.fr"], [.field "bls12-381.fr"]] (.cons (.there .here) (.cons .here .nil))) (DomainBody.letNode (DomainNode.elements (Collection.vector "bls12-381.fr") (.there (.there .here))) (DomainBody.letNode (DomainNode.zip [[.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]] (.cons (.there .here) (.cons .here .nil))) (DomainBody.ret .here)))))}, collection := Collection.vector "bls12-381.fr", captures := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], body := "zkl_map_40c6231bdcafed97eac948be749084ce0abec13b10621543e354f70698ea9db6_body", predicate := "", kind := .local}

def mapBody : Region dialect mapHelper.inputs mapHelper.outputs :=
  .letOp (.collect collectSpec) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))) .nil <|
  .ret (.cons .here .nil)

abbrev wrapperHelper : Helper :=
  ⟨"s12h6d61705f6578616d706c657311h636f6d62696e6174696f6e", .local, [(.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def wrapperBody : Region dialect wrapperHelper.inputs wrapperHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke {name := "_finite_admission_0", kind := .local, inputs := [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.vector "bls12-381.fr"]}) (.cons (.there .here) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))) .nil <|
  .ret (.cons .here .nil)

abbrev protocolSignature : ProtocolSignature where
  name := "s12h6d61705f6578616d706c657317h4c696e656172436f6d62696e6174696f6e"
  roles := ["role00000000", "role00000001"]
  inputs := [(.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]
  outputs := [(.vector "bls12-381.fr")]
  inputScopes := [[0], [0], [0], [0], [0], [0]]
  outputScopes := [[0]]

def protocolBody : Region protocolDialect protocolSignature.inputs protocolSignature.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall {name := "s12h6d61705f6578616d706c657311h636f6d62696e6174696f6e", kind := .local, inputs := [.field "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], outputs := [.vector "bls12-381.fr"]} rfl 0 "s0") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Structured.MapCombinationBodies
