module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`ZkcExamples.Structured.TableIndexedReadData`. -/
namespace ZkcExamples.Structured.TableIndexedReadBodies
open Zkc.Source Zkc.Source.Structured

abbrev readDecisionHelper : Helper :=
  ⟨"zkl_b495e0ed1417c211869f7fedf6d130630630d8ae869a74d3e0edf61af30302b3", .math, [.boolean, .index, .index, (.vector "koala-bear"), (.field "koala-bear")], [.boolean]⟩

def readDecisionBody : Region dialect readDecisionHelper.inputs readDecisionHelper.outputs :=
  .letOp .indexEqual (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.boundedAt "koala-bear") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.fieldEqual "koala-bear") (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp .booleanOr (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev readStepHelper : Helper :=
  ⟨"finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_body", .math, [.boolean, .index, (.vector "koala-bear"), .index, (.field "koala-bear")], [.boolean]⟩

def readStepBody : Region dialect readStepHelper.inputs readStepHelper.outputs :=
  .letOp (.invoke {name := "zkl_b495e0ed1417c211869f7fedf6d130630630d8ae869a74d3e0edf61af30302b3", kind := .math, inputs := [.boolean, .index, .index, .vector "koala-bear", .field "koala-bear"], outputs := [.boolean]}) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) .nil))))) .nil <|
  .ret (.cons .here .nil)

abbrev indexedReadHelper : Helper :=
  ⟨"zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a", .math, [(.vector "koala-bear"), .index, (.field "koala-bear")], [.boolean]⟩

def indexedReadBody : Region dialect indexedReadHelper.inputs indexedReadHelper.outputs :=
  .letOp (.booleanConstant false) .nil .nil <|
  .letOp (.fold {domain := {name := "finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_domain", inputs := [.vector "koala-bear"], collection := Collection.vector "koala-bear", container := .here, indices := true}, state := [.boolean], captures := [.index, .field "koala-bear"], step := "finite_zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a_s4_body", predicate := "", kind := .math}) (.cons (.there .here) (.cons .here (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev realizationHelper : Helper :=
  ⟨"zkl_realization_f23e2cf91e13194bc53b5a53cc8b12fd546c4daae64d3751bb30899d04fa3be4", .local, [(.vector "koala-bear"), .index, (.field "koala-bear")], [.boolean]⟩

def realizationBody : Region dialect realizationHelper.inputs realizationHelper.outputs :=
  .letOp (.invoke {name := "zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a", kind := .math, inputs := [.vector "koala-bear", .index, .field "koala-bear"], outputs := [.boolean]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev formulaHelper : Helper :=
  ⟨"zkf_eeb8bf15a7659bce5aa909302f5a359e054778ba70f159e4c02088dc98b55444", .math, [(.vector "koala-bear"), .index, (.field "koala-bear")], [.boolean]⟩

def formulaBody : Region dialect formulaHelper.inputs formulaHelper.outputs :=
  .letOp (.invoke {name := "zkl_513fafc86f60e415471e1286479cbd64b87fc18d657412194e4e0974b61e260a", kind := .math, inputs := [.vector "koala-bear", .index, .field "koala-bear"], outputs := [.boolean]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev checkReadHelper : Helper :=
  ⟨"zkl_f1d7fac3d3ce489e30442c70b43fb2fd1ecf6ba206d6f59492b3f75b72249a66", .local, [(.vector "koala-bear"), .index, (.field "koala-bear")], [.boolean]⟩

def checkReadBody : Region dialect checkReadHelper.inputs checkReadHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke {name := "zkl_realization_f23e2cf91e13194bc53b5a53cc8b12fd546c4daae64d3751bb30899d04fa3be4", kind := .local, inputs := [.vector "koala-bear", .index, .field "koala-bear"], outputs := [.boolean]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

def runSignature : ProtocolSignature where
  name := "zkl_4597680e78fa47047d8f8fcedcf8fe295ebd02cf0856991e260e9130a8d2ea87"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "koala-bear"), .index, (.field "koala-bear")]
  outputs := [.boolean]
  inputScopes := [[1], [1], [1]]
  outputScopes := [[1]]

def runBody : Region protocolDialect runSignature.inputs runSignature.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall {name := "zkl_f1d7fac3d3ce489e30442c70b43fb2fd1ecf6ba206d6f59492b3f75b72249a66", kind := .local, inputs := [.vector "koala-bear", .index, .field "koala-bear"], outputs := [.boolean]} rfl 1 "s0") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Structured.TableIndexedReadBodies
