module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`ZkcExamples.Construction.BatchOpeningData`. -/
namespace ZkcExamples.Construction.BatchOpeningBodies
open Zkc.Source Zkc.Source.Structured

abbrev checkOpeningHelper : Helper :=
  ⟨"zkl_b26f24aff1f462f4c3e9ea4c594fd6eaaac4e0d13a163302bc46f14e913cc892", .math, [.boolean, (.field "koala-bear"), (.field "koala-bear"), (.field "koala-bear"), (.field "koala-bear")], [.boolean]⟩

def checkOpeningBody : Region dialect checkOpeningHelper.inputs checkOpeningHelper.outputs :=
  .letOp (.fieldEqual "koala-bear") (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldEqual "koala-bear") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev batchStepHelper : Helper :=
  ⟨"finite_zkl_040b90e6fc9f7c074519f3a904772619b0e3c63ed7b7a051cbc3db4b3c514ff3_s3_body", .math, [.boolean, (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") .nil))), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") .nil)))), (.field "koala-bear"), (.field "koala-bear")], [.boolean]⟩

def batchStepBody : Region dialect batchStepHelper.inputs batchStepHelper.outputs :=
  .letOp (.getProduct "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons (.field "koala-bear") (ProductFields.cons (.field "koala-bear") ProductFields.nil)) (.field "koala-bear") .here) (.cons (.there .here) .nil) .nil <|
  .letOp (.getProduct "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons (.field "koala-bear") (ProductFields.cons (.field "koala-bear") ProductFields.nil)) (.field "koala-bear") (.there .here)) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.invoke {name := "zkl_b26f24aff1f462f4c3e9ea4c594fd6eaaac4e0d13a163302bc46f14e913cc892", kind := .math, inputs := [.boolean, .field "koala-bear", .field "koala-bear", .field "koala-bear", .field "koala-bear"], outputs := [.boolean]}) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))))) .nil <|
  .ret (.cons .here .nil)

abbrev batchValuesHelper : Helper :=
  ⟨"zkl_040b90e6fc9f7c074519f3a904772619b0e3c63ed7b7a051cbc3db4b3c514ff3", .math, [(.field "koala-bear"), (.field "koala-bear"), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") .nil))))], [.boolean]⟩

def batchValuesBody : Region dialect batchValuesHelper.inputs batchValuesHelper.outputs :=
  .letOp (.booleanConstant true) .nil .nil <|
  .letOp (.fold {domain := {name := "finite_zkl_040b90e6fc9f7c074519f3a904772619b0e3c63ed7b7a051cbc3db4b3c514ff3_s3_domain", inputs := [(.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons (.field "koala-bear") (ProductFields.cons (.field "koala-bear") ProductFields.nil))))], items := [.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons (.field "koala-bear") (ProductFields.cons (.field "koala-bear") ProductFields.nil))], body := DomainBody.letNode (DomainNode.elements (Collection.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons (.field "koala-bear") (ProductFields.cons (.field "koala-bear") ProductFields.nil)))) .here) (DomainBody.ret .here)}, state := [.boolean], captures := [.field "koala-bear", .field "koala-bear"], step := "finite_zkl_040b90e6fc9f7c074519f3a904772619b0e3c63ed7b7a051cbc3db4b3c514ff3_s3_body", predicate := "", kind := .math}) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev formulaHelper : Helper :=
  ⟨"zkf_53219b51c062230506c8b229ef72062dff0e276e6336e241e0b2d30a9a6fe712", .math, [(.field "koala-bear"), (.field "koala-bear"), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") .nil))))], [.boolean]⟩

def formulaBody : Region dialect formulaHelper.inputs formulaHelper.outputs :=
  .letOp (.invoke {name := "zkl_040b90e6fc9f7c074519f3a904772619b0e3c63ed7b7a051cbc3db4b3c514ff3", kind := .math, inputs := [.field "koala-bear", .field "koala-bear", (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons (.field "koala-bear") (ProductFields.cons (.field "koala-bear") ProductFields.nil))))], outputs := [.boolean]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev realizationHelper : Helper :=
  ⟨"_mathematical_admission_0", .local, [(.field "koala-bear"), (.field "koala-bear"), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") .nil))))], [.boolean]⟩

def realizationBody : Region dialect realizationHelper.inputs realizationHelper.outputs :=
  .letOp (.invoke {name := "zkl_040b90e6fc9f7c074519f3a904772619b0e3c63ed7b7a051cbc3db4b3c514ff3", kind := .math, inputs := [.field "koala-bear", .field "koala-bear", (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons (.field "koala-bear") (ProductFields.cons (.field "koala-bear") ProductFields.nil))))], outputs := [.boolean]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev checkBatchHelper : Helper :=
  ⟨"zkl_765e0fbfb20c4afe7930d2c0cbb531d52446ae1c25c74ad1237691d8738b0a85", .local, [(.field "koala-bear"), (.field "koala-bear"), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") .nil))))], [.boolean]⟩

def checkBatchBody : Region dialect checkBatchHelper.inputs checkBatchHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke {name := "_mathematical_admission_0", kind := .local, inputs := [.field "koala-bear", .field "koala-bear", (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons (.field "koala-bear") (ProductFields.cons (.field "koala-bear") ProductFields.nil))))], outputs := [.boolean]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

def runSignature : ProtocolSignature where
  name := "zkl_206d594942dc6f123848ad35c8fcdc7017b483db9ccd5c0651d1ad5c850eceab"
  roles := ["role00000000", "role00000001"]
  inputs := [(.field "koala-bear"), (.field "koala-bear"), (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") .nil))))]
  outputs := [.boolean, (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (.cons (.field "koala-bear") (.cons (.field "koala-bear") .nil))))]
  inputScopes := [[1], [1], [0]]
  outputScopes := [[1], [1]]

def runBody : Region protocolDialect runSignature.inputs runSignature.outputs :=
  .letOp (.mark "label_6261746368_0") .nil .nil <|
  .letOp (.exchange (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons (.field "koala-bear") (ProductFields.cons (.field "koala-bear") ProductFields.nil)))) 0 1 "label_6261746368_0") (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons (.field "koala-bear") (ProductFields.cons (.field "koala-bear") ProductFields.nil)))) [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.localCall {name := "zkl_765e0fbfb20c4afe7930d2c0cbb531d52446ae1c25c74ad1237691d8738b0a85", kind := .local, inputs := [.field "koala-bear", .field "koala-bear", (.sequence (.product "[\"zkc.language.pack\",\"373a303a32323a62617463685f6f70656e696e673a3a4f70656e696e67313a30313a32323a313a303a31303a6b6f616c612d62656172313a30303a\"]" "case00000000" (ProductFields.cons (.field "koala-bear") (ProductFields.cons (.field "koala-bear") ProductFields.nil))))], outputs := [.boolean]} rfl 1 "s2") (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons .here .nil))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

end ZkcExamples.Construction.BatchOpeningBodies
