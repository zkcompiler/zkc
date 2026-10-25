module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Typed body candidates mechanically rendered from the actual structured export.
The binding module checks every body against that exact snapshot. -/
namespace ZkcExamples.Construction.EmbeddingEqualityBodies
open Zkc.Source Zkc.Source.Structured

abbrev formulaHelper : Helper := ⟨"zkf_fe5e2a3c5bbade8b5ce48ffd090142e127cc04ea947d1766a7f847161f657190", .math, [.field "koala-bear", .field "koala-bear"], [.boolean]⟩

def formulaBody : Region dialect formulaHelper.inputs formulaHelper.outputs :=
  .letOp (.fieldEqual "koala-bear") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev embeddingHelper : Helper := ⟨"s7h6578616d706c655h656d626564", .local, [.field "koala-bear"], [.field "koala-bear.ext8-binomial3"]⟩

def embeddingBody : Region dialect embeddingHelper.inputs embeddingHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.fieldEmbed "koala-bear.ext8-binomial3" "koala-bear") (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

def proofSignature : ProtocolSignature where
  name := "s7h6578616d706c6517h456d62656464696e67457175616c697479"
  roles := ["role00000000", "role00000001"]
  inputs := [.field "koala-bear", .field "koala-bear", .service "random.koala-bear.ext8-binomial3/0"]
  outputs := [.boolean]
  inputScopes := [[0, 1], [1], [1]]
  outputScopes := [[1]]

def proofBody : Region protocolDialect proofSignature.inputs proofSignature.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall embeddingHelper rfl 0 "s0") (.cons .here .nil) .nil <|
  .letOp (.mark "label_6d657373616765_0") .nil .nil <|
  .letOp (.exchange (.field "koala-bear.ext8-binomial3") 0 1 "label_6d657373616765_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "koala-bear.ext8-binomial3") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "label_6368616c6c656e6765") .nil .nil <|
  .letOp (.draw 1 "koala-bear.ext8-binomial3" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there .here))))) .nil) .nil <|
  .letOp (.mark "label_64656c6976657279_0") .nil .nil <|
  .letOp (.exchange (.field "koala-bear.ext8-binomial3") 1 0 "label_64656c6976657279_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "koala-bear.ext8-binomial3") [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "koala-bear.ext8-binomial3") rfl) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.localCall embeddingHelper rfl 1 "s9") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "koala-bear.ext8-binomial3") rfl) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldEqual "koala-bear.ext8-binomial3") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "koala-bear.ext8-binomial3") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.mark "s14") .nil .nil <|
  .letOp (.localCall embeddingHelper rfl 1 "s14") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "koala-bear.ext8-binomial3") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldEqual "koala-bear.ext8-binomial3") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanAnd) rfl) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Construction.EmbeddingEqualityBodies
