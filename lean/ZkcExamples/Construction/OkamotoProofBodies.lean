module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`ZkcExamples.Construction.OkamotoProofData`. -/
namespace ZkcExamples.Construction.OkamotoProofBodies
open Zkc.Source Zkc.Source.Structured

abbrev formulaHelper : Helper :=
  ⟨"zkf_ee2797abccd0e935344e56c0d971bac75f26e275fad5327153b3087a6373d751", .math, [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩

def formulaBody : Region dialect formulaHelper.inputs formulaHelper.outputs :=
  .letOp (.groupScale "bls12-381.g1" "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.groupScale "bls12-381.g1" "bls12-381.fr") (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .letOp (.groupAdd "bls12-381.g1") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.groupEqual "bls12-381.g1") (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def proofSignature : ProtocolSignature where
  name := "zkl_9cdd0a5f70a0ca96171d93c3dd785e5e27e287a64a646c3fc511d97f10bd4aec"
  roles := ["role00000000", "role00000001"]
  inputs := [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")]
  outputs := [.boolean]
  inputScopes := [[0, 1], [0, 1], [0, 1], [0], [0], [0], [1]]
  outputScopes := [[1]]

def proofBody : Region protocolDialect proofSignature.inputs proofSignature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.statement "zkl_c0f7bdccf86767a692c23203245eac7b9fa25c8263474880e3ae8f0eee6bc453" [.group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr", .field "bls12-381.fr"] ["role00000001", "role00000001", "role00000001", "role00000000", "role00000000"] 0) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil))))) .nil <|
  .letOp (.mark "label_66697273745f6e6f6e6365") .nil .nil <|
  .letOp (.draw 0 "bls12-381.fr" "label_66697273745f6e6f6e6365") (.cons (.there (.there (.there (.there (.there .here))))) .nil) .nil <|
  .letOp (.mark "label_7365636f6e645f6e6f6e6365") .nil .nil <|
  .letOp (.draw 0 "bls12-381.fr" "label_7365636f6e645f6e6f6e6365") (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there .here)) (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupAdd "bls12-381.g1") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "label_636f6d6d69746d656e74_0") .nil .nil <|
  .letOp (.exchange (.group "bls12-381.g1") 0 1 "label_636f6d6d69746d656e74_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.group "bls12-381.g1") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "label_6368616c6c656e6765") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil) .nil <|
  .letOp (.mark "label_64656c6976657279_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "label_66697273745f726573706f6e7365_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_66697273745f726573706f6e7365_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "label_7365636f6e645f726573706f6e7365_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_7365636f6e645f726573706f6e7365_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupAdd "bls12-381.g1") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupAdd "bls12-381.g1") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupEqual "bls12-381.g1") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Construction.OkamotoProofBodies
