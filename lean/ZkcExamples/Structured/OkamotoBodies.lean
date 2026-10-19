module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`ZkcExamples.Structured.OkamotoData`. -/
namespace ZkcExamples.Structured.OkamotoBodies
open Zkc.Source Zkc.Source.Structured

abbrev formulaHelper : Helper :=
  ⟨"zkf_01154fec8af291aca8be519c449a67c049aa4dcb065a920025604d72b145cb5c", .math, [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩

def formulaBody : Region dialect formulaHelper.inputs formulaHelper.outputs :=
  .letOp (.groupScale "bls12-381.g1" "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.groupScale "bls12-381.g1" "bls12-381.fr") (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .letOp (.groupAdd "bls12-381.g1") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.groupEqual "bls12-381.g1") (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def interactiveSignature : ProtocolSignature where
  name := "zkl_cb3e72883b485338da9280b19db8db790298fd13d2324e645c75fcbf0f3b86c9"
  roles := ["role00000000", "role00000001"]
  inputs := [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")]
  outputs := [.boolean]
  inputScopes := [[0, 1], [0, 1], [0, 1], [0], [0], [0], [1]]
  outputScopes := [[1]]

def interactiveBody : Region protocolDialect interactiveSignature.inputs interactiveSignature.outputs :=
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

end ZkcExamples.Structured.OkamotoBodies
