module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal signatures and typed bodies of the three retained Schnorr source
forms: the helper-based verifier with its two Math helpers, the reordered
verifier and the early-challenge mutation. `SchnorrVariants` proves admission
of each complete original snapshot from these bodies. -/
namespace ZkcExamples.Structured.SchnorrVariantsBodies
open Zkc.Source Zkc.Source.Structured

abbrev responseHelper : Helper :=
  ⟨"s13h7363686e6f72725f666f726d738h726573706f6e7365", .math,
    [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def responseBody : Region dialect responseHelper.inputs responseHelper.outputs :=
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev equationHelper : Helper :=
  ⟨"s13h7363686e6f72725f666f726d738h6571756174696f6e", .math,
    [.group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr",
      .field "bls12-381.fr"], [.boolean]⟩

def equationBody : Region dialect equationHelper.inputs equationHelper.outputs :=
  .letOp (.groupScale "bls12-381.g1" "bls12-381.fr") (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.groupScale "bls12-381.g1" "bls12-381.fr") (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.groupAdd "bls12-381.g1") (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .letOp (.groupEqual "bls12-381.g1") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def helpersSignature : ProtocolSignature where
  name := "s13h7363686e6f72725f666f726d7315h48656c7065727350726f746f636f6c"
  roles := ["role00000000", "role00000001"]
  inputs := [.group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr",
    .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"]
  outputs := [.boolean]
  inputScopes := [[0, 1], [0, 1], [0], [0], [1]]
  outputScopes := [[1]]

def helpersBody : Region protocolDialect helpersSignature.inputs helpersSignature.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.draw 0 "bls12-381.fr" "s0") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "label_636f6d6d69746d656e74_0") .nil .nil <|
  .letOp (.exchange (.group "bls12-381.g1") 0 1 "label_636f6d6d69746d656e74_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.group "bls12-381.g1") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "label_6368616c6c656e6765") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil) .nil <|
  .letOp (.mark "label_64656c6976657279_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke {name := "s13h7363686e6f72725f666f726d738h726573706f6e7365", kind := .math, inputs := [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr"]}) rfl) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil))) .nil <|
  .letOp (.mark "label_726573706f6e7365_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726573706f6e7365_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke {name := "s13h7363686e6f72725f666f726d738h6571756174696f6e", kind := .math, inputs := [.group "bls12-381.g1", .group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.boolean]}) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil))))) .nil <|
  .ret (.cons .here .nil)

def reorderedSignature : ProtocolSignature where
  name := "s13h7363686e6f72725f666f726d7317h52656f72646572656450726f746f636f6c"
  roles := ["role00000000", "role00000001"]
  inputs := [.group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr",
    .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"]
  outputs := [.boolean]
  inputScopes := [[0, 1], [0, 1], [0], [0], [1]]
  outputScopes := [[1]]

def reorderedBody : Region protocolDialect reorderedSignature.inputs reorderedSignature.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.draw 0 "bls12-381.fr" "s0") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "label_636f6d6d69746d656e74_0") .nil .nil <|
  .letOp (.exchange (.group "bls12-381.g1") 0 1 "label_636f6d6d69746d656e74_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.group "bls12-381.g1") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "label_6368616c6c656e6765") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil) .nil <|
  .letOp (.mark "label_64656c6976657279_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "label_726573706f6e7365_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726573706f6e7365_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupAdd "bls12-381.g1") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupEqual "bls12-381.g1") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def earlySignature : ProtocolSignature where
  name := "s13h7363686e6f72725f666f726d7322h4561726c794368616c6c656e676550726f746f636f6c"
  roles := ["role00000000", "role00000001"]
  inputs := [.group "bls12-381.g1", .group "bls12-381.g1", .field "bls12-381.fr",
    .service "random.bls12-381.fr/0", .service "random.bls12-381.fr/0"]
  outputs := [.boolean]
  inputScopes := [[0, 1], [0, 1], [0], [0], [1]]
  outputScopes := [[1]]

def earlyBody : Region protocolDialect earlySignature.inputs earlySignature.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.draw 0 "bls12-381.fr" "s0") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "label_6368616c6c656e6765") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there .here))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there .here)) (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "label_636f6d6d69746d656e74_0") .nil .nil <|
  .letOp (.exchange (.group "bls12-381.g1") 0 1 "label_636f6d6d69746d656e74_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.group "bls12-381.g1") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "label_64656c6976657279_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "label_726573706f6e7365_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726573706f6e7365_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupAdd "bls12-381.g1") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.groupEqual "bls12-381.g1") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Structured.SchnorrVariantsBodies
