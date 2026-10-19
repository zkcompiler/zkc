module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal full signatures and typed bodies of the GKR source
(`examples/projects/gkr`, `example::Interactive` and `example::Proof`). The
Views module proves admission of the complete original snapshot from them. -/
namespace ZkcExamples.Structured.GkrSourceBodies
open Zkc.Source Zkc.Source.Structured

abbrev emptyHelper : Helper := ⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [.vector "bls12-381.fr"]⟩

def emptyBody : Region dialect [] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .ret (.cons .here .nil)

abbrev appendHelper : Helper := ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def appendBody : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper2Helper : Helper := ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩

def helper2Body : Region dialect [.index, .index] [.boolean] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexLess)) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper3Helper : Helper := ⟨"s3h7a6b6311h6d756c74696c696e6561724h726f7773", .local, [.index], [.index]⟩

def helper3Body : Region dialect [.index] [.index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 64)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (
    .ret .nil) (.cons (
    .letOp (.mark "s2_reject") .nil .nil <|
    .stop .reject) .nil)) <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.loop [.index] []) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil))) (.cons (
    .letOp (.mark "s7") .nil .nil <|
    .letOp (.exec (.indexConstant 2)) .nil .nil <|
    .letOp (.mark "s8") .nil .nil <|
    .letOp (.exec (.indexMul)) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
    .ret (.cons .here .nil)) .nil) <|
  .ret (.cons .here .nil)

abbrev helper4Helper : Helper := ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [.vector "bls12-381.fr", .index, .index], [.boolean]⟩

def helper4Body : Region dialect [.vector "bls12-381.fr", .index, .index] [.boolean] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.branch [.index] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) .nil)) (.cons (
    .letOp (.mark "s4") .nil .nil <|
    .letOp (.exec (.indexConstant 64)) .nil .nil <|
    .letOp (.mark "s5") .nil .nil <|
    .letOp (.invoke ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩) (.cons (.there .here) (.cons .here .nil)) .nil <|
    .ret (.cons .here .nil)) (.cons (
    .letOp (.mark "s7") .nil .nil <|
    .letOp (.booleanConstant false) .nil .nil <|
    .ret (.cons .here .nil)) .nil)) <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.branch [.vector "bls12-381.fr", .index] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) (.cons (
    .letOp (.mark "s12") .nil .nil <|
    .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons .here .nil) .nil <|
    .letOp (.mark "s13") .nil .nil <|
    .letOp (.exec (.indexMod)) (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
    .letOp (.mark "s14") .nil .nil <|
    .letOp (.exec (.indexConstant 0)) .nil .nil <|
    .letOp (.mark "s15") .nil .nil <|
    .letOp (.exec (.indexEqual)) (.cons (.there .here) (.cons .here .nil)) .nil <|
    .ret (.cons .here .nil)) (.cons (
    .letOp (.mark "s17") .nil .nil <|
    .letOp (.booleanConstant false) .nil .nil <|
    .ret (.cons .here .nil)) .nil)) <|
  .letOp (.mark "s22") .nil .nil <|
  .letOp (.branch [.vector "bls12-381.fr", .index, .index] [.boolean]) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) (.cons (
    .letOp (.mark "s23") .nil .nil <|
    .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons .here .nil) .nil <|
    .letOp (.mark "s24") .nil .nil <|
    .letOp (.exec (.indexDiv)) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
    .letOp (.mark "s25") .nil .nil <|
    .letOp (.invoke ⟨"s3h7a6b6311h6d756c74696c696e6561724h726f7773", .local, [.index], [.index]⟩) (.cons (.there (.there (.there .here))) .nil) .nil <|
    .letOp (.mark "s26") .nil .nil <|
    .letOp (.exec (.indexEqual)) (.cons (.there .here) (.cons .here .nil)) .nil <|
    .ret (.cons .here .nil)) (.cons (
    .letOp (.mark "s28") .nil .nil <|
    .letOp (.booleanConstant false) .nil .nil <|
    .ret (.cons .here .nil)) .nil)) <|
  .ret (.cons .here .nil)

abbrev helper5Helper : Helper := ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩

def helper5Body : Region dialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [.vector "bls12-381.fr", .index, .index], [.boolean]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (
    .ret .nil) (.cons (
    .letOp (.mark "s1_reject") .nil .nil <|
    .stop .reject) .nil)) <|
  .ret (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))

abbrev helper6Helper : Helper := ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .vector "bls12-381.fr"]⟩

def helper6Body : Region dialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩) (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (
    .ret .nil) (.cons (
    .letOp (.mark "s3_reject") .nil .nil <|
    .stop .reject) .nil)) <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there .here)) .nil) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper7Helper : Helper := ⟨"zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", .math, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def helper7Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper8Helper : Helper := ⟨"zkl_map_7aa10c0d106e0082840e035854d97e34de85744d05e64191205f7ada5a3efd95", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper8Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.map ⟨"zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", "bls12-381.fr", [true, true, false]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper9Helper : Helper := ⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def helper9Body : Region dialect [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke ⟨"zkl_map_7aa10c0d106e0082840e035854d97e34de85744d05e64191205f7ada5a3efd95", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.exec (.indexSub)) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))

abbrev helper10Helper : Helper := ⟨"zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def helper10Body : Region dialect [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper11Helper : Helper := ⟨"finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def helper11Body : Region dialect [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .vector "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke ⟨"zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", .local, [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper12Helper : Helper := ⟨"finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩

def helper12Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.fold ⟨⟨"finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain", [.vector "bls12-381.fr"], "bls12-381.fr", .here, false⟩, [.vector "bls12-381.fr", .index, .index], [], "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper13Helper : Helper := ⟨"zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def helper13Body : Region dialect [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper14Helper : Helper := ⟨"zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩

def helper14Body : Region dialect [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"] [.vector "bls12-381.fr", .index, .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper15Helper : Helper := ⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩

def helper15Body : Region dialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr"] :=
  .ret (.cons .here .nil)

abbrev helper16Helper : Helper := ⟨"zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩

def helper16Body : Region dialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr"] :=
  .letOp (.invoke ⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev evaluateHelper : Helper := ⟨"zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def evaluateBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke ⟨"zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke ⟨"zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

abbrev helper18Helper : Helper := ⟨"s3h676b7212h706f7765725f6f665f74776f", .local, [.index], [.index]⟩

def helper18Body : Region dialect [.index] [.index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.loop [.index] []) (.cons .here (.cons (.there (.there .here)) (.cons (.there .here) .nil))) (.cons (
    .letOp (.mark "s4") .nil .nil <|
    .letOp (.exec (.indexConstant 2)) .nil .nil <|
    .letOp (.mark "s5") .nil .nil <|
    .letOp (.exec (.indexMul)) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
    .ret (.cons .here .nil)) .nil) <|
  .ret (.cons .here .nil)

abbrev selectBlockHelper : Helper := ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩

def selectBlockBody : Region dialect [.vector "bls12-381.fr", .index, .index] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.loop [.vector "bls12-381.fr", .index] [.index]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there .here) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil))))) (.cons (
    .letOp (.mark "s5") .nil .nil <|
    .letOp (.exec (.indexConstant 1)) .nil .nil <|
    .letOp (.mark "s6") .nil .nil <|
    .letOp (.exec (.indexSub)) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
    .letOp (.mark "s8") .nil .nil <|
    .letOp (.invoke ⟨"s3h676b7212h706f7765725f6f665f74776f", .local, [.index], [.index]⟩) (.cons .here .nil) .nil <|
    .letOp (.mark "s9") .nil .nil <|
    .letOp (.exec (.indexDiv)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here .nil)) .nil <|
    .letOp (.mark "s10") .nil .nil <|
    .letOp (.exec (.indexConstant 2)) .nil .nil <|
    .letOp (.mark "s11") .nil .nil <|
    .letOp (.exec (.indexMod)) (.cons (.there .here) (.cons .here .nil)) .nil <|
    .letOp (.mark "s13") .nil .nil <|
    .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil) .nil <|
    .letOp (.mark "s15") .nil .nil <|
    .letOp (.exec (.indexConstant 1)) .nil .nil <|
    .letOp (.mark "s16") .nil .nil <|
    .letOp (.exec (.indexEqual)) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
    .letOp (.mark "s19") .nil .nil <|
    .letOp (.branch [.vector "bls12-381.fr", .vector "bls12-381.fr"] [.vector "bls12-381.fr"]) (.cons .here (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))) (.cons (
      .ret (.cons (.there .here) .nil)) (.cons (
      .ret (.cons .here .nil)) .nil)) <|
    .ret (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)))) .nil) <|
  .ret (.cons .here .nil)

abbrev helper20Helper : Helper := ⟨"zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩

def helper20Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .index] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.loop [.vector "bls12-381.fr"] [.field "bls12-381.fr"]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) (.cons (
    .letOp (.mark "s4") .nil .nil <|
    .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
    .ret (.cons .here (.cons (.there (.there (.there .here))) .nil))) .nil) <|
  .ret (.cons .here .nil)

abbrev helper21Helper : Helper := ⟨"zkl_e7a7efcd14676d32c0e577ff1097f611a3dc84c74ecaa8bfdbebb25968971255", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩

def helper21Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .index] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper22Helper : Helper := ⟨"finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_body", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩

def helper22Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .index] [.vector "bls12-381.fr"] :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke ⟨"zkl_e7a7efcd14676d32c0e577ff1097f611a3dc84c74ecaa8bfdbebb25968971255", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper23Helper : Helper := ⟨"finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩

def helper23Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .index] [.vector "bls12-381.fr"] :=
  .letOp (.fold ⟨⟨"finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_domain", [.vector "bls12-381.fr"], "bls12-381.fr", .here, false⟩, [.vector "bls12-381.fr"], [.index], "finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper24Helper : Helper := ⟨"zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294", .local, [.vector "bls12-381.fr", .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper24Body : Region dialect [.vector "bls12-381.fr", .index, .vector "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there .here)) (.cons .here (.cons (.there .here) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper25Helper : Helper := ⟨"zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490", .local, [.vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩

def helper25Body : Region dialect [.vector "bls12-381.fr", .index] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294", .local, [.vector "bls12-381.fr", .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there (.there .here)) (.cons (.there .here) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper26Helper : Helper := ⟨"zkl_ac1d3513b06c1d4950d126f678b9482e4ca13944fc4b35442d1a33796d064b0c", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper26Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper27Helper : Helper := ⟨"finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_body", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper27Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke ⟨"zkl_ac1d3513b06c1d4950d126f678b9482e4ca13944fc4b35442d1a33796d064b0c", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper28Helper : Helper := ⟨"finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper28Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.fold ⟨⟨"finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_domain", [.vector "bls12-381.fr"], "bls12-381.fr", .here, false⟩, [.vector "bls12-381.fr"], [], "finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper29Helper : Helper := ⟨"zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper29Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper30Helper : Helper := ⟨"zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947", .local, [.vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩

def helper30Body : Region dialect [.vector "bls12-381.fr", .index] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.loop [.vector "bls12-381.fr"] [.vector "bls12-381.fr"]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) (.cons (
    .letOp (.mark "s5") .nil .nil <|
    .letOp (.invoke ⟨"zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
    .ret (.cons .here (.cons (.there (.there (.there .here))) .nil))) .nil) <|
  .ret (.cons .here .nil)

abbrev helper31Helper : Helper := ⟨"zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", .math, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def helper31Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper32Helper : Helper := ⟨"zkl_map_719dca588088f3092ef883328cfee43eccaf8ee254795a3fa9677cd3140b4af2", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper32Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.map ⟨"zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", "bls12-381.fr", [true, true, true, true]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev helper33Helper : Helper := ⟨"zkl_3a99bc0fa1dab7cb27c9ec80754c3782b0a32e76ddc961a50e12c24c6cbff683", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩

def helper33Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"s3h676b7212h706f7765725f6f665f74776f", .local, [.index], [.index]⟩) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490", .local, [.vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke ⟨"zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947", .local, [.vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s14") .nil .nil <|
  .letOp (.loop [.vector "bls12-381.fr"] [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .vector "bls12-381.fr", .vector "bls12-381.fr"]) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))))))) (.cons (
    .letOp (.mark "s15") .nil .nil <|
    .letOp (.invoke ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
    .letOp (.mark "s17") .nil .nil <|
    .letOp (.invoke ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
    .letOp (.mark "s19") .nil .nil <|
    .letOp (.invoke ⟨"zkl_map_719dca588088f3092ef883328cfee43eccaf8ee254795a3fa9677cd3140b4af2", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))) .nil <|
    .letOp (.mark "s20") .nil .nil <|
    .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
    .letOp (.mark "s21") .nil .nil <|
    .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
    .ret (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil))))))) .nil) <|
  .ret (.cons .here .nil)

abbrev helper34Helper : Helper := ⟨"zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .index, .index], [.vector "bls12-381.fr"]⟩

def helper34Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .index, .index] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.indexSub)) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.indexSub)) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s10") .nil .nil <|
  .letOp (.loop [.vector "bls12-381.fr", .index] [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index]) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)))))))) (.cons (
    .letOp (.mark "s11") .nil .nil <|
    .letOp (.exec (.indexConstant 1)) .nil .nil <|
    .letOp (.mark "s12") .nil .nil <|
    .letOp (.exec (.indexSub)) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
    .letOp (.mark "s14") .nil .nil <|
    .letOp (.invoke ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))) .nil <|
    .letOp (.mark "s15") .nil .nil <|
    .letOp (.invoke ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))) .nil <|
    .letOp (.mark "s16") .nil .nil <|
    .letOp (.invoke ⟨"zkl_3a99bc0fa1dab7cb27c9ec80754c3782b0a32e76ddc961a50e12c24c6cbff683", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)))) .nil <|
    .ret (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil))))))) .nil) <|
  .ret (.cons .here .nil)

abbrev helper35Helper : Helper := ⟨"zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59", .local, [.vector "bls12-381.fr", .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper35Body : Region dialect [.vector "bls12-381.fr", .index, .vector "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩) (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here .nil))) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke ⟨"zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper36Helper : Helper := ⟨"zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"]⟩

def helper36Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index] [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"s3h676b7212h706f7765725f6f665f74776f", .local, [.index], [.index]⟩) (.cons (.there (.there (.there (.there .here)))) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.indexAdd)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.exec (.indexAdd)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.invoke ⟨"zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59", .local, [.vector "bls12-381.fr", .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.invoke ⟨"zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59", .local, [.vector "bls12-381.fr", .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.invoke ⟨"zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490", .local, [.vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.invoke ⟨"zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947", .local, [.vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .ret (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))))

abbrev helper37Helper : Helper := ⟨"zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b", .math, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def helper37Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper38Helper : Helper := ⟨"zkl_map_c924eca691a9f196c01671f2b9eb9f861c0eea9093f77c8c7fbeabb112d1de13", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper38Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.map ⟨"zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b", "bls12-381.fr", [true, true, true, true, true, true, true, true]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))))) .nil <|
  .ret (.cons .here .nil)

abbrev helper39Helper : Helper := ⟨"zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229", .math, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def helper39Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldSubtract "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper40Helper : Helper := ⟨"zkl_realization_4077daa8d30ef9f9ed0f8a89f7e3c731a33fa91da5e56301c22d3f8aab9de4bb", .local, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def helper40Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.invoke ⟨"zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229", .math, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper41Helper : Helper := ⟨"zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"]⟩

def helper41Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"] [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil <|
  .letOp (.mark "s10") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil) .nil <|
  .letOp (.mark "s16") .nil .nil <|
  .letOp (.invoke ⟨"zkl_map_719dca588088f3092ef883328cfee43eccaf8ee254795a3fa9677cd3140b4af2", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) (.cons .here .nil)))) .nil <|
  .letOp (.mark "s17") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s23") .nil .nil <|
  .letOp (.invoke ⟨"zkl_map_719dca588088f3092ef883328cfee43eccaf8ee254795a3fa9677cd3140b4af2", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .letOp (.mark "s24") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s34") .nil .nil <|
  .letOp (.invoke ⟨"zkl_map_c924eca691a9f196c01671f2b9eb9f861c0eea9093f77c8c7fbeabb112d1de13", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))))) .nil <|
  .letOp (.mark "s35") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s37") .nil .nil <|
  .letOp (.invoke ⟨"zkl_realization_4077daa8d30ef9f9ed0f8a89f7e3c731a33fa91da5e56301c22d3f8aab9de4bb", .local, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) (.cons .here .nil))) .nil <|
  .ret (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here (.cons (.there .here) .nil)))

abbrev helper42Helper : Helper := ⟨"zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", .math, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def helper42Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper43Helper : Helper := ⟨"zkl_map_edb5f34dbd23ff8b57cd7b37e753ccde76d52d6618e6bfdb20588d98190970ae", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper43Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.map ⟨"zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", "bls12-381.fr", [true, true, false]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper44Helper : Helper := ⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper44Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke ⟨"zkl_map_edb5f34dbd23ff8b57cd7b37e753ccde76d52d6618e6bfdb20588d98190970ae", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper45Helper : Helper := ⟨"zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"]⟩

def helper45Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"] :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke ⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke ⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke ⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.invoke ⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .ret (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))))

abbrev helper46Helper : Helper := ⟨"zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137", .math, [], [.field "bls12-381.fr"]⟩

def helper46Body : Region dialect [] [.field "bls12-381.fr"] :=
  .letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil <|
  .ret (.cons .here .nil)

abbrev helper47Helper : Helper := ⟨"zkl_realization_14cec027168c52ac1086393ae6a515357a9adb06fc866ff0c51d28e0a269dbeb", .local, [], [.field "bls12-381.fr"]⟩

def helper47Body : Region dialect [] [.field "bls12-381.fr"] :=
  .letOp (.invoke ⟨"zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137", .math, [], [.field "bls12-381.fr"]⟩) .nil .nil <|
  .ret (.cons .here .nil)

abbrev helper48Helper : Helper := ⟨"zkl_8184464d79b9512ca72dac4d64d1ba3d187fd1efb0b8118690b5a104ab35f351", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩

def helper48Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .index] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke ⟨"zkl_realization_14cec027168c52ac1086393ae6a515357a9adb06fc866ff0c51d28e0a269dbeb", .local, [], [.field "bls12-381.fr"]⟩) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper49Helper : Helper := ⟨"zkl_f9bc3972b3acce79409bfe72125c3b04de4dbb81a13d1dfbc918146c1354315c", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩

def helper49Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .index] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"zkl_8184464d79b9512ca72dac4d64d1ba3d187fd1efb0b8118690b5a104ab35f351", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper50Helper : Helper := ⟨"finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_body", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩

def helper50Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .index] [.vector "bls12-381.fr"] :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke ⟨"zkl_f9bc3972b3acce79409bfe72125c3b04de4dbb81a13d1dfbc918146c1354315c", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper51Helper : Helper := ⟨"finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩

def helper51Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .index] [.vector "bls12-381.fr"] :=
  .letOp (.fold ⟨⟨"finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_domain", [.vector "bls12-381.fr"], "bls12-381.fr", .here, false⟩, [.vector "bls12-381.fr"], [.index], "finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper52Helper : Helper := ⟨"zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35", .local, [.vector "bls12-381.fr", .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper52Body : Region dialect [.vector "bls12-381.fr", .index, .vector "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there .here)) (.cons .here (.cons (.there .here) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper53Helper : Helper := ⟨"zkl_09043a1369ab6c082f8534fc9d21f34f77067e68b9a4c2a907a132342ff59811", .local, [.field "bls12-381.fr", .index, .field "bls12-381.fr", .index], [.field "bls12-381.fr", .index]⟩

def helper53Body : Region dialect [.field "bls12-381.fr", .index, .field "bls12-381.fr", .index] [.field "bls12-381.fr", .index] :=
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.indexEqual)) (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.branch [.field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"]) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) (.cons (
    .ret (.cons (.there .here) .nil)) (.cons (
    .ret (.cons .here .nil)) .nil)) <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s12") .nil .nil <|
  .letOp (.exec (.indexAdd)) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there .here)) (.cons .here .nil))

abbrev helper54Helper : Helper := ⟨"finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_body", .local, [.field "bls12-381.fr", .index, .field "bls12-381.fr", .vector "bls12-381.fr", .index], [.field "bls12-381.fr", .index]⟩

def helper54Body : Region dialect [.field "bls12-381.fr", .index, .field "bls12-381.fr", .vector "bls12-381.fr", .index] [.field "bls12-381.fr", .index] :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke ⟨"zkl_09043a1369ab6c082f8534fc9d21f34f77067e68b9a4c2a907a132342ff59811", .local, [.field "bls12-381.fr", .index, .field "bls12-381.fr", .index], [.field "bls12-381.fr", .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper55Helper : Helper := ⟨"finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .index], [.field "bls12-381.fr", .index]⟩

def helper55Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .index] [.field "bls12-381.fr", .index] :=
  .letOp (.fold ⟨⟨"finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_domain", [.vector "bls12-381.fr"], "bls12-381.fr", .here, false⟩, [.field "bls12-381.fr", .index], [.index], "finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper56Helper : Helper := ⟨"zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45", .local, [.field "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.field "bls12-381.fr", .index]⟩

def helper56Body : Region dialect [.field "bls12-381.fr", .index, .index, .vector "bls12-381.fr"] [.field "bls12-381.fr", .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .index], [.field "bls12-381.fr", .index]⟩) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper57Helper : Helper := ⟨"zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [.vector "bls12-381.fr", .index], [.field "bls12-381.fr"]⟩

def helper57Body : Region dialect [.vector "bls12-381.fr", .index] [.field "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_realization_14cec027168c52ac1086393ae6a515357a9adb06fc866ff0c51d28e0a269dbeb", .local, [], [.field "bls12-381.fr"]⟩) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke ⟨"zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45", .local, [.field "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.field "bls12-381.fr", .index]⟩) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev helper58Helper : Helper := ⟨"zkl_c15efd5f24b71cb9e6e3766d00c208e0a0014177a6ae1e9dd67b23bda4eff8ab", .math, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def helper58Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper59Helper : Helper := ⟨"zkl_realization_4c0ed08d0065dbe9c7159df984d4cc2ec1f0d1a966f866deb80fc9a777a3bdd1", .local, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def helper59Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.invoke ⟨"zkl_c15efd5f24b71cb9e6e3766d00c208e0a0014177a6ae1e9dd67b23bda4eff8ab", .math, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper60Helper : Helper := ⟨"zkl_c8eacd293248ba42cad22bd955e2dec7c6105efe1dabf391c3a74b436be7412e", .math, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def helper60Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper61Helper : Helper := ⟨"zkl_map_d9eab7e54d46c5b4a26d237b77bbb92434339455eeac57a265818f2be66fa299", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper61Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.map ⟨"zkl_c8eacd293248ba42cad22bd955e2dec7c6105efe1dabf391c3a74b436be7412e", "bls12-381.fr", [true, true, false]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper62Helper : Helper := ⟨"zkl_abd6f98141af14ddf8b9152129fb3a9fb361b5735ade780e8d1c876d68deb283", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .field "bls12-381.fr", .index], [.vector "bls12-381.fr", .field "bls12-381.fr", .index]⟩

def helper62Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .field "bls12-381.fr", .index] [.vector "bls12-381.fr", .field "bls12-381.fr", .index] :=
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.exec (.indexMod)) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.exec (.indexEqual)) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.branch [.field "bls12-381.fr"] [.field "bls12-381.fr"]) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) (.cons (
    .letOp (.mark "s9") .nil .nil <|
    .letOp (.invoke ⟨"zkl_realization_14cec027168c52ac1086393ae6a515357a9adb06fc866ff0c51d28e0a269dbeb", .local, [], [.field "bls12-381.fr"]⟩) .nil .nil <|
    .ret (.cons .here .nil)) (.cons (
    .ret (.cons .here .nil)) .nil)) <|
  .letOp (.mark "s13") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s15") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s16") .nil .nil <|
  .letOp (.exec (.indexAdd)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons .here .nil)))

abbrev helper63Helper : Helper := ⟨"finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_body", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .field "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr", .field "bls12-381.fr", .index]⟩

def helper63Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .field "bls12-381.fr", .vector "bls12-381.fr", .index] [.vector "bls12-381.fr", .field "bls12-381.fr", .index] :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke ⟨"zkl_abd6f98141af14ddf8b9152129fb3a9fb361b5735ade780e8d1c876d68deb283", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .field "bls12-381.fr", .index], [.vector "bls12-381.fr", .field "bls12-381.fr", .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper64Helper : Helper := ⟨"finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .field "bls12-381.fr", .index]⟩

def helper64Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .index, .index] [.vector "bls12-381.fr", .field "bls12-381.fr", .index] :=
  .letOp (.fold ⟨⟨"finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_domain", [.vector "bls12-381.fr"], "bls12-381.fr", .here, false⟩, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.index], "finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil))))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper65Helper : Helper := ⟨"zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .field "bls12-381.fr", .index]⟩

def helper65Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .index, .vector "bls12-381.fr"] [.vector "bls12-381.fr", .field "bls12-381.fr", .index] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .field "bls12-381.fr", .index]⟩) (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper66Helper : Helper := ⟨"zkl_3d3958243128671a7ae06c730aba5c78b4cae61932510ab43ba5bcabe7324295", .local, [.vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩

def helper66Body : Region dialect [.vector "bls12-381.fr", .index] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke ⟨"zkl_realization_14cec027168c52ac1086393ae6a515357a9adb06fc866ff0c51d28e0a269dbeb", .local, [], [.field "bls12-381.fr"]⟩) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.invoke ⟨"zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .field "bls12-381.fr", .index]⟩) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there .here))) .nil))))) .nil <|
  .ret (.cons .here .nil)

abbrev helper67Helper : Helper := ⟨"zkl_02aa9bd9900f843069baf97f23f4f5ccab54b136c8fed5b90842e4c46b7e5fcd", .math, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def helper67Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper68Helper : Helper := ⟨"zkl_map_2789fa8a53a1844ea853e44908a95ecd4f8048c9c950e4408450082ff2a6b124", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def helper68Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.map ⟨"zkl_02aa9bd9900f843069baf97f23f4f5ccab54b136c8fed5b90842e4c46b7e5fcd", "bls12-381.fr", [true, true]⟩) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper69Helper : Helper := ⟨"zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩

def helper69Body : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.indexAdd)) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke ⟨"zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35", .local, [.vector "bls12-381.fr", .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s13") .nil .nil <|
  .letOp (.loop [.vector "bls12-381.fr", .index] [.vector "bls12-381.fr", .vector "bls12-381.fr", .index]) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there .here)) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there .here)))) .nil))))))) (.cons (
    .letOp (.mark "s14") .nil .nil <|
    .letOp (.invoke ⟨"zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [.vector "bls12-381.fr", .index], [.field "bls12-381.fr"]⟩) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)) .nil <|
    .letOp (.mark "s16") .nil .nil <|
    .letOp (.invoke ⟨"zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [.vector "bls12-381.fr", .index], [.field "bls12-381.fr"]⟩) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there .here))) .nil)) .nil <|
    .letOp (.mark "s18") .nil .nil <|
    .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there .here))) .nil) .nil <|
    .letOp (.mark "s22") .nil .nil <|
    .letOp (.invoke ⟨"zkl_map_edb5f34dbd23ff8b57cd7b37e753ccde76d52d6618e6bfdb20588d98190970ae", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) .nil <|
    .letOp (.mark "s26") .nil .nil <|
    .letOp (.invoke ⟨"zkl_realization_4c0ed08d0065dbe9c7159df984d4cc2ec1f0d1a966f866deb80fc9a777a3bdd1", .local, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
    .letOp (.mark "s27") .nil .nil <|
    .letOp (.invoke ⟨"zkl_map_d9eab7e54d46c5b4a26d237b77bbb92434339455eeac57a265818f2be66fa299", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons .here .nil))) .nil <|
    .letOp (.mark "s29") .nil .nil <|
    .letOp (.invoke ⟨"zkl_3d3958243128671a7ae06c730aba5c78b4cae61932510ab43ba5bcabe7324295", .local, [.vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)) .nil <|
    .letOp (.mark "s30") .nil .nil <|
    .letOp (.invoke ⟨"zkl_map_2789fa8a53a1844ea853e44908a95ecd4f8048c9c950e4408450082ff2a6b124", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
    .letOp (.mark "s32") .nil .nil <|
    .letOp (.exec (.indexConstant 1)) .nil .nil <|
    .letOp (.mark "s33") .nil .nil <|
    .letOp (.exec (.indexAdd)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons .here .nil)) .nil <|
    .ret (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) .nil)))))) .nil) <|
  .ret (.cons .here .nil)

abbrev helper70Helper : Helper := ⟨"zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47", .local, [.vector "bls12-381.fr", .index], [.field "bls12-381.fr"]⟩

def helper70Body : Region dialect [.vector "bls12-381.fr", .index] [.field "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.indexAdd)) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [.vector "bls12-381.fr", .index], [.field "bls12-381.fr"]⟩) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev sumHelper : Helper := ⟨"zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216", .local, [.vector "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def sumBody : Region dialect [.vector "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

abbrev evaluateWiringHelper : Helper := ⟨"zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def evaluateWiringBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexAdd)) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.exec (.indexAdd)) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.invoke ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr", .index, .index]⟩) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.invoke ⟨"zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)))) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.invoke ⟨"zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)))) .nil <|
  .letOp (.mark "s10") .nil .nil <|
  .letOp (.invoke ⟨"zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], [.vector "bls12-381.fr", .index, .index]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) .nil)))) .nil <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.invoke ⟨"zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s12") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

abbrev helper73Helper : Helper := ⟨"zkl_82e44b33934fd674fa24fbb7f5705f2364f5020774fe25318dd2b968f9d001e4", .math, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩

def helper73Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there .here)) (.cons (.there .here) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

abbrev helper74Helper : Helper := ⟨"zkl_realization_9d43c4097a4ca91587f8171ca54eb555a11f0224b2da4a4febb9a659c3539adc", .local, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩

def helper74Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.invoke ⟨"zkl_82e44b33934fd674fa24fbb7f5705f2364f5020774fe25318dd2b968f9d001e4", .math, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper75Helper : Helper := ⟨"zkl_bcbdb252ffc9abd0563757a6a45f0dccb9a7c345ecbfb58b787c5137455bd42e", .local, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩

def helper75Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke ⟨"zkl_realization_9d43c4097a4ca91587f8171ca54eb555a11f0224b2da4a4febb9a659c3539adc", .local, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper76Helper : Helper := ⟨"zkl_acc5a50f3a300b126874f48e782cbb903e9f900ea776915474c16f8e7ecd49b5", .math, [], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩

def helper76Body : Region dialect [] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil <|
  .letOp (.fieldConstant "bls12-381.fr" 1) .nil .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

abbrev helper77Helper : Helper := ⟨"zkl_realization_c5fb2e31298efb8b038a412e95023e803291096e10c504b0be65251ace3e142d", .local, [], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩

def helper77Body : Region dialect [] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.invoke ⟨"zkl_acc5a50f3a300b126874f48e782cbb903e9f900ea776915474c16f8e7ecd49b5", .math, [], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩) .nil .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper78Helper : Helper := ⟨"finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body", .local, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩

def helper78Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke ⟨"zkl_bcbdb252ffc9abd0563757a6a45f0dccb9a7c345ecbfb58b787c5137455bd42e", .local, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper79Helper : Helper := ⟨"finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩

def helper79Body : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.fold ⟨⟨"finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_domain", [.vector "bls12-381.fr"], "bls12-381.fr", .here, false⟩, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"], "finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper80Helper : Helper := ⟨"zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d", .local, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩

def helper80Body : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr"] [.field "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev evaluateCoefficientsHelper : Helper := ⟨"zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

def evaluateCoefficientsBody : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_realization_c5fb2e31298efb8b038a412e95023e803291096e10c504b0be65251ace3e142d", .local, [], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke ⟨"zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d", .local, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev linePointHelper : Helper := ⟨"zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

def linePointBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_map_edb5f34dbd23ff8b57cd7b37e753ccde76d52d6618e6bfdb20588d98190970ae", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

def roundsSignature : ProtocolSignature := ⟨"zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", ["role00000000", "role00000001"], [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"], [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [[0], [0], [0], [0], [1], [0, 1], [1]], [[0], [0], [0], [0], [0], [1], [1]]⟩

def roundsBody : Region protocolDialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"] [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.localCall ⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [.vector "bls12-381.fr"]⟩ rfl 0 "s1") .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.localCall ⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [.vector "bls12-381.fr"]⟩ rfl 1 "s3") .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.repeat ⟨[.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.service "random.bls12-381.fr/0"], [0, 1], [[0], [0], [0], [0], [0], [1], [1]], 4⟩ "s6") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))))))))) (.cons (
    .letOp (.mark "s7") .nil .nil <|
    .letOp (.localCall ⟨"zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"], [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"]⟩ rfl 0 "s7") (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)))) .nil <|
    .letOp (.mark "label_726f756e64_0") .nil .nil <|
    .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_0") (.cons .here .nil) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
    .letOp (.mark "label_726f756e64_1") .nil .nil <|
    .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_1") (.cons (.there (.there (.there .here))) .nil) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
    .letOp (.mark "label_726f756e64_2") .nil .nil <|
    .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_2") (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldEqual "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.cons .here .nil)) .nil <|
    .letOp (.mark "s18") .nil .nil <|
    .letOp (.guard 1 "s18") (.cons .here .nil) .nil <|
    .letOp (.mark "label_6368616c6c656e6765") .nil .nil <|
    .letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) .nil) .nil <|
    .letOp (.mark "label_64656c6976657279_0") .nil .nil <|
    .letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons .here .nil) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil <|
    .letOp (.mark "s23") .nil .nil <|
    .letOp (.localCall ⟨"zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"]⟩ rfl 0 "s23") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons .here .nil))))) .nil <|
    .letOp (.mark "s25") .nil .nil <|
    .letOp (.localCall ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩ rfl 0 "s25") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
    .letOp (.mark "s27") .nil .nil <|
    .letOp (.localCall ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩ rfl 1 "s27") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil)) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) (.cons .here .nil)) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons .here .nil)) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons .here .nil)) .nil <|
    .ret (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)))))))) .nil) <|
  .ret (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))))))

def gkrSignature : ProtocolSignature := ⟨"zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2", ["role00000000", "role00000001"], [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .index, .service "random.bls12-381.fr/0"], [.boolean], [[0, 1], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [1]], [[1]]⟩

def gkrBody : Region protocolDialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .index, .service "random.bls12-381.fr/0"] [.boolean] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall ⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [.vector "bls12-381.fr"]⟩ rfl 1 "s0") .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.localCall ⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [.vector "bls12-381.fr"]⟩ rfl 0 "s2") .nil .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.repeat ⟨[.vector "bls12-381.fr", .vector "bls12-381.fr"], [.service "random.bls12-381.fr/0"], [0, 1], [[1], [0]], 4⟩ "s4") (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)))) (.cons (
    .letOp (.mark "label_6f7574707574") .nil .nil <|
    .letOp (.draw 1 "bls12-381.fr" "label_6f7574707574") (.cons (.there (.there (.there .here))) .nil) .nil <|
    .letOp (.mark "label_6f75747075745f64656c6976657279_0") .nil .nil <|
    .letOp (.exchange (.field "bls12-381.fr") 1 0 "label_6f75747075745f64656c6976657279_0") (.cons .here .nil) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil <|
    .letOp (.mark "s9") .nil .nil <|
    .letOp (.localCall ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩ rfl 1 "s9") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) .nil)) .nil <|
    .letOp (.mark "s11") .nil .nil <|
    .letOp (.localCall ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩ rfl 0 "s11") (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there .here) .nil)) .nil <|
    .ret (.cons (.there .here) (.cons .here .nil))) .nil) <|
  .letOp (.mark "s15") .nil .nil <|
  .letOp (.localCall ⟨"zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr"], [.field "bls12-381.fr"]⟩ rfl 1 "s15") (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s23") .nil .nil <|
  .letOp (.repeat ⟨[.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .index, .service "random.bls12-381.fr/0"], [0, 1], [[1], [0], [1]], 4⟩ "s23") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil))))))))))) (.cons (
    .letOp (.mark "s24") .nil .nil <|
    .letOp (.localCall ⟨"zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .index, .index], [.vector "bls12-381.fr"]⟩ rfl 0 "s24") (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons .here .nil))))))) .nil <|
    .letOp (.mark "s26") .nil .nil <|
    .letOp (.localCall ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩ rfl 0 "s26") (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil))) .nil <|
    .letOp (.mark "s27") .nil .nil <|
    .letOp (.localCall ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩ rfl 0 "s27") (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil))) .nil <|
    .letOp (.mark "s28") .nil .nil <|
    .letOp (.localCall ⟨"zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"]⟩ rfl 0 "s28") (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil))))) .nil <|
    .letOp (.mark "label_6c656674") .nil .nil <|
    .letOp (.protocolApply ⟨"zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", ["role00000000", "role00000001"], [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"], [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [[0], [0], [0], [0], [1], [0, 1], [1]], [[0], [0], [0], [0], [0], [1], [1]]⟩ [0, 1] "label_6c656674") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) .nil))))))) .nil <|
    .letOp (.mark "label_7269676874") .nil .nil <|
    .letOp (.protocolApply ⟨"zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", ["role00000000", "role00000001"], [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"], [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [[0], [0], [0], [0], [1], [0, 1], [1]], [[0], [0], [0], [0], [0], [1], [1]]⟩ [0, 1] "label_7269676874") (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))) .nil))))))) .nil <|
    .letOp (.mark "s38") .nil .nil <|
    .letOp (.localCall ⟨"zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index], [.vector "bls12-381.fr"]⟩ rfl 0 "s38") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))) .nil)))) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.indexConstant 0) rfl) .nil .nil <|
    .letOp (.mark "s41") .nil .nil <|
    .letOp (.localCall ⟨"zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [.vector "bls12-381.fr", .index], [.field "bls12-381.fr"]⟩ rfl 0 "s41") (.cons (.there .here) (.cons .here .nil)) .nil <|
    .letOp (.mark "label_6c696e655f636f6e7374616e74_0") .nil .nil <|
    .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_6c696e655f636f6e7374616e74_0") (.cons .here .nil) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
    .letOp (.mark "s44") .nil .nil <|
    .letOp (.localCall ⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [.vector "bls12-381.fr"]⟩ rfl 1 "s44") .nil .nil <|
    .letOp (.mark "s45") .nil .nil <|
    .letOp (.localCall ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩ rfl 1 "s45") (.cons .here (.cons (.there .here) .nil)) .nil <|
    .letOp (.mark "s48") .nil .nil <|
    .letOp (.repeat ⟨[.vector "bls12-381.fr"], [.vector "bls12-381.fr"], [0, 1], [[1]], 4⟩ "s48") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))) (.cons (
      .letOp (.mark "s49") .nil .nil <|
      .letOp (.localCall ⟨"zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47", .local, [.vector "bls12-381.fr", .index], [.field "bls12-381.fr"]⟩ rfl 0 "s49") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
      .letOp (.mark "label_6c696e655f636f656666696369656e74_0") .nil .nil <|
      .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_6c696e655f636f656666696369656e74_0") (.cons .here .nil) .nil <|
      .letOp (.mark "") .nil .nil <|
      .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
      .letOp (.mark "s52") .nil .nil <|
      .letOp (.localCall ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩ rfl 1 "s52") (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
      .ret (.cons .here .nil)) .nil) <|
    .letOp (.mark "s56") .nil .nil <|
    .letOp (.localCall ⟨"zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216", .local, [.vector "bls12-381.fr"], [.field "bls12-381.fr"]⟩ rfl 1 "s56") (.cons .here .nil) .nil <|
    .letOp (.mark "s58") .nil .nil <|
    .letOp (.localCall ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩ rfl 1 "s58") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))) .nil))) .nil <|
    .letOp (.mark "s61") .nil .nil <|
    .letOp (.localCall ⟨"zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"], [.field "bls12-381.fr"]⟩ rfl 1 "s61") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil)))) .nil <|
    .letOp (.mark "s63") .nil .nil <|
    .letOp (.localCall ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [.vector "bls12-381.fr", .index, .index], [.vector "bls12-381.fr"]⟩ rfl 1 "s63") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))))) .nil))) .nil <|
    .letOp (.mark "s66") .nil .nil <|
    .letOp (.localCall ⟨"zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr"], [.field "bls12-381.fr"]⟩ rfl 1 "s66") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) .nil)))) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.calculate (.fieldEqual "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))) (.cons .here .nil)) .nil <|
    .letOp (.mark "s75") .nil .nil <|
    .letOp (.guard 1 "s75") (.cons .here .nil) .nil <|
    .letOp (.mark "label_6c696e655f6368616c6c656e6765") .nil .nil <|
    .letOp (.draw 1 "bls12-381.fr" "label_6c696e655f6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))))))))))))))) .nil) .nil <|
    .letOp (.mark "label_6c696e655f64656c6976657279_0") .nil .nil <|
    .letOp (.exchange (.field "bls12-381.fr") 1 0 "label_6c696e655f64656c6976657279_0") (.cons .here .nil) .nil <|
    .letOp (.mark "") .nil .nil <|
    .letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil <|
    .letOp (.mark "s80") .nil .nil <|
    .letOp (.localCall ⟨"zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7", .local, [.vector "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩ rfl 1 "s80") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons (.there (.there .here)) .nil)) .nil <|
    .letOp (.mark "s84") .nil .nil <|
    .letOp (.localCall ⟨"zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩ rfl 1 "s84") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))) (.cons (.there (.there (.there .here))) .nil))) .nil <|
    .letOp (.mark "s86") .nil .nil <|
    .letOp (.localCall ⟨"zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩ rfl 0 "s86") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))) (.cons (.there (.there .here)) .nil))) .nil <|
    .ret (.cons (.there .here) (.cons .here (.cons (.there (.there .here)) .nil)))) .nil) <|
  .letOp (.mark "s90") .nil .nil <|
  .letOp (.localCall ⟨"zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr"], [.field "bls12-381.fr"]⟩ rfl 1 "s90") (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldEqual "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Structured.GkrSourceBodies
