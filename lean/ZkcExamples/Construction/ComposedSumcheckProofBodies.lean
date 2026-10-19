module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`ZkcExamples.Construction.ComposedSumcheckProofData`. -/
namespace ZkcExamples.Construction.ComposedSumcheckProofBodies
open Zkc.Source Zkc.Source.Structured

abbrev helper0Helper : Helper :=
  ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩

def helper0Body : Region dialect helper0Helper.inputs helper0Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec .indexLess) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper1Helper : Helper :=
  ⟨"s3h7a6b6311h6d756c74696c696e6561724h726f7773", .local, [.index], [.index]⟩

def helper1Body : Region dialect helper1Helper.inputs helper1Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 64)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke {name := "s3h7a6b637h696e64696365734h6c657373", kind := .local, inputs := [.index, .index], outputs := [.boolean]}) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s2_reject") .nil .nil (.stop PIR.Stop.reject)) .nil)) <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.loop [.index] []) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil))) (.cons (.letOp (.mark "s7") .nil .nil (.letOp (.exec (.indexConstant 2)) .nil .nil (.letOp (.mark "s8") .nil .nil (.letOp (.exec .indexMul) (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) .nil) <|
  .ret (.cons .here .nil)

abbrev helper2Helper : Helper :=
  ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean]⟩

def helper2Body : Region dialect helper2Helper.inputs helper2Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke {name := "s3h7a6b637h696e64696365734h6c657373", kind := .local, inputs := [.index, .index], outputs := [.boolean]}) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.branch [.index] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) .nil)) (.cons (.letOp (.mark "s4") .nil .nil (.letOp (.exec (.indexConstant 64)) .nil .nil (.letOp (.mark "s5") .nil .nil (.letOp (.invoke {name := "s3h7a6b637h696e64696365734h6c657373", kind := .local, inputs := [.index, .index], outputs := [.boolean]}) (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) (.cons (.letOp (.mark "s7") .nil .nil (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil)))) .nil)) <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.branch [.vector "bls12-381.fr", .index] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) (.cons (.letOp (.mark "s12") .nil .nil (.letOp (.exec (.vectorLength "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s13") .nil .nil (.letOp (.exec .indexMod) (.cons .here (.cons (.there (.there .here)) .nil)) .nil (.letOp (.mark "s14") .nil .nil (.letOp (.exec (.indexConstant 0)) .nil .nil (.letOp (.mark "s15") .nil .nil (.letOp (.exec .indexEqual) (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))))))) (.cons (.letOp (.mark "s17") .nil .nil (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil)))) .nil)) <|
  .letOp (.mark "s22") .nil .nil <|
  .letOp (.branch [.vector "bls12-381.fr", .index, .index] [.boolean]) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) (.cons (.letOp (.mark "s23") .nil .nil (.letOp (.exec (.vectorLength "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s24") .nil .nil (.letOp (.exec .indexDiv) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.mark "s25") .nil .nil (.letOp (.invoke {name := "s3h7a6b6311h6d756c74696c696e6561724h726f7773", kind := .local, inputs := [.index], outputs := [.index]}) (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.mark "s26") .nil .nil (.letOp (.exec .indexEqual) (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))))))) (.cons (.letOp (.mark "s28") .nil .nil (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil)))) .nil)) <|
  .ret (.cons .here .nil)

abbrev helper3Helper : Helper :=
  ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper3Body : Region dialect helper3Helper.inputs helper3Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke {name := "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.boolean]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s1_reject") .nil .nil (.stop PIR.Stop.reject)) .nil)) <|
  .ret (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))

abbrev helper4Helper : Helper :=
  ⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩

def helper4Body : Region dialect helper4Helper.inputs helper4Helper.outputs :=
  .ret (.cons .here .nil)

abbrev helper5Helper : Helper :=
  ⟨"zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩

def helper5Body : Region dialect helper5Helper.inputs helper5Helper.outputs :=
  .letOp (.invoke {name := "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", kind := .math, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.vector "bls12-381.fr"]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper6Helper : Helper :=
  ⟨"zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper6Body : Region dialect helper6Helper.inputs helper6Helper.outputs :=
  .letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper7Helper : Helper :=
  ⟨"finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper7Body : Region dialect helper7Helper.inputs helper7Helper.outputs :=
  .letOp (.invoke {name := "zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", kind := .math, inputs := [.field "bls12-381.fr", .field "bls12-381.fr"], outputs := [.field "bls12-381.fr"]}) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper8Helper : Helper :=
  ⟨"zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", .math, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper8Body : Region dialect helper8Helper.inputs helper8Helper.outputs :=
  .letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil <|
  .letOp (.fold {domain := {name := "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain", inputs := [.vector "bls12-381.fr"], field := "bls12-381.fr", container := .here, indices := false}, state := [.field "bls12-381.fr"], captures := [], step := "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", predicate := "", kind := .math}) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev formulaHelper : Helper :=
  ⟨"zkf_654a0e58b11e83f398996b9e830df00890bec0f8dc08a65c5750d6d9c759b643", .math, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [.boolean]⟩

def formulaBody : Region dialect formulaHelper.inputs formulaHelper.outputs :=
  .letOp (.invoke {name := "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", kind := .math, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.vector "bls12-381.fr"]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.invoke {name := "zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", kind := .math, inputs := [.vector "bls12-381.fr"], outputs := [.field "bls12-381.fr"]}) (.cons .here .nil) .nil <|
  .letOp (.fieldEqual "bls12-381.fr") (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper10Helper : Helper :=
  ⟨"zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩

def helper10Body : Region dialect helper10Helper.inputs helper10Helper.outputs :=
  .ret (.cons (.there (.there .here)) .nil)

abbrev helper11Helper : Helper :=
  ⟨"zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩

def helper11Body : Region dialect helper11Helper.inputs helper11Helper.outputs :=
  .ret (.cons (.there .here) .nil)

abbrev helper12Helper : Helper :=
  ⟨"zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46", .local, [], [(.vector "bls12-381.fr")]⟩

def helper12Body : Region dialect helper12Helper.inputs helper12Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .ret (.cons .here .nil)

abbrev helper13Helper : Helper :=
  ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩

def helper13Body : Region dialect helper13Helper.inputs helper13Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke {name := "s3h7a6b637h696e64696365734h6c657373", kind := .local, inputs := [.index, .index], outputs := [.boolean]}) (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s3_reject") .nil .nil (.stop PIR.Stop.reject)) .nil)) <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there .here)) .nil) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper14Helper : Helper :=
  ⟨"zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", .local, [(.vector "bls12-381.fr"), .index, .index], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def helper14Body : Region dialect helper14Helper.inputs helper14Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke {name := "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.vector "bls12-381.fr", .vector "bls12-381.fr"]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons (.there (.there .here)) .nil) .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

abbrev helper15Helper : Helper :=
  ⟨"zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper15Body : Region dialect helper15Helper.inputs helper15Helper.outputs :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper16Helper : Helper :=
  ⟨"zkl_map_7aa10c0d106e0082840e035854d97e34de85744d05e64191205f7ada5a3efd95", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def helper16Body : Region dialect helper16Helper.inputs helper16Helper.outputs :=
  .letOp (.map {helperName := "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", field := "bls12-381.fr", rowwise := [true, true, false]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper17Helper : Helper :=
  ⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper17Body : Region dialect helper17Helper.inputs helper17Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke {name := "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.vector "bls12-381.fr", .vector "bls12-381.fr"]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke {name := "zkl_map_7aa10c0d106e0082840e035854d97e34de85744d05e64191205f7ada5a3efd95", kind := .local, inputs := [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], outputs := [.vector "bls12-381.fr"]}) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.exec .indexSub) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))

abbrev helper18Helper : Helper :=
  ⟨"zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def helper18Body : Region dialect helper18Helper.inputs helper18Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper19Helper : Helper :=
  ⟨"zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper19Body : Region dialect helper19Helper.inputs helper19Helper.outputs :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke {name := "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], outputs := [.vector "bls12-381.fr", .index, .index]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper20Helper : Helper :=
  ⟨"finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper20Body : Region dialect helper20Helper.inputs helper20Helper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke {name := "zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], outputs := [.vector "bls12-381.fr", .index, .index]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper21Helper : Helper :=
  ⟨"finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper21Body : Region dialect helper21Helper.inputs helper21Helper.outputs :=
  .letOp (.fold {domain := {name := "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain", inputs := [.vector "bls12-381.fr"], field := "bls12-381.fr", container := .here, indices := false}, state := [.vector "bls12-381.fr", .index, .index], captures := [], step := "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", predicate := "", kind := .local}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper22Helper : Helper :=
  ⟨"zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper22Body : Region dialect helper22Helper.inputs helper22Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke {name := "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0", kind := .local, inputs := [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index], outputs := [.vector "bls12-381.fr", .index, .index]}) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper23Helper : Helper :=
  ⟨"zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper23Body : Region dialect helper23Helper.inputs helper23Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke {name := "zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], outputs := [.vector "bls12-381.fr", .index, .index]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper24Helper : Helper :=
  ⟨"zkl_3b67bb5451d0deeed7ab9379c12e7c154a5c16946b7db9b65bc0d4be6b613f1d", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩

def helper24Body : Region dialect helper24Helper.inputs helper24Helper.outputs :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke {name := "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.vector "bls12-381.fr", .index, .index]}) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.invoke {name := "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"], outputs := [.vector "bls12-381.fr", .index, .index]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.invoke {name := "zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.vector "bls12-381.fr"]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.exec (.fieldEqual "bls12-381.fr")) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper25Helper : Helper :=
  ⟨"zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩

def helper25Body : Region dialect helper25Helper.inputs helper25Helper.outputs :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke {name := "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.boolean]}) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.branch [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))) (.cons (.letOp (.mark "s7") .nil .nil (.letOp (.invoke {name := "zkl_3b67bb5451d0deeed7ab9379c12e7c154a5c16946b7db9b65bc0d4be6b613f1d", kind := .local, inputs := [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], outputs := [.boolean]}) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil (.ret (.cons .here .nil)))) (.cons (.letOp (.mark "s9") .nil .nil (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil)))) .nil)) <|
  .ret (.cons .here .nil)

abbrev helper26Helper : Helper :=
  ⟨"s3h7a6b637h626f6f6c65616e4h626f7468", .math, [.boolean, .boolean], [.boolean]⟩

def helper26Body : Region dialect helper26Helper.inputs helper26Helper.outputs :=
  .letOp .booleanAnd (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

def protocol0Signature : ProtocolSignature where
  name := "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]
  outputs := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")]
  inputScopes := [[0], [0], [0], [1], [0, 1], [1]]
  outputScopes := [[0], [0], [0], [0], [1], [1]]

def protocol0Body : Region protocolDialect protocol0Signature.inputs protocol0Signature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke {name := "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", kind := .math, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.index]}) rfl) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.guard 0 "s3") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke {name := "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", kind := .math, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.index]}) rfl) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.localCall {name := "s3h7a6b637h696e64696365734h6c657373", kind := .local, inputs := [.index, .index], outputs := [.boolean]} rfl 0 "s5") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanConstant false) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .booleanEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.guard 0 "s8") (.cons .here .nil) .nil <|
  .letOp (.mark "s10") .nil .nil <|
  .letOp (.localCall {name := "zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46", kind := .local, inputs := [], outputs := [.vector "bls12-381.fr"]} rfl 0 "s10") .nil .nil <|
  .letOp (.mark "s12") .nil .nil <|
  .letOp (.localCall {name := "zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46", kind := .local, inputs := [], outputs := [.vector "bls12-381.fr"]} rfl 1 "s12") .nil .nil <|
  .letOp (.mark "s15") .nil .nil <|
  .letOp (.repeat {state := [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], captures := [.service "random.bls12-381.fr/0"], roles := [0, 1], stateScopes := [[0], [0], [0], [0], [1], [1]], maximum := 4} "s15") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)))))))) (.cons (.letOp (.mark "s16") .nil .nil (.letOp (.localCall {name := "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.field "bls12-381.fr", .field "bls12-381.fr"]} rfl 0 "s16") (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))) .nil (.letOp (.mark "label_726f756e64_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil (.letOp (.mark "label_726f756e64_1") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_1") (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldEqual "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons .here .nil)) .nil (.letOp (.mark "s24") .nil .nil (.letOp (.guard 1 "s24") (.cons .here .nil) .nil (.letOp (.mark "label_6368616c6c656e6765") .nil .nil (.letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil) .nil (.letOp (.mark "label_64656c6976657279_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil (.letOp (.mark "s29") .nil .nil (.letOp (.localCall {name := "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"], outputs := [.vector "bls12-381.fr", .index, .index]} rfl 0 "s29") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons .here .nil)))) .nil (.letOp (.mark "s31") .nil .nil (.letOp (.localCall {name := "zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58", kind := .local, inputs := [.vector "bls12-381.fr", .field "bls12-381.fr"], outputs := [.vector "bls12-381.fr"]} rfl 0 "s31") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.mark "s33") .nil .nil (.letOp (.localCall {name := "zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58", kind := .local, inputs := [.vector "bls12-381.fr", .field "bls12-381.fr"], outputs := [.vector "bls12-381.fr"]} rfl 1 "s33") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldConstant "bls12-381.fr" 1) rfl) .nil .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldSubtract "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil))))))))))))))))))))))))))))))))))))))))))))) .nil) <|
  .ret (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))))))

def proofSignature : ProtocolSignature where
  name := "zkl_441c117f8000119f8eafff882ba0eaa7842ce440e5d97bb64e08f51893894e2d"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]
  outputs := [.boolean]
  inputScopes := [[0, 1], [0, 1], [1], [1], [0, 1], [1]]
  outputScopes := [[1]]

def proofBody : Region protocolDialect proofSignature.inputs proofSignature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.localCall {name := "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.vector "bls12-381.fr", .index, .index]} rfl 0 "s1") (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil))) .nil <|
  .letOp (.mark "label_6c656674") .nil .nil <|
  .letOp (.protocolApply {name := "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", roles := ["role00000000", "role00000001"], inputs := [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"], outputs := [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"], inputScopes := [[0], [0], [0], [1], [0, 1], [1]], outputScopes := [[0], [0], [0], [0], [1], [1]]} [0, 1] "label_6c656674") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)))))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.localCall {name := "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", kind := .local, inputs := [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], outputs := [.boolean]} rfl 1 "s7") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "s10") .nil .nil <|
  .letOp (.localCall {name := "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", kind := .local, inputs := [.vector "bls12-381.fr", .index, .index], outputs := [.vector "bls12-381.fr", .index, .index]} rfl 0 "s10") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) (.cons .here .nil))) .nil <|
  .letOp (.mark "label_7269676874") .nil .nil <|
  .letOp (.protocolApply {name := "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", roles := ["role00000000", "role00000001"], inputs := [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"], outputs := [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"], inputScopes := [[0], [0], [0], [1], [0, 1], [1]], outputScopes := [[0], [0], [0], [0], [1], [1]]} [0, 1] "label_7269676874") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) .nil)))))) .nil <|
  .letOp (.mark "s16") .nil .nil <|
  .letOp (.localCall {name := "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", kind := .local, inputs := [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], outputs := [.boolean]} rfl 1 "s16") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke {name := "s3h7a6b637h626f6f6c65616e4h626f7468", kind := .math, inputs := [.boolean, .boolean], outputs := [.boolean]}) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Construction.ComposedSumcheckProofBodies
