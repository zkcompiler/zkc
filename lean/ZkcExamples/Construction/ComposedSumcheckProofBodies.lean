module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`ZkcExamples.Construction.ComposedSumcheckProofData`. -/
namespace ZkcExamples.Construction.ComposedSumcheckProofBodies
open Zkc.Source Zkc.Source.Structured

abbrev helper0Helper : Helper :=
  ⟨"zkf_6e9c627b6b78d36775361ea67f9564ea93304d9439a8efd5a13c4285a6774caa", .math, [(.vector "bls12-381.fr"), .index], [.boolean]⟩

def helper0Body : Region dialect helper0Helper.inputs helper0Helper.outputs :=
  .letOp (.vectorLength "bls12-381.fr") (.cons .here .nil) .nil <|
  .letOp .indexPowerOfTwo (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.indexConstant 4) .nil .nil <|
  .letOp .indexLess (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .letOp .booleanEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper1Helper : Helper :=
  ⟨"zkl_e6c7f1789c6410d7df7f947de61fe27fb3436c5e9f5e23ae73c9b66a88fd7d1a", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper1Body : Region dialect helper1Helper.inputs helper1Helper.outputs :=
  .letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper2Helper : Helper :=
  ⟨"finite_zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305_s1_body", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper2Body : Region dialect helper2Helper.inputs helper2Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_e6c7f1789c6410d7df7f947de61fe27fb3436c5e9f5e23ae73c9b66a88fd7d1a", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper3Helper : Helper :=
  ⟨"zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305", .math, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper3Body : Region dialect helper3Helper.inputs helper3Helper.outputs :=
  .letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil <|
  .letOp (.fold ⟨⟨ "finite_zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305_s1_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here)) ⟩, [(.field "bls12-381.fr")], [], "finite_zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305_s1_body", "", .math⟩) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper4Helper : Helper :=
  ⟨"zkf_71838ae694224dd160cf5b65d1bde35de122773b8eeb322b05ddaf4708d2957e", .math, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩

def helper4Body : Region dialect helper4Helper.inputs helper4Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305", .math, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here .nil) .nil <|
  .letOp (.fieldEqual "bls12-381.fr") (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.invoke (⟨ "zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305", .math, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.fieldEqual "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper5Helper : Helper :=
  ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩

def helper5Body : Region dialect helper5Helper.inputs helper5Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec .indexLess) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper6Helper : Helper :=
  ⟨"s3h7a6b6311h6d756c74696c696e6561724h726f7773", .local, [.index], [.index]⟩

def helper6Body : Region dialect helper6Helper.inputs helper6Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 64)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke (⟨ "s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean] ⟩ : Helper)) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s2_reject") .nil .nil (.stop .reject)) .nil)) <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.loop [.index] []) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil))) (.cons (.letOp (.mark "s7") .nil .nil (.letOp (.exec (.indexConstant 2)) .nil .nil (.letOp (.mark "s8") .nil .nil (.letOp (.exec .indexMul) (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) .nil) <|
  .ret (.cons .here .nil)

abbrev helper7Helper : Helper :=
  ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean]⟩

def helper7Body : Region dialect helper7Helper.inputs helper7Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke (⟨ "s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean] ⟩ : Helper)) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.branch [.index] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) .nil)) (.cons (.letOp (.mark "s4") .nil .nil (.letOp (.exec (.indexConstant 64)) .nil .nil (.letOp (.mark "s5") .nil .nil (.letOp (.invoke (⟨ "s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean] ⟩ : Helper)) (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) (.cons (.letOp (.mark "s7") .nil .nil (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil)))) .nil)) <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.branch [(.vector "bls12-381.fr"), .index] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) (.cons (.letOp (.mark "s12") .nil .nil (.letOp (.exec (.vectorLength "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s13") .nil .nil (.letOp (.exec .indexMod) (.cons .here (.cons (.there (.there .here)) .nil)) .nil (.letOp (.mark "s14") .nil .nil (.letOp (.exec (.indexConstant 0)) .nil .nil (.letOp (.mark "s15") .nil .nil (.letOp (.exec .indexEqual) (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))))))) (.cons (.letOp (.mark "s17") .nil .nil (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil)))) .nil)) <|
  .letOp (.mark "s22") .nil .nil <|
  .letOp (.branch [(.vector "bls12-381.fr"), .index, .index] [.boolean]) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) (.cons (.letOp (.mark "s23") .nil .nil (.letOp (.exec (.vectorLength "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s24") .nil .nil (.letOp (.exec .indexDiv) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.mark "s25") .nil .nil (.letOp (.invoke (⟨ "s3h7a6b6311h6d756c74696c696e6561724h726f7773", .local, [.index], [.index] ⟩ : Helper)) (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.mark "s26") .nil .nil (.letOp (.exec .indexEqual) (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))))))) (.cons (.letOp (.mark "s28") .nil .nil (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil)))) .nil)) <|
  .ret (.cons .here .nil)

abbrev helper8Helper : Helper :=
  ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper8Body : Region dialect helper8Helper.inputs helper8Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s1_reject") .nil .nil (.stop .reject)) .nil)) <|
  .ret (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))

abbrev pendingHelper : Helper :=
  ⟨"zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def pendingBody : Region dialect pendingHelper.inputs pendingHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper15Helper : Helper :=
  ⟨"zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩

def helper15Body : Region dialect helper15Helper.inputs helper15Helper.outputs :=
  .ret (.cons (.there (.there .here)) .nil)

abbrev helper9Helper : Helper :=
  ⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩

def helper9Body : Region dialect helper9Helper.inputs helper9Helper.outputs :=
  .ret (.cons .here .nil)

abbrev helper16Helper : Helper :=
  ⟨"zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩

def helper16Body : Region dialect helper16Helper.inputs helper16Helper.outputs :=
  .ret (.cons (.there .here) .nil)

abbrev tableShapeFormulaHelper : Helper :=
  ⟨"zkf_326ab2331715c62ba21cb6a967c927ba6ad7f7f2da5e84eb0e5de0fc610f26ca", .math, [(.vector "bls12-381.fr"), .index, .index], [.boolean]⟩

def tableShapeFormulaBody : Region dialect tableShapeFormulaHelper.inputs tableShapeFormulaHelper.outputs :=
  .letOp (.invoke (⟨ "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", .math, [(.vector "bls12-381.fr"), .index, .index], [.index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.invoke (⟨ "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.vectorLength "bls12-381.fr") (.cons .here .nil) .nil <|
  .letOp (.invoke (⟨ "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [(.vector "bls12-381.fr"), .index, .index], [.index] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))) .nil <|
  .letOp .indexPowerOfTwo (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper11Helper : Helper :=
  ⟨"zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper11Body : Region dialect helper11Helper.inputs helper11Helper.outputs :=
  .letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper12Helper : Helper :=
  ⟨"finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper12Body : Region dialect helper12Helper.inputs helper12Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper13Helper : Helper :=
  ⟨"zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", .math, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper13Body : Region dialect helper13Helper.inputs helper13Helper.outputs :=
  .letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil <|
  .letOp (.fold ⟨⟨ "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here)) ⟩, [(.field "bls12-381.fr")], [], "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", "", .math⟩) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev pendingFormulaHelper : Helper :=
  ⟨"zkf_c51d11bf318ad26bc2fce7b89eec63f85b98f57e91e0e9e6256f84a573b5b6e6", .math, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩

def pendingFormulaBody : Region dialect pendingFormulaHelper.inputs pendingFormulaHelper.outputs :=
  .letOp (.invoke (⟨ "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.multilinearRestrictPrefix "bls12-381.fr") (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.invoke (⟨ "zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", .math, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here .nil) .nil <|
  .letOp (.fieldEqual "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper17Helper : Helper :=
  ⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩

def helper17Body : Region dialect helper17Helper.inputs helper17Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .ret (.cons .here .nil)

abbrev openClaimHelper : Helper :=
  ⟨"zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def openClaimBody : Region dialect openClaimHelper.inputs openClaimHelper.outputs :=
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper18Helper : Helper :=
  ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩

def helper18Body : Region dialect helper18Helper.inputs helper18Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean] ⟩ : Helper)) (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s3_reject") .nil .nil (.stop .reject)) .nil)) <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there .here)) .nil) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper19Helper : Helper :=
  ⟨"zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", .local, [(.vector "bls12-381.fr"), .index, .index], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def helper19Body : Region dialect helper19Helper.inputs helper19Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons (.there (.there .here)) .nil) .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

abbrev helper20Helper : Helper :=
  ⟨"zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper20Body : Region dialect helper20Helper.inputs helper20Helper.outputs :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper23Helper : Helper :=
  ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def helper23Body : Region dialect helper23Helper.inputs helper23Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev atPrefixHelper : Helper :=
  ⟨"zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def atPrefixBody : Region dialect atPrefixHelper.inputs atPrefixHelper.outputs :=
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper31Helper : Helper :=
  ⟨"s3h7a6b637h626f6f6c65616e4h626f7468", .math, [.boolean, .boolean], [.boolean]⟩

def helper31Body : Region dialect helper31Helper.inputs helper31Helper.outputs :=
  .letOp .booleanAnd (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper22Helper : Helper :=
  ⟨"_mathematical_admission_1", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def scopedHelper22Body : Region dialect scopedHelper22Helper.inputs scopedHelper22Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper23Helper : Helper :=
  ⟨"zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def scopedHelper23Body : Region dialect scopedHelper23Helper.inputs scopedHelper23Helper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_1", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper24Helper : Helper :=
  ⟨"_finite_admission_0", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def scopedHelper24Body : Region dialect scopedHelper24Helper.inputs scopedHelper24Helper.outputs :=
  .letOp (.collect ⟨⟨ "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here)))) ⟩, (.vector "bls12-381.fr"), [(.field "bls12-381.fr")], "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper22Helper : Helper :=
  ⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper22Body : Region dialect helper22Helper.inputs helper22Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_0", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.exec .indexSub) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))

abbrev helper24Helper : Helper :=
  ⟨"zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper24Body : Region dialect helper24Helper.inputs helper24Helper.outputs :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper25Helper : Helper :=
  ⟨"finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper25Body : Region dialect helper25Helper.inputs helper25Helper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev scopedHelper28Helper : Helper :=
  ⟨"_mathematical_admission_2", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩

def scopedHelper28Body : Region dialect scopedHelper28Helper.inputs scopedHelper28Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper29Helper : Helper :=
  ⟨"_finite_admission_3", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index]⟩

def scopedHelper29Body : Region dialect scopedHelper29Helper.inputs scopedHelper29Helper.outputs :=
  .letOp (.fold ⟨⟨ "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here)) ⟩, [(.vector "bls12-381.fr"), .index, .index], [], "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper27Helper : Helper :=
  ⟨"zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper27Body : Region dialect helper27Helper.inputs helper27Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_3", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper28Helper : Helper :=
  ⟨"zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper28Body : Region dialect helper28Helper.inputs helper28Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev checkHelper : Helper :=
  ⟨"zkl_967e003dd39c9e1730d1e9e543081e08e351228ff07f85fb14e1e88dbded8a99", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩

def checkBody : Region dialect checkHelper.inputs checkHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_2", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.exec (.fieldEqual "bls12-381.fr")) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper30Helper : Helper :=
  ⟨"zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩

def helper30Body : Region dialect helper30Helper.inputs helper30Helper.outputs :=
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there .here) .nil) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean] ⟩ : Helper)) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.branch [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))) (.cons (.letOp (.mark "s12") .nil .nil (.letOp (.invoke (⟨ "zkl_967e003dd39c9e1730d1e9e543081e08e351228ff07f85fb14e1e88dbded8a99", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil (.ret (.cons .here .nil)))) (.cons (.letOp (.mark "s14") .nil .nil (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil)))) .nil)) <|
  .ret (.cons .here .nil)

def protocol0Signature : ProtocolSignature where
  name := "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]
  outputs := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")]
  inputScopes := [[0], [0], [0], [1], [1], [0, 1], [1]]
  outputScopes := [[0], [0], [0], [0], [1], [1]]

def protocol0Body : Region protocolDialect protocol0Signature.inputs protocol0Signature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke (⟨ "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", .math, [(.vector "bls12-381.fr"), .index, .index], [.index] ⟩ : Helper)) rfl) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.guard 0 "s3") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke (⟨ "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [(.vector "bls12-381.fr"), .index, .index], [.index] ⟩ : Helper)) rfl) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean] ⟩ : Helper) rfl 0 "s5") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanConstant false) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .booleanEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.guard 0 "s8") (.cons .here .nil) .nil <|
  .letOp (.mark "s10") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 0 "s10") .nil .nil <|
  .letOp (.mark "s12") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s12") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)) .nil <|
  .letOp (.mark "s18") .nil .nil <|
  .letOp (.repeat (⟨ [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [1], [1]], 4⟩ : RepeatSpec) "s18") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there .here)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) .nil)))))))) (.cons (.letOp (.mark "s19") .nil .nil (.letOp (.localCall (⟨ "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", .local, [(.vector "bls12-381.fr"), .index, .index], [(.field "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper) rfl 0 "s19") (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))) .nil (.letOp (.mark "label_726f756e64_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil (.letOp (.mark "label_726f756e64_1") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_1") (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldEqual "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons .here .nil)) .nil (.letOp (.mark "s27") .nil .nil (.letOp (.guard 1 "s27") (.cons .here .nil) .nil (.letOp (.mark "label_6368616c6c656e6765") .nil .nil (.letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil) .nil (.letOp (.mark "label_64656c6976657279_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil (.letOp (.mark "s32") .nil .nil (.letOp (.localCall (⟨ "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper) rfl 0 "s32") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons .here .nil)))) .nil (.letOp (.mark "s34") .nil .nil (.letOp (.localCall (⟨ "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 0 "s34") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.mark "s36") .nil .nil (.letOp (.localCall (⟨ "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 1 "s36") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldConstant "bls12-381.fr" 1) rfl) .nil .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldSubtract "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil))))))))))))))))))))))))))))))))))))))))))))) .nil) <|
  .letOp (.mark "s48") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s48") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .ret (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there .here) .nil))))))

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
  .letOp (.localCall (⟨ "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper) rfl 0 "s1") (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s3") (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil <|
  .letOp (.mark "label_6c656674") .nil .nil <|
  .letOp (.protocolApply (⟨ "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", ["role00000000", "role00000001"], [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [[0], [0], [0], [1], [1], [0, 1], [1]], [[0], [0], [0], [0], [1], [1]] ⟩ : ProtocolSignature) [0, 1] "label_6c656674") (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil))))))) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean] ⟩ : Helper) rfl 1 "s9") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "s12") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper) rfl 0 "s12") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons .here .nil))) .nil <|
  .letOp (.mark "s14") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s14") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) .nil) .nil <|
  .letOp (.mark "label_7269676874") .nil .nil <|
  .letOp (.protocolApply (⟨ "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", ["role00000000", "role00000001"], [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [[0], [0], [0], [1], [1], [0, 1], [1]], [[0], [0], [0], [0], [1], [1]] ⟩ : ProtocolSignature) [0, 1] "label_7269676874") (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))) .nil))))))) .nil <|
  .letOp (.mark "s20") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean] ⟩ : Helper) rfl 1 "s20") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke (⟨ "s3h7a6b637h626f6f6c65616e4h626f7468", .math, [.boolean, .boolean], [.boolean] ⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Construction.ComposedSumcheckProofBodies
