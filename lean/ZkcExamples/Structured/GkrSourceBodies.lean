module

public import Zkc.Source.Structured.ProtocolOperations
public import Zkc.Protocols.Gkr.Source.HelperBodies

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`ZkcExamples.Structured.GkrSourceData`. -/
namespace ZkcExamples.Structured.GkrSourceBodies
open Zkc.Source Zkc.Source.Structured

abbrev helper2Helper : Helper :=
  ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩

def helper2Body : Region dialect helper2Helper.inputs helper2Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec .indexLess) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper3Helper : Helper :=
  ⟨"s3h7a6b6311h6d756c74696c696e6561724h726f7773", .local, [.index], [.index]⟩

def helper3Body : Region dialect helper3Helper.inputs helper3Helper.outputs :=
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

abbrev helper4Helper : Helper :=
  ⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean]⟩

def helper4Body : Region dialect helper4Helper.inputs helper4Helper.outputs :=
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

abbrev sourceHelper4Helper : Helper :=
  ⟨"s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index]⟩

def sourceHelper4Body : Region dialect sourceHelper4Helper.inputs sourceHelper4Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec .indexAdd) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper18Helper : Helper :=
  ⟨"s3h676b7212h706f7765725f6f665f74776f", .local, [.index], [.index]⟩

def helper18Body : Region dialect helper18Helper.inputs helper18Helper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.powerOfTwoBody

abbrev emptyHelper : Helper :=
  ⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩

def emptyBody : Region dialect emptyHelper.inputs emptyHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .ret (.cons .here .nil)

abbrev appendHelper : Helper :=
  ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def appendBody : Region dialect appendHelper.inputs appendHelper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper5Helper : Helper :=
  ⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper5Body : Region dialect helper5Helper.inputs helper5Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s1_reject") .nil .nil (.stop .reject)) .nil)) <|
  .ret (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))

abbrev helper6Helper : Helper :=
  ⟨"zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩

def helper6Body : Region dialect helper6Helper.inputs helper6Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean] ⟩ : Helper)) (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s3_reject") .nil .nil (.stop .reject)) .nil)) <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there .here)) .nil) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper7Helper : Helper :=
  ⟨"zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper7Body : Region dialect helper7Helper.inputs helper7Helper.outputs :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper15Helper : Helper :=
  ⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩

def helper15Body : Region dialect helper15Helper.inputs helper15Helper.outputs :=
  .ret (.cons .here .nil)

abbrev sourceHelper19Helper : Helper :=
  ⟨"zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def sourceHelper19Body : Region dialect sourceHelper19Helper.inputs sourceHelper19Helper.outputs :=
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev sourceHelper20Helper : Helper :=
  ⟨"zkl_e0f7a4e58ae24eb13e9b2033c42c179b2766ff6cdb4ae1470bf7ef9b1721d646", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def sourceHelper20Body : Region dialect sourceHelper20Helper.inputs sourceHelper20Helper.outputs :=
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev selectBlockHelper : Helper :=
  ⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩

def selectBlockBody : Region dialect selectBlockHelper.inputs selectBlockHelper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.selectBlockBody

abbrev helper20Helper : Helper :=
  ⟨"zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩

def helper20Body : Region dialect helper20Helper.inputs helper20Helper.outputs :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.loop [(.vector "bls12-381.fr")] [(.field "bls12-381.fr")]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) (.cons (.letOp (.mark "s4") .nil .nil (.letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil (.ret (.cons .here (.cons (.there (.there (.there .here))) .nil))))) .nil) <|
  .ret (.cons .here .nil)

abbrev helper21Helper : Helper :=
  ⟨"zkl_e7a7efcd14676d32c0e577ff1097f611a3dc84c74ecaa8bfdbebb25968971255", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩

def helper21Body : Region dialect helper21Helper.inputs helper21Helper.outputs :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper22Helper : Helper :=
  ⟨"finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_body", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩

def helper22Body : Region dialect helper22Helper.inputs helper22Helper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_e7a7efcd14676d32c0e577ff1097f611a3dc84c74ecaa8bfdbebb25968971255", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper26Helper : Helper :=
  ⟨"zkl_ac1d3513b06c1d4950d126f678b9482e4ca13944fc4b35442d1a33796d064b0c", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def helper26Body : Region dialect helper26Helper.inputs helper26Helper.outputs :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper27Helper : Helper :=
  ⟨"finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_body", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def helper27Body : Region dialect helper27Helper.inputs helper27Helper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_ac1d3513b06c1d4950d126f678b9482e4ca13944fc4b35442d1a33796d064b0c", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper31Helper : Helper :=
  ⟨"zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper31Body : Region dialect helper31Helper.inputs helper31Helper.outputs :=
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev sourceHelper37Helper : Helper :=
  ⟨"zkl_e1405e1bb4604e60f337203132c746492bf7c31b55302426ae19c2c021c2da1a", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def sourceHelper37Body : Region dialect sourceHelper37Helper.inputs sourceHelper37Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev sourceHelper39Helper : Helper :=
  ⟨"zkf_029bdd6bcc5b1485783f1674f8c6e15543fd2d268649f211eab729158162c828", .math, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [.boolean]⟩

def sourceHelper39Body : Region dialect sourceHelper39Helper.inputs sourceHelper39Helper.outputs :=
  .letOp (.vectorLength "bls12-381.fr") (.cons .here .nil) .nil <|
  .letOp (.vectorLength "bls12-381.fr") (.cons (.there (.there .here)) .nil) .nil <|
  .letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.vectorLength "bls12-381.fr") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.vectorLength "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil <|
  .letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.vectorLength "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil) .nil <|
  .letOp (.vectorLength "bls12-381.fr") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil) .nil <|
  .letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev sourceHelper40Helper : Helper :=
  ⟨"zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def sourceHelper40Body : Region dialect sourceHelper40Helper.inputs sourceHelper40Helper.outputs :=
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper37Helper : Helper :=
  ⟨"zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper37Body : Region dialect helper37Helper.inputs helper37Helper.outputs :=
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

abbrev helper39Helper : Helper :=
  ⟨"zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper39Body : Region dialect helper39Helper.inputs helper39Helper.outputs :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldSubtract "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper42Helper : Helper :=
  ⟨"zkl_9de40b3e39acd7da53c8d9f1ec759779b60f4d0d3b7314f8741f798f050dbfd1", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper42Body : Region dialect helper42Helper.inputs helper42Helper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.interpolateBody

abbrev sourceHelper49Helper : Helper :=
  ⟨"zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def sourceHelper49Body : Region dialect sourceHelper49Helper.inputs sourceHelper49Helper.outputs :=
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev sourceHelper50Helper : Helper :=
  ⟨"zkl_cfcf40daaab145a916368cf7a01eccd9ba0e536fbbc30a06c4a25e7ec96ecbe7", .local, [(.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩

def sourceHelper50Body : Region dialect sourceHelper50Helper.inputs sourceHelper50Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec .indexEqual) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.branch [(.vector "bls12-381.fr")] [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")]) (.cons .here (.cons (.there (.there (.there .here))) .nil)) (.cons (.ret (.cons .here (.cons .here .nil))) (.cons (.letOp (.mark "s7") .nil .nil (.letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons .here .nil) .nil (.ret (.cons .here (.cons (.there .here) .nil))))) .nil)) <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper46Helper : Helper :=
  ⟨"zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137", .math, [], [(.field "bls12-381.fr")]⟩

def helper46Body : Region dialect helper46Helper.inputs helper46Helper.outputs :=
  .letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil <|
  .ret (.cons .here .nil)

abbrev helper53Helper : Helper :=
  ⟨"zkl_09043a1369ab6c082f8534fc9d21f34f77067e68b9a4c2a907a132342ff59811", .local, [(.field "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index], [(.field "bls12-381.fr"), .index]⟩

def helper53Body : Region dialect helper53Helper.inputs helper53Helper.outputs :=
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec .indexEqual) (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.branch [(.field "bls12-381.fr"), (.field "bls12-381.fr")] [(.field "bls12-381.fr")]) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) (.cons (.ret (.cons (.there .here) .nil)) (.cons (.ret (.cons .here .nil)) .nil)) <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s12") .nil .nil <|
  .letOp (.exec .indexAdd) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there .here)) (.cons .here .nil))

abbrev helper54Helper : Helper :=
  ⟨"finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_body", .local, [(.field "bls12-381.fr"), .index, (.field "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.field "bls12-381.fr"), .index]⟩

def helper54Body : Region dialect helper54Helper.inputs helper54Helper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_09043a1369ab6c082f8534fc9d21f34f77067e68b9a4c2a907a132342ff59811", .local, [(.field "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index], [(.field "bls12-381.fr"), .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper58Helper : Helper :=
  ⟨"zkl_c15efd5f24b71cb9e6e3766d00c208e0a0014177a6ae1e9dd67b23bda4eff8ab", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper58Body : Region dialect helper58Helper.inputs helper58Helper.outputs :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper60Helper : Helper :=
  ⟨"zkl_c8eacd293248ba42cad22bd955e2dec7c6105efe1dabf391c3a74b436be7412e", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper60Body : Region dialect helper60Helper.inputs helper60Helper.outputs :=
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper67Helper : Helper :=
  ⟨"zkl_02aa9bd9900f843069baf97f23f4f5ccab54b136c8fed5b90842e4c46b7e5fcd", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def helper67Body : Region dialect helper67Helper.inputs helper67Helper.outputs :=
  .letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev sumHelper : Helper :=
  ⟨"zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216", .local, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def sumBody : Region dialect sumHelper.inputs sumHelper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.sumBody

abbrev helper73Helper : Helper :=
  ⟨"zkl_82e44b33934fd674fa24fbb7f5705f2364f5020774fe25318dd2b968f9d001e4", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def helper73Body : Region dialect helper73Helper.inputs helper73Helper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.powerStepBody

abbrev helper76Helper : Helper :=
  ⟨"zkl_acc5a50f3a300b126874f48e782cbb903e9f900ea776915474c16f8e7ecd49b5", .math, [], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def helper76Body : Region dialect helper76Helper.inputs helper76Helper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.powerInitialStateBody

abbrev sourceHelper83Helper : Helper :=
  ⟨"zkl_293773d0130047867a66c9eaf450957dc940a0b0b9ee8988021422577cf8335f", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def sourceHelper83Body : Region dialect sourceHelper83Helper.inputs sourceHelper83Helper.outputs :=
  .letOp (.fieldAdd "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev sourceHelper82Helper : Helper :=
  ⟨"finite_zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff_s2_body", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def sourceHelper82Body : Region dialect sourceHelper82Helper.inputs sourceHelper82Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_293773d0130047867a66c9eaf450957dc940a0b0b9ee8988021422577cf8335f", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev sourceHelper81Helper : Helper :=
  ⟨"zkf_d1b83b15191b85497fc6003ecffb377b2ff71a9228a1114a266874f0ba672708", .math, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩

def sourceHelper81Body : Region dialect sourceHelper81Helper.inputs sourceHelper81Helper.outputs :=
  .letOp (.multilinearRestrictPrefix "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil <|
  .letOp (.fold ⟨⟨ "finite_zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff_s2_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here)) ⟩, [(.field "bls12-381.fr")], [], "finite_zkl_cb10975ebbde52f87ba3f031d71fbab61676c0ccc3b05423f90b82c03f36e3ff_s2_body", "", .math⟩) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldEqual "bls12-381.fr") (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper16Helper : Helper :=
  ⟨"_mathematical_admission_0", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩

def helper16Body : Region dialect helper16Helper.inputs helper16Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev interpolateRealizationHelper : Helper :=
  ⟨"_mathematical_admission_2", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def interpolateRealizationBody : Region dialect interpolateRealizationHelper.inputs interpolateRealizationHelper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.interpolateRealizationBody

abbrev interpolateCallbackHelper : Helper :=
  ⟨"zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def interpolateCallbackBody : Region dialect interpolateCallbackHelper.inputs interpolateCallbackHelper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_2", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper8Helper : Helper :=
  ⟨"_finite_admission_1", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def helper8Body : Region dialect helper8Helper.inputs helper8Helper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.firstInterpolationMapBody

abbrev helper9Helper : Helper :=
  ⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper9Body : Region dialect helper9Helper.inputs helper9Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_1", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.exec .indexSub) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))

abbrev helper10Helper : Helper :=
  ⟨"zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper10Body : Region dialect helper10Helper.inputs helper10Helper.outputs :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper11Helper : Helper :=
  ⟨"finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper11Body : Region dialect helper11Helper.inputs helper11Helper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper12Helper : Helper :=
  ⟨"_finite_admission_3", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper12Body : Region dialect helper12Helper.inputs helper12Helper.outputs :=
  .letOp (.fold ⟨⟨ "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here)) ⟩, [(.vector "bls12-381.fr"), .index, .index], [], "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper13Helper : Helper :=
  ⟨"zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper13Body : Region dialect helper13Helper.inputs helper13Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_3", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper14Helper : Helper :=
  ⟨"zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩

def helper14Body : Region dialect helper14Helper.inputs helper14Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev evaluateHelper : Helper :=
  ⟨"zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def evaluateBody : Region dialect evaluateHelper.inputs evaluateHelper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.evaluateBody

abbrev helper35Helper : Helper :=
  ⟨"zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59", .local, [(.vector "bls12-381.fr"), .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def helper35Body : Region dialect helper35Helper.inputs helper35Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here .nil))) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be", .local, [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_0", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev evaluateWiringHelper : Helper :=
  ⟨"zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def evaluateWiringBody : Region dialect evaluateWiringHelper.inputs evaluateWiringHelper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.evaluateWiringBody

abbrev sourceHelper84Helper : Helper :=
  ⟨"zkl_d74cb9bd9ed782590145b66a573f8104fca0e842c109c7d034296431308fc6b9", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩

def sourceHelper84Body : Region dialect sourceHelper84Helper.inputs sourceHelper84Helper.outputs :=
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.fieldEqual "bls12-381.fr")) (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper42Helper : Helper :=
  ⟨"_mathematical_admission_5", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def scopedHelper42Body : Region dialect scopedHelper42Helper.inputs scopedHelper42Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_6b3d366572d1ba53650a202f39ff52a2f298a1591829443fbeaa34ef3974f084", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper43Helper : Helper :=
  ⟨"zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def scopedHelper43Body : Region dialect scopedHelper43Helper.inputs scopedHelper43Helper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_5", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper44Helper : Helper :=
  ⟨"_finite_admission_4", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def scopedHelper44Body : Region dialect scopedHelper44Helper.inputs scopedHelper44Helper.outputs :=
  .letOp (.collect ⟨⟨ "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there .here))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there .here)))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here)))))))) ⟩, (.vector "bls12-381.fr"), [], "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper45Helper : Helper :=
  ⟨"_finite_admission_6", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩

def scopedHelper45Body : Region dialect scopedHelper45Helper.inputs scopedHelper45Helper.outputs :=
  .letOp (.fold ⟨⟨ "finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here)) ⟩, [(.vector "bls12-381.fr")], [.index], "finite_zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper24Helper : Helper :=
  ⟨"zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294", .local, [(.vector "bls12-381.fr"), .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def helper24Body : Region dialect helper24Helper.inputs helper24Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_6", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there .here)) (.cons .here (.cons (.there .here) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper25Helper : Helper :=
  ⟨"zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490", .local, [(.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩

def helper25Body : Region dialect helper25Helper.inputs helper25Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_33e26704899171b0d3e366f86377dfc6602b55f53021ce20930f7ae9e8061294", .local, [(.vector "bls12-381.fr"), .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there (.there .here)) (.cons (.there .here) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper48Helper : Helper :=
  ⟨"_finite_admission_7", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def scopedHelper48Body : Region dialect scopedHelper48Helper.inputs scopedHelper48Helper.outputs :=
  .letOp (.fold ⟨⟨ "finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here)) ⟩, [(.vector "bls12-381.fr")], [], "finite_zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper29Helper : Helper :=
  ⟨"zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def helper29Body : Region dialect helper29Helper.inputs helper29Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_7", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper30Helper : Helper :=
  ⟨"zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947", .local, [(.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩

def helper30Body : Region dialect helper30Helper.inputs helper30Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.loop [(.vector "bls12-381.fr")] [(.vector "bls12-381.fr")]) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) (.cons (.letOp (.mark "s5") .nil .nil (.letOp (.invoke (⟨ "zkl_5939bc7a1ddcd11f8e2153f23b3ed89c16434b9b99db1512543ee10e7b59b248", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil (.ret (.cons .here (.cons (.there (.there (.there .here))) .nil))))) .nil) <|
  .ret (.cons .here .nil)

abbrev helper33Helper : Helper :=
  ⟨"zkl_3a99bc0fa1dab7cb27c9ec80754c3782b0a32e76ddc961a50e12c24c6cbff683", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩

def helper33Body : Region dialect helper33Helper.inputs helper33Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "s3h676b7212h706f7765725f6f665f74776f", .local, [.index], [.index] ⟩ : Helper)) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490", .local, [(.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947", .local, [(.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s14") .nil .nil <|
  .letOp (.loop [(.vector "bls12-381.fr")] [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))))))) (.cons (.letOp (.mark "s15") .nil .nil (.letOp (.invoke (⟨ "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil))) .nil (.letOp (.mark "s17") .nil .nil (.letOp (.invoke (⟨ "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil (.letOp (.mark "s19") .nil .nil (.letOp (.invoke (⟨ "_finite_admission_4", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))) .nil (.letOp (.mark "s20") .nil .nil (.letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil (.letOp (.mark "s21") .nil .nil (.letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil (.ret (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil))))))))))))))))) .nil) <|
  .ret (.cons .here .nil)

abbrev helper34Helper : Helper :=
  ⟨"zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, .index], [(.vector "bls12-381.fr")]⟩

def helper34Body : Region dialect helper34Helper.inputs helper34Helper.outputs :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec .indexSub) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec .indexSub) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s10") .nil .nil <|
  .letOp (.loop [(.vector "bls12-381.fr"), .index] [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index]) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)))))))) (.cons (.letOp (.mark "s11") .nil .nil (.letOp (.exec (.indexConstant 1)) .nil .nil (.letOp (.mark "s12") .nil .nil (.letOp (.exec .indexSub) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil (.letOp (.mark "s14") .nil .nil (.letOp (.invoke (⟨ "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))) .nil (.letOp (.mark "s15") .nil .nil (.letOp (.invoke (⟨ "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))) .nil (.letOp (.mark "s16") .nil .nil (.letOp (.invoke (⟨ "zkl_3a99bc0fa1dab7cb27c9ec80754c3782b0a32e76ddc961a50e12c24c6cbff683", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)))) .nil (.ret (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil))))))))))))))))) .nil) <|
  .ret (.cons .here .nil)

abbrev helper36Helper : Helper :=
  ⟨"zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩

def helper36Body : Region dialect helper36Helper.inputs helper36Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "s3h676b7212h706f7765725f6f665f74776f", .local, [.index], [.index] ⟩ : Helper)) (.cons (.there (.there (.there (.there .here)))) .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec .indexAdd) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.exec .indexAdd) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59", .local, [(.vector "bls12-381.fr"), .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_b16c159516733e0a19ce242015622636ee99dc6084d8c851dfb43c25cee57b59", .local, [(.vector "bls12-381.fr"), .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_afd97de07c9ccae9db68186ebf66098aed7daffb4b11c598d0da5cd116df8490", .local, [(.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_33f3047479634e63ecd16a0855f88ad8af019c37d677a4ffe6f5bacc63307947", .local, [(.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .ret (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))))

abbrev scopedHelper54Helper : Helper :=
  ⟨"_finite_admission_8", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def scopedHelper54Body : Region dialect scopedHelper54Helper.inputs scopedHelper54Helper.outputs :=
  .letOp (.collect ⟨⟨ "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there .here))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there .here)))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here)))))))) ⟩, (.vector "bls12-381.fr"), [], "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper55Helper : Helper :=
  ⟨"_finite_admission_9", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def scopedHelper55Body : Region dialect scopedHelper55Helper.inputs scopedHelper55Helper.outputs :=
  .letOp (.collect ⟨⟨ "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there .here))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there .here)))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here)))))))) ⟩, (.vector "bls12-381.fr"), [], "zkl_map_af20412de65402ccb37e9b1155a5813b651e3465b274bef11b5ab20eace8f011_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper56Helper : Helper :=
  ⟨"_mathematical_admission_11", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def scopedHelper56Body : Region dialect scopedHelper56Helper.inputs scopedHelper56Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_ae0ec2b882ea51d896368927e811be493e3af32def2e5ada1525e385646e6229", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper57Helper : Helper :=
  ⟨"_mathematical_admission_12", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def scopedHelper57Body : Region dialect scopedHelper57Helper.inputs scopedHelper57Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_f5e0b2f9a4003d8d806a7a288580cf1f30d07d383f870564beff948ccf011d6b", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper58Helper : Helper :=
  ⟨"zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def scopedHelper58Body : Region dialect scopedHelper58Helper.inputs scopedHelper58Helper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_12", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper59Helper : Helper :=
  ⟨"_finite_admission_10", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def scopedHelper59Body : Region dialect scopedHelper59Helper.inputs scopedHelper59Helper.outputs :=
  .letOp (.collect ⟨⟨ "zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there .here))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there .here)))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there (.there .here))))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there (.there (.there .here)))))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there (.there (.there (.there .here))))))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.letNode (.elements (.vector "bls12-381.fr") (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.letNode (.zip [[(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here)))))))))))))))) ⟩, (.vector "bls12-381.fr"), [], "zkl_map_b02c6bec831af4d953cc5d5558b1dfebb2f6666e509fde68f0a09745680b6577_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))))) .nil <|
  .ret (.cons .here .nil)

abbrev helper41Helper : Helper :=
  ⟨"zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def helper41Body : Region dialect helper41Helper.inputs helper41Helper.outputs :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil <|
  .letOp (.mark "s10") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil) .nil <|
  .letOp (.mark "s16") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_8", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) (.cons .here .nil)))) .nil <|
  .letOp (.mark "s17") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s23") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_9", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .letOp (.mark "s24") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s34") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_10", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))))) .nil <|
  .letOp (.mark "s35") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s37") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_11", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) (.cons .here .nil))) .nil <|
  .ret (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here (.cons (.there .here) .nil)))

abbrev lineInterpolationRealizationHelper : Helper :=
  ⟨"_mathematical_admission_14", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def lineInterpolationRealizationBody : Region dialect lineInterpolationRealizationHelper.inputs lineInterpolationRealizationHelper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.lineInterpolationRealizationBody

abbrev lineCallbackHelper : Helper :=
  ⟨"zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def lineCallbackBody : Region dialect lineCallbackHelper.inputs lineCallbackHelper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.lineCallbackBody

abbrev scopedHelper63Helper : Helper :=
  ⟨"_finite_admission_13", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def scopedHelper63Body : Region dialect scopedHelper63Helper.inputs scopedHelper63Helper.outputs :=
  .letOp (.collect ⟨⟨ "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here)))) ⟩, (.vector "bls12-381.fr"), [(.field "bls12-381.fr")], "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper44Helper : Helper :=
  ⟨"zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def helper44Body : Region dialect helper44Helper.inputs helper44Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_13", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper45Helper : Helper :=
  ⟨"zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩

def helper45Body : Region dialect helper45Helper.inputs helper45Helper.outputs :=
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_19eb2471a19ddb7204e865a3cced7de20ed18271fd1a56db5300227b86d660ac", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .ret (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))))

abbrev scopedHelper66Helper : Helper :=
  ⟨"_finite_admission_15", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def scopedHelper66Body : Region dialect scopedHelper66Helper.inputs scopedHelper66Helper.outputs :=
  .letOp (.collect ⟨⟨ "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here)))) ⟩, (.vector "bls12-381.fr"), [(.field "bls12-381.fr")], "zkl_map_c146dd3d9114244d244e3c5f1750c58c167183b76600905d92674f3b3e023a6f_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper67Helper : Helper :=
  ⟨"_mathematical_admission_16", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def scopedHelper67Body : Region dialect scopedHelper67Helper.inputs scopedHelper67Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_c15efd5f24b71cb9e6e3766d00c208e0a0014177a6ae1e9dd67b23bda4eff8ab", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper68Helper : Helper :=
  ⟨"_mathematical_admission_19", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def scopedHelper68Body : Region dialect scopedHelper68Helper.inputs scopedHelper68Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_c8eacd293248ba42cad22bd955e2dec7c6105efe1dabf391c3a74b436be7412e", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper69Helper : Helper :=
  ⟨"zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def scopedHelper69Body : Region dialect scopedHelper69Helper.inputs scopedHelper69Helper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_19", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper70Helper : Helper :=
  ⟨"_finite_admission_17", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def scopedHelper70Body : Region dialect scopedHelper70Helper.inputs scopedHelper70Helper.outputs :=
  .letOp (.collect ⟨⟨ "zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here)))) ⟩, (.vector "bls12-381.fr"), [(.field "bls12-381.fr")], "zkl_map_f8f9614d3bd7d4196ffb7d73d3d80b5571e091e9fdbaeb4adc8aa23e703bd4a5_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper71Helper : Helper :=
  ⟨"_mathematical_admission_20", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def scopedHelper71Body : Region dialect scopedHelper71Helper.inputs scopedHelper71Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_02aa9bd9900f843069baf97f23f4f5ccab54b136c8fed5b90842e4c46b7e5fcd", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper72Helper : Helper :=
  ⟨"zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def scopedHelper72Body : Region dialect scopedHelper72Helper.inputs scopedHelper72Helper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_20", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper73Helper : Helper :=
  ⟨"_finite_admission_18", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def scopedHelper73Body : Region dialect scopedHelper73Helper.inputs scopedHelper73Helper.outputs :=
  .letOp (.collect ⟨⟨ "zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_domain", [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.letNode (.elements (.vector "bls12-381.fr") (.there .here)) (.letNode (.zip [[(.field "bls12-381.fr")], [(.field "bls12-381.fr")]] (.cons (.there .here) (.cons .here .nil))) (.ret .here)))) ⟩, (.vector "bls12-381.fr"), [], "zkl_map_b7eb5d68e6edd9e938f02a44220440e7b9e5f3fe195e305a87f963f93affd321_body", "", .local⟩) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper74Helper : Helper :=
  ⟨"_mathematical_admission_21", .local, [], [(.field "bls12-381.fr")]⟩

def scopedHelper74Body : Region dialect scopedHelper74Helper.inputs scopedHelper74Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_e38306e1154810613f8b855b4e24394048cbbd4c4b2723722235b0e03496f137", .math, [], [(.field "bls12-381.fr")] ⟩ : Helper)) .nil .nil <|
  .ret (.cons .here .nil)

abbrev helper48Helper : Helper :=
  ⟨"zkl_8184464d79b9512ca72dac4d64d1ba3d187fd1efb0b8118690b5a104ab35f351", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩

def helper48Body : Region dialect helper48Helper.inputs helper48Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_21", .local, [], [(.field "bls12-381.fr")] ⟩ : Helper)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_fbd2531b804047766f8107241edd0ea81368b70795e44e4d8e07484d142783bb", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper49Helper : Helper :=
  ⟨"zkl_f9bc3972b3acce79409bfe72125c3b04de4dbb81a13d1dfbc918146c1354315c", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩

def helper49Body : Region dialect helper49Helper.inputs helper49Helper.outputs :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_8184464d79b9512ca72dac4d64d1ba3d187fd1efb0b8118690b5a104ab35f351", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper50Helper : Helper :=
  ⟨"finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_body", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩

def helper50Body : Region dialect helper50Helper.inputs helper50Helper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_f9bc3972b3acce79409bfe72125c3b04de4dbb81a13d1dfbc918146c1354315c", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper62Helper : Helper :=
  ⟨"zkl_abd6f98141af14ddf8b9152129fb3a9fb361b5735ade780e8d1c876d68deb283", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index], [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index]⟩

def helper62Body : Region dialect helper62Helper.inputs helper62Helper.outputs :=
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.exec .indexMod) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.exec .indexEqual) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.branch [(.field "bls12-381.fr")] [(.field "bls12-381.fr")]) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) (.cons (.letOp (.mark "s9") .nil .nil (.letOp (.invoke (⟨ "_mathematical_admission_21", .local, [], [(.field "bls12-381.fr")] ⟩ : Helper)) .nil .nil (.ret (.cons .here .nil)))) (.cons (.ret (.cons .here .nil)) .nil)) <|
  .letOp (.mark "s13") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s15") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s16") .nil .nil <|
  .letOp (.exec .indexAdd) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons .here .nil)))

abbrev helper63Helper : Helper :=
  ⟨"finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_body", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.field "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index]⟩

def helper63Body : Region dialect helper63Helper.inputs helper63Helper.outputs :=
  .letOp (.mark "body") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_abd6f98141af14ddf8b9152129fb3a9fb361b5735ade780e8d1c876d68deb283", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index], [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev scopedHelper80Helper : Helper :=
  ⟨"_finite_admission_22", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩

def scopedHelper80Body : Region dialect scopedHelper80Helper.inputs scopedHelper80Helper.outputs :=
  .letOp (.fold ⟨⟨ "finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here)) ⟩, [(.vector "bls12-381.fr")], [.index], "finite_zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper52Helper : Helper :=
  ⟨"zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35", .local, [(.vector "bls12-381.fr"), .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def helper52Body : Region dialect helper52Helper.inputs helper52Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_22", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there .here)) (.cons .here (.cons (.there .here) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper82Helper : Helper :=
  ⟨"_finite_admission_23", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, .index], [(.field "bls12-381.fr"), .index]⟩

def scopedHelper82Body : Region dialect scopedHelper82Helper.inputs scopedHelper82Helper.outputs :=
  .letOp (.fold ⟨⟨ "finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here)) ⟩, [(.field "bls12-381.fr"), .index], [.index], "finite_zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper56Helper : Helper :=
  ⟨"zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45", .local, [(.field "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), .index]⟩

def helper56Body : Region dialect helper56Helper.inputs helper56Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_23", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, .index], [(.field "bls12-381.fr"), .index] ⟩ : Helper)) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

abbrev helper57Helper : Helper :=
  ⟨"zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [(.vector "bls12-381.fr"), .index], [(.field "bls12-381.fr")]⟩

def helper57Body : Region dialect helper57Helper.inputs helper57Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_21", .local, [], [(.field "bls12-381.fr")] ⟩ : Helper)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_4d05c370830a894df2470c3859782e53b3322378b124acf8f383759935b54a45", .local, [(.field "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), .index] ⟩ : Helper)) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))) .nil <|
  .ret (.cons .here .nil)

abbrev helper70Helper : Helper :=
  ⟨"zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47", .local, [(.vector "bls12-381.fr"), .index], [(.field "bls12-381.fr")]⟩

def helper70Body : Region dialect helper70Helper.inputs helper70Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec .indexAdd) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [(.vector "bls12-381.fr"), .index], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev scopedHelper86Helper : Helper :=
  ⟨"_finite_admission_24", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index]⟩

def scopedHelper86Body : Region dialect scopedHelper86Helper.inputs scopedHelper86Helper.outputs :=
  .letOp (.fold ⟨⟨ "finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_domain", [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")], (.letNode (.elements (.vector "bls12-381.fr") .here) (.ret .here)) ⟩, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index], [.index], "finite_zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403_s0_body", "", .local⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil))))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper65Helper : Helper :=
  ⟨"zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index]⟩

def helper65Body : Region dialect helper65Helper.inputs helper65Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "_finite_admission_24", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index] ⟩ : Helper)) (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper66Helper : Helper :=
  ⟨"zkl_3d3958243128671a7ae06c730aba5c78b4cae61932510ab43ba5bcabe7324295", .local, [(.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩

def helper66Body : Region dialect helper66Helper.inputs helper66Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke (⟨ "_mathematical_admission_21", .local, [], [(.field "bls12-381.fr")] ⟩ : Helper)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_b09f44c87195c8e3d60f4dede007ee713df6eb6126ac95620f16b0ca8ac2c403", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index] ⟩ : Helper)) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there .here))) .nil))))) .nil <|
  .ret (.cons .here .nil)

abbrev helper69Helper : Helper :=
  ⟨"zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩

def helper69Body : Region dialect helper69Helper.inputs helper69Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec .indexAdd) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_a746a0d46b63db09f05e685a16e7d9cfdc6a78a249031577993dd2aeeff20b35", .local, [(.vector "bls12-381.fr"), .index, (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s13") .nil .nil <|
  .letOp (.loop [(.vector "bls12-381.fr"), .index] [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index]) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there .here)) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there .here)))) .nil))))))) (.cons (.letOp (.mark "s14") .nil .nil (.letOp (.invoke (⟨ "zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [(.vector "bls12-381.fr"), .index], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)) .nil (.letOp (.mark "s16") .nil .nil (.letOp (.invoke (⟨ "zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [(.vector "bls12-381.fr"), .index], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.mark "s18") .nil .nil (.letOp (.exec (.vectorSplit "bls12-381.fr")) (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.mark "s22") .nil .nil (.letOp (.invoke (⟨ "_finite_admission_15", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))) .nil (.letOp (.mark "s26") .nil .nil (.letOp (.invoke (⟨ "_mathematical_admission_16", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil (.letOp (.mark "s27") .nil .nil (.letOp (.invoke (⟨ "_finite_admission_17", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons .here .nil))) .nil (.letOp (.mark "s29") .nil .nil (.letOp (.invoke (⟨ "zkl_3d3958243128671a7ae06c730aba5c78b4cae61932510ab43ba5bcabe7324295", .local, [(.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)) .nil (.letOp (.mark "s30") .nil .nil (.letOp (.invoke (⟨ "_finite_admission_18", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper)) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil (.letOp (.mark "s32") .nil .nil (.letOp (.exec (.indexConstant 1)) .nil .nil (.letOp (.mark "s33") .nil .nil (.letOp (.exec .indexAdd) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons .here .nil)) .nil (.ret (.cons (.there (.there .here)) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) .nil)))))))))))))))))))))))))) .nil) <|
  .ret (.cons .here .nil)

abbrev sourceHelper110Helper : Helper :=
  ⟨"_finite_admission_25", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def sourceHelper110Body : Region dialect sourceHelper110Helper.inputs sourceHelper110Helper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.lineInterpolationMapBody

abbrev linePointHelper : Helper :=
  ⟨"zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩

def linePointBody : Region dialect linePointHelper.inputs linePointHelper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.linePointBody

abbrev helper74Helper : Helper :=
  ⟨"_mathematical_admission_26", .local, [], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def helper74Body : Region dialect helper74Helper.inputs helper74Helper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.powerInitialRealizationBody

abbrev sourceHelper112Helper : Helper :=
  ⟨"_mathematical_admission_27", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def sourceHelper112Body : Region dialect sourceHelper112Helper.inputs sourceHelper112Helper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.powerStepRealizationBody

abbrev helper75Helper : Helper :=
  ⟨"zkl_bcbdb252ffc9abd0563757a6a45f0dccb9a7c345ecbfb58b787c5137455bd42e", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def helper75Body : Region dialect helper75Helper.inputs helper75Helper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.powerStepWrapperBody

abbrev helper78Helper : Helper :=
  ⟨"finite_zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d_s0_body", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def helper78Body : Region dialect helper78Helper.inputs helper78Helper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.powerFoldCallbackBody

abbrev helper43Helper : Helper :=
  ⟨"_finite_admission_28", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def helper43Body : Region dialect helper43Helper.inputs helper43Helper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.powerFoldBody

abbrev helper80Helper : Helper :=
  ⟨"zkl_247e1b3b5a6ce35694e95bcda98d3515aa558355e01cc2e1d2878fc90608735d", .local, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩

def helper80Body : Region dialect helper80Helper.inputs helper80Helper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.powerFoldWrapperBody

abbrev evaluateCoefficientsHelper : Helper :=
  ⟨"zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩

def evaluateCoefficientsBody : Region dialect evaluateCoefficientsHelper.inputs evaluateCoefficientsHelper.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.evaluateCoefficientsBody

def roundsSignature : ProtocolSignature where
  name := "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]
  outputs := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]
  inputScopes := [[0], [0], [0], [0], [1], [1], [0, 1], [1]]
  outputScopes := [[0], [0], [0], [0], [0], [1], [1]]

def roundsBody : Region protocolDialect roundsSignature.inputs roundsSignature.outputs :=
  Zkc.Protocols.Gkr.Source.HelperBodies.roundsProtocolBody 4

def sourceProtocol80Signature : ProtocolSignature where
  name := "zkl_9719be65739d901a935dbaa0f3f8323a785562f7eee1e60cc8c8c9676f8fdb55"
  roles := ["role00000000"]
  inputs := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]
  outputs := [.boolean]
  inputScopes := [[0], [0], [0]]
  outputScopes := [[0]]

def sourceProtocol80Body : Region protocolDialect sourceProtocol80Signature.inputs sourceProtocol80Signature.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_d74cb9bd9ed782590145b66a573f8104fca0e842c109c7d034296431308fc6b9", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean] ⟩ : Helper) rfl 0 "s0") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

def gkrSignature : ProtocolSignature where
  name := "zkl_c0372bf2a0caec53ac4800eb2a35b7daaf18a424854430934453ed7d7d0ee7f2"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")]
  outputs := [.boolean]
  inputScopes := [[0, 1], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [1]]
  outputScopes := [[1]]

def gkrBody : Region protocolDialect gkrSignature.inputs gkrSignature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 4) rfl) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean] ⟩ : Helper) rfl 1 "s1") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanConstant false) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .booleanEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.guard 1 "s4") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 4) rfl) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean] ⟩ : Helper) rfl 1 "s6") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanConstant false) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .booleanEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.guard 1 "s9") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean] ⟩ : Helper) rfl 1 "s11") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons .here .nil))) .nil <|
  .letOp (.mark "s12") .nil .nil <|
  .letOp (.guard 1 "s12") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "s14") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean] ⟩ : Helper) rfl 1 "s14") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.cons .here .nil))) .nil <|
  .letOp (.mark "s15") .nil .nil <|
  .letOp (.guard 1 "s15") (.cons .here .nil) .nil <|
  .letOp (.mark "s16") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index] ⟩ : Helper) rfl 1 "s16") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "s17") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index] ⟩ : Helper) rfl 1 "s17") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "s18") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index] ⟩ : Helper) rfl 1 "s18") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "s20") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean] ⟩ : Helper) rfl 1 "s20") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s21") .nil .nil <|
  .letOp (.guard 1 "s21") (.cons .here .nil) .nil <|
  .letOp (.mark "s22") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index] ⟩ : Helper) rfl 1 "s22") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "s23") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index] ⟩ : Helper) rfl 1 "s23") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "s24") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index] ⟩ : Helper) rfl 1 "s24") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "s26") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean] ⟩ : Helper) rfl 1 "s26") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s27") .nil .nil <|
  .letOp (.guard 1 "s27") (.cons .here .nil) .nil <|
  .letOp (.mark "s28") .nil .nil <|
  .letOp (.localCall (⟨ "s3h676b7212h706f7765725f6f665f74776f", .local, [.index], [.index] ⟩ : Helper) rfl 1 "s28") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))) .nil) .nil <|
  .letOp (.mark "s29") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean] ⟩ : Helper) rfl 1 "s29") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanConstant false) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .booleanEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s32") .nil .nil <|
  .letOp (.guard 1 "s32") (.cons .here .nil) .nil <|
  .letOp (.mark "s33") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 1 "s33") .nil .nil <|
  .letOp (.mark "s35") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 0 "s35") .nil .nil <|
  .letOp (.mark "s37") .nil .nil <|
  .letOp (.repeat (⟨ [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[1], [0]], 4⟩ : RepeatSpec) "s37") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))) .nil)))) (.cons (.letOp (.mark "label_6f7574707574") .nil .nil (.letOp (.draw 1 "bls12-381.fr" "label_6f7574707574") (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.mark "label_6f75747075745f64656c6976657279_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 1 0 "label_6f75747075745f64656c6976657279_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil (.letOp (.mark "s42") .nil .nil (.letOp (.localCall (⟨ "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 1 "s42") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) .nil)) .nil (.letOp (.mark "s44") .nil .nil (.letOp (.localCall (⟨ "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 0 "s44") (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there .here) .nil)) .nil (.ret (.cons (.there .here) (.cons .here .nil))))))))))))) .nil) <|
  .letOp (.mark "s48") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s48") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s49") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s49") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s57") .nil .nil <|
  .letOp (.repeat (⟨ [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")], [0, 1], [[0], [1], [1]], 4⟩ : RepeatSpec) "s57") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))))) .nil))))))))))) (.cons (.letOp (.mark "s58") .nil .nil (.letOp (.localCall (⟨ "zkl_e0f7a4e58ae24eb13e9b2033c42c179b2766ff6cdb4ae1470bf7ef9b1721d646", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s58") (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.mark "s60") .nil .nil (.letOp (.localCall (⟨ "zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 0 "s60") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there .here)) .nil))))))) .nil (.letOp (.mark "s62") .nil .nil (.letOp (.localCall (⟨ "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 0 "s62") (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil))) .nil (.letOp (.mark "s63") .nil .nil (.letOp (.localCall (⟨ "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 0 "s63") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil))) .nil (.letOp (.mark "s64") .nil .nil (.letOp (.localCall (⟨ "zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")] ⟩ : Helper) rfl 0 "s64") (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil))))) .nil (.letOp (.mark "s67") .nil .nil (.letOp (.localCall (⟨ "zkl_e1405e1bb4604e60f337203132c746492bf7c31b55302426ae19c2c021c2da1a", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s67") (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil) .nil (.letOp (.mark "label_6c656674") .nil .nil (.letOp (.protocolApply (⟨ "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", ["role00000000", "role00000001"], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [[0], [0], [0], [0], [1], [1], [0, 1], [1]], [[0], [0], [0], [0], [0], [1], [1]] ⟩ : ProtocolSignature) [0, 1] "label_6c656674") (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) .nil)))))))) .nil (.letOp (.mark "label_7269676874") .nil .nil (.letOp (.protocolApply (⟨ "zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", ["role00000000", "role00000001"], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [[0], [0], [0], [0], [1], [1], [0, 1], [1]], [[0], [0], [0], [0], [0], [1], [1]] ⟩ : ProtocolSignature) [0, 1] "label_7269676874") (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))) .nil)))))))) .nil (.letOp (.mark "s76") .nil .nil (.letOp (.localCall (⟨ "zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s76") (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil (.letOp (.mark "s79") .nil .nil (.letOp (.localCall (⟨ "zkl_cfcf40daaab145a916368cf7a01eccd9ba0e536fbbc30a06c4a25e7ec96ecbe7", .local, [(.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")] ⟩ : Helper) rfl 1 "s79") (.cons .here .nil) .nil (.letOp (.mark "s81") .nil .nil (.letOp (.localCall (⟨ "zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 0 "s81") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))) .nil)))) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.indexConstant 0) rfl) .nil .nil (.letOp (.mark "s84") .nil .nil (.letOp (.localCall (⟨ "zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [(.vector "bls12-381.fr"), .index], [(.field "bls12-381.fr")] ⟩ : Helper) rfl 0 "s84") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.mark "label_6c696e655f636f6e7374616e74_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 0 1 "label_6c696e655f636f6e7374616e74_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil (.letOp (.mark "s87") .nil .nil (.letOp (.localCall (⟨ "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 1 "s87") .nil .nil (.letOp (.mark "s88") .nil .nil (.letOp (.localCall (⟨ "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 1 "s88") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "s91") .nil .nil (.letOp (.repeat (⟨ [(.vector "bls12-381.fr")], [(.vector "bls12-381.fr")], [0, 1], [[1]], 4⟩ : RepeatSpec) "s91") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))))))))))))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))) (.cons (.letOp (.mark "s92") .nil .nil (.letOp (.localCall (⟨ "zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47", .local, [(.vector "bls12-381.fr"), .index], [(.field "bls12-381.fr")] ⟩ : Helper) rfl 0 "s92") (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.letOp (.mark "label_6c696e655f636f656666696369656e74_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 0 1 "label_6c696e655f636f656666696369656e74_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil (.letOp (.mark "s95") .nil .nil (.letOp (.localCall (⟨ "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 1 "s95") (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))))))) .nil) (.letOp (.mark "s99") .nil .nil (.letOp (.localCall (⟨ "zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216", .local, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s99") (.cons .here .nil) .nil (.letOp (.mark "s101") .nil .nil (.letOp (.localCall (⟨ "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 1 "s101") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))))))))))) .nil))) .nil (.letOp (.mark "s105") .nil .nil (.letOp (.localCall (⟨ "zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s105") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil)))) .nil (.letOp (.mark "s107") .nil .nil (.letOp (.localCall (⟨ "zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 1 "s107") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))))))))))))) .nil))) .nil (.letOp (.mark "s111") .nil .nil (.letOp (.localCall (⟨ "zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s111") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil)))) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldEqual "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) (.cons .here .nil)) .nil (.letOp (.mark "s120") .nil .nil (.letOp (.guard 1 "s120") (.cons .here .nil) .nil (.letOp (.mark "label_6c696e655f6368616c6c656e6765") .nil .nil (.letOp (.draw 1 "bls12-381.fr" "label_6c696e655f6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) .nil) .nil (.letOp (.mark "label_6c696e655f64656c6976657279_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 1 0 "label_6c696e655f64656c6976657279_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil (.letOp (.mark "s127") .nil .nil (.letOp (.localCall (⟨ "zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 1 "s127") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))) (.cons (.there (.there .here)) .nil))) .nil (.letOp (.mark "s128") .nil .nil (.letOp (.localCall (⟨ "zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s128") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.mark "s129") .nil .nil (.letOp (.localCall (⟨ "zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")] ⟩ : Helper) rfl 1 "s129") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.mark "s131") .nil .nil (.letOp (.localCall (⟨ "zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")] ⟩ : Helper) rfl 0 "s131") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there .here)))) .nil))) .nil (.ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) .nil) <|
  .letOp (.mark "label_696e707574") .nil .nil <|
  .letOp (.protocolApply (⟨ "zkl_9719be65739d901a935dbaa0f3f8323a785562f7eee1e60cc8c8c9676f8fdb55", ["role00000000"], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean], [[0], [0], [0]], [[0]] ⟩ : ProtocolSignature) [1] "label_696e707574") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))) (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Structured.GkrSourceBodies
