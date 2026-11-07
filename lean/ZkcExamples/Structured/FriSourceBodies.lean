module

public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Literal typed bodies printed from the admitted snapshot of
`ZkcExamples.Structured.FriSourceData`. -/
namespace ZkcExamples.Structured.FriSourceBodies
open Zkc.Source Zkc.Source.Structured

abbrev helper0Helper : Helper :=
  ⟨"zkl_efc5ece4a9b8074e3e7d2a732607ad124d6dff15f36a8e9dc596d88df0573550", .local, [(.vector "koala-bear.ext8-binomial3")], [.index]⟩

def helper0Body : Region dialect helper0Helper.inputs helper0Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorLength "koala-bear.ext8-binomial3")) (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

abbrev helper1Helper : Helper :=
  ⟨"zkl_c3169a788d16114055a6dcd17778ae22d9676c00065943d6b8246ea4c514dfa6", .local, [(.field "koala-bear.ext8-binomial3"), .index], [(.field "koala-bear.ext8-binomial3"), .index]⟩

def helper1Body : Region dialect helper1Helper.inputs helper1Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.numerical Numerical.polyPoint "koala-bear.ext8-binomial3" "")) (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here .nil))) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.fieldConstant "koala-bear.ext8-binomial3" 0) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.fieldEqual "koala-bear.ext8-binomial3")) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .letOp (.mark "s5_both") .nil .nil <|
  .letOp .booleanAnd (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s5_left") .nil .nil <|
  .letOp (.exec .booleanNot) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "s5_right") .nil .nil <|
  .letOp (.exec .booleanNot) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "s5_neither") .nil .nil <|
  .letOp .booleanAnd (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp .booleanOr (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s6_reject") .nil .nil (.stop .reject)) .nil)) <|
  .ret (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil))

abbrev helper2Helper : Helper :=
  ⟨"zkl_c97799520c7003578d28af2a16eeebea354b88059ae6ee44e5912a4212abf651", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")]⟩

def helper2Body : Region dialect helper2Helper.inputs helper2Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorLength "koala-bear.ext8-binomial3")) (.cons .here .nil) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.numerical Numerical.polyPoint "koala-bear.ext8-binomial3" "")) (.cons (.there (.there (.there .here))) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.fieldConstant "koala-bear.ext8-binomial3" 0) .nil .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.exec (.fieldEqual "koala-bear.ext8-binomial3")) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .letOp (.mark "s6_both") .nil .nil <|
  .letOp .booleanAnd (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s6_left") .nil .nil <|
  .letOp (.exec .booleanNot) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "s6_right") .nil .nil <|
  .letOp (.exec .booleanNot) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "s6_neither") .nil .nil <|
  .letOp .booleanAnd (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp .booleanOr (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s7_reject") .nil .nil (.stop .reject)) .nil)) <|
  .ret (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil))

abbrev helper3Helper : Helper :=
  ⟨"zkl_82d4f61df0504a5e4381e3fd226e2a5b64bf67e87429b2feabc0d4ed0629be57", .local, [.index], [(.field "koala-bear.ext8-binomial3")]⟩

def helper3Body : Region dialect helper3Helper.inputs helper3Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.numerical Numerical.polyRoot "koala-bear.ext8-binomial3" "")) (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

abbrev helper4Helper : Helper :=
  ⟨"zkl_a14c556d4abc6083c08616c54f7346c2cf2a3ae5f52aa3d4d28b079f9c3d719f", .local, [(.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")]⟩

def helper4Body : Region dialect helper4Helper.inputs helper4Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.numerical Numerical.fieldInverse "koala-bear.ext8-binomial3" "")) (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

abbrev helper5Helper : Helper :=
  ⟨"zkl_ba5165e8a5166d242bec0ad9c1a2d8b4be9869965e35cf771ca0cdc9860d6769", .math, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3")]⟩

def helper5Body : Region dialect helper5Helper.inputs helper5Helper.outputs :=
  .ret (.cons .here .nil)

abbrev helper6Helper : Helper :=
  ⟨"zkl_91a9aadf1b0fc93d864d1fb54700c603b5573e69038cd1eb2fa4c116d5288df4", .local, [(.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")]⟩

def helper6Body : Region dialect helper6Helper.inputs helper6Helper.outputs :=
  .ret (.cons .here .nil)

abbrev helper7Helper : Helper :=
  ⟨"zkl_1a2e4785483066d8b0fd3368b37363fe403d5142f89276ff62679d35b3d441f5", .math, [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index, .index], [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index]⟩

def helper7Body : Region dialect helper7Helper.inputs helper7Helper.outputs :=
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp .indexBitAnd (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "koala-bear.ext8-binomial3") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .letOp (.select (.field "koala-bear.ext8-binomial3")) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.fieldMultiply "koala-bear.ext8-binomial3") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp .indexLogicalShiftRight (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) (.cons .here .nil)))

abbrev helper8Helper : Helper :=
  ⟨"finite_zkl_7687774cc1014f46884b89c91fc63d3def7566efa921884515ed50af7c46dfca_s5_body", .math, [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index, .index, .index, .index], [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index]⟩

def helper8Body : Region dialect helper8Helper.inputs helper8Helper.outputs :=
  .letOp (.invoke (⟨ "zkl_1a2e4785483066d8b0fd3368b37363fe403d5142f89276ff62679d35b3d441f5", .math, [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index, .index], [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index] ⟩ : Helper)) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)))

abbrev helper9Helper : Helper :=
  ⟨"s3h7a6b637h696e646963657314h6269745f77696474685f68616c66", .math, [.index, .index, .index], [.index, .index]⟩

def helper9Body : Region dialect helper9Helper.inputs helper9Helper.outputs :=
  .letOp .indexLogicalShiftRight (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.indexConstant 0) .nil .nil <|
  .letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.select .index) (.cons .here (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp .indexWrappingAdd (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.select .index) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here .nil))) .nil <|
  .ret (.cons (.there (.there .here)) (.cons .here .nil))

abbrev helper10Helper : Helper :=
  ⟨"s3h7a6b637h696e64696365739h6269745f7769647468", .math, [.index], [.index]⟩

def helper10Body : Region dialect helper10Helper.inputs helper10Helper.outputs :=
  .letOp (.indexConstant 0) .nil .nil <|
  .letOp (.indexConstant 32) .nil .nil <|
  .letOp (.invoke (⟨ "s3h7a6b637h696e646963657314h6269745f77696474685f68616c66", .math, [.index, .index, .index], [.index, .index] ⟩ : Helper)) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))) .nil <|
  .letOp (.indexConstant 16) .nil .nil <|
  .letOp (.invoke (⟨ "s3h7a6b637h696e646963657314h6269745f77696474685f68616c66", .math, [.index, .index, .index], [.index, .index] ⟩ : Helper)) (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here .nil))) .nil <|
  .letOp (.indexConstant 8) .nil .nil <|
  .letOp (.invoke (⟨ "s3h7a6b637h696e646963657314h6269745f77696474685f68616c66", .math, [.index, .index, .index], [.index, .index] ⟩ : Helper)) (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here .nil))) .nil <|
  .letOp (.indexConstant 4) .nil .nil <|
  .letOp (.invoke (⟨ "s3h7a6b637h696e646963657314h6269745f77696474685f68616c66", .math, [.index, .index, .index], [.index, .index] ⟩ : Helper)) (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here .nil))) .nil <|
  .letOp (.indexConstant 2) .nil .nil <|
  .letOp (.invoke (⟨ "s3h7a6b637h696e646963657314h6269745f77696474685f68616c66", .math, [.index, .index, .index], [.index, .index] ⟩ : Helper)) (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here .nil))) .nil <|
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp (.invoke (⟨ "s3h7a6b637h696e646963657314h6269745f77696474685f68616c66", .math, [.index, .index, .index], [.index, .index] ⟩ : Helper)) (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here .nil))) .nil <|
  .letOp (.indexConstant 0) .nil .nil <|
  .letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.indexConstant 0) .nil .nil <|
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp .indexWrappingAdd (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .letOp (.select .index) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) (.cons .here .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev helper11Helper : Helper :=
  ⟨"zkl_7687774cc1014f46884b89c91fc63d3def7566efa921884515ed50af7c46dfca", .math, [(.field "koala-bear.ext8-binomial3"), .index], [(.field "koala-bear.ext8-binomial3")]⟩

def helper11Body : Region dialect helper11Helper.inputs helper11Helper.outputs :=
  .letOp (.fieldConstant "koala-bear.ext8-binomial3" 1) .nil .nil <|
  .letOp (.indexConstant 0) .nil .nil <|
  .letOp (.invoke (⟨ "s3h7a6b637h696e64696365739h6269745f7769647468", .math, [.index], [.index] ⟩ : Helper)) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.fold ⟨⟨ "finite_zkl_7687774cc1014f46884b89c91fc63d3def7566efa921884515ed50af7c46dfca_s5_domain", [.index, .index], [.index], (.letNode (.range .here (.there .here)) (.ret .here)) ⟩, [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index], [], "finite_zkl_7687774cc1014f46884b89c91fc63d3def7566efa921884515ed50af7c46dfca_s5_body", "", .math⟩) (.cons (.there .here) (.cons .here (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil))))) .nil <|
  .ret (.cons .here .nil)

abbrev helper12Helper : Helper :=
  ⟨"zkl_0f373e04763f76f5bc854b8bf9c944c1196fd15a82dfad4ad61d1f7bedb50c63", .math, [.index, (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [.boolean]⟩

def helper12Body : Region dialect helper12Helper.inputs helper12Helper.outputs :=
  .letOp (.indexConstant 0) .nil .nil <|
  .letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .letOp .booleanEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.branch [.index] [.boolean]) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) (.cons (.letOp (.indexConstant 1) .nil .nil (.letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.booleanConstant false) .nil .nil (.letOp .booleanEqual (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) (.cons (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil))) .nil)) <|
  .letOp (.branch [.index] [.boolean]) (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)) (.cons (.letOp (.indexConstant 1) .nil .nil (.letOp .indexWrappingSubtract (.cons (.there .here) (.cons .here .nil)) .nil (.letOp .indexBitAnd (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.letOp (.indexConstant 0) .nil .nil (.letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))))) (.cons (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil))) .nil)) <|
  .letOp (.branch [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")] [.boolean]) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil))) (.cons (.letOp (.fieldMultiply "koala-bear.ext8-binomial3") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.fieldConstant "koala-bear.ext8-binomial3" 1) .nil .nil (.letOp (.fieldEqual "koala-bear.ext8-binomial3") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))) (.cons (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil))) .nil)) <|
  .letOp (.branch [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")] [.boolean]) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil))) (.cons (.letOp (.fieldMultiply "koala-bear.ext8-binomial3") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.fieldConstant "koala-bear.ext8-binomial3" 1) .nil .nil (.letOp (.fieldEqual "koala-bear.ext8-binomial3") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))) (.cons (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil))) .nil)) <|
  .letOp (.branch [(.field "koala-bear.ext8-binomial3")] [.boolean]) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil)) (.cons (.letOp (.fieldConstant "koala-bear.ext8-binomial3" 1) .nil .nil (.letOp (.fieldConstant "koala-bear.ext8-binomial3" 1) .nil .nil (.letOp (.fieldAdd "koala-bear.ext8-binomial3") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldMultiply "koala-bear.ext8-binomial3") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil (.letOp (.fieldConstant "koala-bear.ext8-binomial3" 1) .nil .nil (.letOp (.fieldEqual "koala-bear.ext8-binomial3") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))))) (.cons (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil))) .nil)) <|
  .letOp (.branch [.index, (.field "koala-bear.ext8-binomial3")] [.boolean]) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil))) (.cons (.letOp (.indexConstant 1) .nil .nil (.letOp .indexLogicalShiftRight (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.invoke (⟨ "zkl_7687774cc1014f46884b89c91fc63d3def7566efa921884515ed50af7c46dfca", .math, [(.field "koala-bear.ext8-binomial3"), .index], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper)) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil (.letOp (.fieldConstant "koala-bear.ext8-binomial3" 0) .nil .nil (.letOp (.fieldConstant "koala-bear.ext8-binomial3" 1) .nil .nil (.letOp (.fieldSubtract "koala-bear.ext8-binomial3") (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldEqual "koala-bear.ext8-binomial3") (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))))))) (.cons (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil))) .nil)) <|
  .letOp (.branch [.index, (.field "koala-bear.ext8-binomial3")] [.boolean]) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil))) (.cons (.letOp (.invoke (⟨ "zkl_7687774cc1014f46884b89c91fc63d3def7566efa921884515ed50af7c46dfca", .math, [(.field "koala-bear.ext8-binomial3"), .index], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper)) (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.fieldConstant "koala-bear.ext8-binomial3" 1) .nil .nil (.letOp (.fieldEqual "koala-bear.ext8-binomial3") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))) (.cons (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil))) .nil)) <|
  .ret (.cons .here .nil)

abbrev formulaHelper : Helper :=
  ⟨"zkf_7132273e83171bd86b37e02daf08f6a3cd8013f7f59ad6856e3fa898be443c3a", .math, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index, .index, (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [.boolean]⟩

def formulaBody : Region dialect formulaHelper.inputs formulaHelper.outputs :=
  .letOp (.vectorLength "koala-bear.ext8-binomial3") (.cons .here .nil) .nil <|
  .letOp .indexEqual (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp .indexLogicalShiftRight (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .letOp .indexEqual (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.invoke (⟨ "zkl_0f373e04763f76f5bc854b8bf9c944c1196fd15a82dfad4ad61d1f7bedb50c63", .math, [.index, (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [.boolean] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)))))) .nil <|
  .letOp .booleanAnd (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.vectorLength "koala-bear.ext8-binomial3") (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil) .nil <|
  .letOp (.indexConstant 32) .nil .nil <|
  .letOp .indexLess (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.vectorLength "koala-bear.ext8-binomial3") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil) .nil <|
  .letOp (.indexConstant 32) .nil .nil <|
  .letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp .booleanOr (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper14Helper : Helper :=
  ⟨"s3h6672698h706169725f6c6f77", .math, [.index, .index], [.index]⟩

def helper14Body : Region dialect helper14Helper.inputs helper14Helper.outputs :=
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp .indexLogicalShiftRight (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.indexConstant 1) .nil .nil <|
  .letOp .indexWrappingSubtract (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp .indexBitAnd (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper15Helper : Helper :=
  ⟨"zkl_1d5c68c5e36ee11e4cbcec8bd6616e4424fe384afe270d5217a19883323f5700", .math, [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")]⟩

def helper15Body : Region dialect helper15Helper.inputs helper15Helper.outputs :=
  .letOp (.fieldAdd "koala-bear.ext8-binomial3") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.fieldMultiply "koala-bear.ext8-binomial3") (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.fieldSubtract "koala-bear.ext8-binomial3") (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.fieldMultiply "koala-bear.ext8-binomial3") (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil <|
  .letOp (.fieldMultiply "koala-bear.ext8-binomial3") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.fieldMultiply "koala-bear.ext8-binomial3") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil <|
  .letOp (.fieldAdd "koala-bear.ext8-binomial3") (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper16Helper : Helper :=
  ⟨"zkl_aa0aec6615d49a948ab374adba233e906c2c6967a94858613b3ca4ddd06904c6", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")]⟩

def helper16Body : Region dialect helper16Helper.inputs helper16Helper.outputs :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.numerical Numerical.polyFold "koala-bear.ext8-binomial3" "")) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.fieldMultiply "koala-bear.ext8-binomial3") (.cons (.there (.there .here)) (.cons (.there (.there .here)) .nil)) .nil <|
  .ret (.cons (.there .here) (.cons .here .nil))

abbrev helper17Helper : Helper :=
  ⟨"zkl_3fc484f212417cf1807e4e56c56ebcd4de56544c720736160173309d3a8308a3", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.polynomial "koala-bear.ext8-binomial3")]⟩

def helper17Body : Region dialect helper17Helper.inputs helper17Helper.outputs :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.numerical Numerical.polyInterpolate "koala-bear.ext8-binomial3" "")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper18Helper : Helper :=
  ⟨"zkl_817516c442f78c72df2638838067ebdfea021bffc66f35fc6a1e0fd1f5063abe", .local, [(.polynomial "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3")]⟩

def helper18Body : Region dialect helper18Helper.inputs helper18Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.numerical Numerical.polyCoefficients "koala-bear.ext8-binomial3" "")) (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

abbrev helper19Helper : Helper :=
  ⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩

def helper19Body : Region dialect helper19Helper.inputs helper19Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec .indexLess) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper20Helper : Helper :=
  ⟨"zkl_5685869750c28f21075e099f486dad29b7b6b0af87dc894c64e1f0b87c6f4f83", .local, [(.vector "koala-bear.ext8-binomial3"), (.vector "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3")]⟩

def helper20Body : Region dialect helper20Helper.inputs helper20Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.numerical Numerical.vectorConcat "koala-bear.ext8-binomial3" "")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper21Helper : Helper :=
  ⟨"zkl_e89a50287c9ee2bddba5ca02644e8e82b28f07304dc3bcccad00744aeea36fda", .local, [(.vector "koala-bear.ext8-binomial3"), .index], [(.vector "koala-bear.ext8-binomial3")]⟩

def helper21Body : Region dialect helper21Helper.inputs helper21Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorLength "koala-bear.ext8-binomial3")) (.cons .here .nil) .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.invoke (⟨ "s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean] ⟩ : Helper)) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.booleanConstant false) .nil .nil <|
  .letOp (.mark "s3_both") .nil .nil <|
  .letOp .booleanAnd (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s3_left") .nil .nil <|
  .letOp (.exec .booleanNot) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "s3_right") .nil .nil <|
  .letOp (.exec .booleanNot) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "s3_neither") .nil .nil <|
  .letOp .booleanAnd (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp .booleanOr (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.branch [] []) (.cons .here .nil) (.cons (.ret .nil) (.cons (.letOp (.mark "s4_reject") .nil .nil (.stop .reject)) .nil)) <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.fieldConstant "koala-bear.ext8-binomial3" 0) .nil .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.exec (.vectorLength "koala-bear.ext8-binomial3")) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec .indexSub) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.exec (.numerical Numerical.vectorFill "koala-bear.ext8-binomial3" "")) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_5685869750c28f21075e099f486dad29b7b6b0af87dc894c64e1f0b87c6f4f83", .local, [(.vector "koala-bear.ext8-binomial3"), (.vector "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3")] ⟩ : Helper)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper22Helper : Helper :=
  ⟨"s3h7a6b6310h7072696d6974697665737h696e64696365735h656d707479", .local, [], [.indices]⟩

def helper22Body : Region dialect helper22Helper.inputs helper22Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.numerical Numerical.indicesEmpty "" "")) .nil .nil <|
  .ret (.cons .here .nil)

abbrev helper23Helper : Helper :=
  ⟨"s3h7a6b6310h7072696d6974697665737h696e64696365736h617070656e64", .local, [.indices, .index], [.indices]⟩

def helper23Body : Region dialect helper23Helper.inputs helper23Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.numerical Numerical.indicesAppend "" "")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper24Helper : Helper :=
  ⟨"s3h7a6b6310h7072696d6974697665737h696e64696365736h6c656e677468", .local, [.indices], [.index]⟩

def helper24Body : Region dialect helper24Helper.inputs helper24Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.numerical Numerical.indicesLength "" "")) (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

abbrev helper25Helper : Helper :=
  ⟨"s3h66726917h626f756e6465645f706f736974696f6e73", .local, [.indices, .index], [.boolean]⟩

def helper25Body : Region dialect helper25Helper.inputs helper25Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.booleanConstant true) .nil .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 0)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.numerical Numerical.indicesLength "" "")) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.loop [.boolean] [.indices, .index]) (.cons (.there .here) (.cons .here (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil))))) (.cons (.letOp (.mark "s7") .nil .nil (.letOp (.exec (.numerical Numerical.indicesAt "" "")) (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.letOp (.mark "s11") .nil .nil (.letOp (.branch [.index, .index] [.boolean]) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil))) (.cons (.letOp (.mark "s12") .nil .nil (.letOp (.invoke (⟨ "s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean] ⟩ : Helper)) (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))) (.cons (.letOp (.mark "s14") .nil .nil (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil)))) .nil)) (.ret (.cons .here (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))))) .nil) <|
  .ret (.cons .here .nil)

abbrev helper26Helper : Helper :=
  ⟨"zkl_a020b68fa3c7229c3a465edef5f5e01391f88527db4b82d2b62005f9ced9ff86", .local, [], [(.vector "koala-bear.ext8-binomial3")]⟩

def helper26Body : Region dialect helper26Helper.inputs helper26Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorEmpty "koala-bear.ext8-binomial3")) .nil .nil <|
  .ret (.cons .here .nil)

abbrev helper27Helper : Helper :=
  ⟨"zkl_d996c673878fadd82bc5da874ec28c7e0038e1489dbd5901f3eaef6a271fde3e", .math, [.index, .index], [.boolean]⟩

def helper27Body : Region dialect helper27Helper.inputs helper27Helper.outputs :=
  .letOp (.indexConstant 3) .nil .nil <|
  .letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.branch [.index] [.boolean]) (.cons .here (.cons (.there (.there (.there .here))) .nil)) (.cons (.letOp (.indexConstant 8) .nil .nil (.letOp .indexEqual (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))) (.cons (.letOp (.booleanConstant false) .nil .nil (.ret (.cons .here .nil))) .nil)) <|
  .ret (.cons .here .nil)

abbrev helper28Helper : Helper :=
  ⟨"zkl_c6bd4a70513c0e60a81af5917db503ec406ca6b7bc6e2fdcce6b66384a2bcc40", .math, [(.field "koala-bear.ext8-binomial3"), .index], [.index]⟩

def helper28Body : Region dialect helper28Helper.inputs helper28Helper.outputs :=
  .ret (.cons (.there .here) .nil)

abbrev helper29Helper : Helper :=
  ⟨"zkl_59770f895f4a65e43d6bfdf2cbc5814fe95b7e42f1c760b4bf05d976566f4545", .local, [.boolean, (.vector "koala-bear.ext8-binomial3"), .index], [.boolean]⟩

def helper29Body : Region dialect helper29Helper.inputs helper29Helper.outputs :=
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.branch [(.vector "koala-bear.ext8-binomial3"), .index] [.boolean]) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) (.cons (.letOp (.mark "s3") .nil .nil (.letOp (.exec (.vectorLength "koala-bear.ext8-binomial3")) (.cons .here .nil) .nil (.letOp (.mark "s4") .nil .nil (.letOp (.exec .indexEqual) (.cons .here (.cons (.there (.there .here)) .nil)) .nil (.ret (.cons .here .nil)))))) (.cons (.letOp (.mark "s6") .nil .nil (.letOp (.booleanConstant true) .nil .nil (.ret (.cons .here .nil)))) .nil)) <|
  .ret (.cons .here .nil)

abbrev helper30Helper : Helper :=
  ⟨"s3h7a6b6310h7072696d6974697665737h696e64696365733h676574", .local, [.indices, .index], [.index]⟩

def helper30Body : Region dialect helper30Helper.inputs helper30Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.numerical Numerical.indicesAt "" "")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper31Helper : Helper :=
  ⟨"zkl_a4de6c653f3dd98800c1f0f224fb298886bf002c3b67044fb5d4d3400ec6d6d4", .local, [.boolean, (.vector "koala-bear.ext8-binomial3"), .index, (.field "koala-bear.ext8-binomial3")], [.boolean]⟩

def helper31Body : Region dialect helper31Helper.inputs helper31Helper.outputs :=
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.branch [(.vector "koala-bear.ext8-binomial3"), .index, (.field "koala-bear.ext8-binomial3")] [.boolean]) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)))) (.cons (.letOp (.mark "s4") .nil .nil (.letOp (.exec (.numerical Numerical.vectorGet "koala-bear.ext8-binomial3" "")) (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "s5") .nil .nil (.letOp (.exec (.fieldEqual "koala-bear.ext8-binomial3")) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) (.cons (.letOp (.mark "s7") .nil .nil (.letOp (.booleanConstant true) .nil .nil (.ret (.cons .here .nil)))) .nil)) <|
  .ret (.cons .here .nil)

abbrev helper32Helper : Helper :=
  ⟨"zkl_daa4cc1b0228f87a89c04d62b4b161ffd93cfdc07ffcd4c34bb70b214836fc85", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3")]⟩

def helper32Body : Region dialect helper32Helper.inputs helper32Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorAppend "koala-bear.ext8-binomial3")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper33Helper : Helper :=
  ⟨"zkl_262408e7c1d541225e833ebfbee1716171d6581b8912fbf3dd09c1587c9cb24d", .math, [(.field "koala-bear.ext8-binomial3"), .index], [(.field "koala-bear.ext8-binomial3")]⟩

def helper33Body : Region dialect helper33Helper.inputs helper33Helper.outputs :=
  .ret (.cons .here .nil)

abbrev helper34Helper : Helper :=
  ⟨"zkl_3b188f0dc9463b9d6a8a79a883c9e7fdbb2156a82f23d60b58e9faf7820076cd", .local, [(.vector "koala-bear.ext8-binomial3")], [(.polynomial "koala-bear.ext8-binomial3")]⟩

def helper34Body : Region dialect helper34Helper.inputs helper34Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.numerical Numerical.polyFromCoefficients "koala-bear.ext8-binomial3" "")) (.cons .here .nil) .nil <|
  .ret (.cons .here .nil)

abbrev helper35Helper : Helper :=
  ⟨"zkl_5c318b2e032d1e0f9a2f55b8815b11755921d7ae0813e90fab4342215729000c", .local, [(.polynomial "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")]⟩

def helper35Body : Region dialect helper35Helper.inputs helper35Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.numerical Numerical.polyEvaluate "koala-bear.ext8-binomial3" "")) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev helper36Helper : Helper :=
  ⟨"zkl_a2cb18beedc26c3b2940b6a483d3dac2dfdfc2ee3b57a534fa8a67065bc2fc54", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index, .index], [(.field "koala-bear.ext8-binomial3")]⟩

def helper36Body : Region dialect helper36Helper.inputs helper36Helper.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_3b188f0dc9463b9d6a8a79a883c9e7fdbb2156a82f23d60b58e9faf7820076cd", .local, [(.vector "koala-bear.ext8-binomial3")], [(.polynomial "koala-bear.ext8-binomial3")] ⟩ : Helper)) (.cons .here .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.numerical Numerical.polyPoint "koala-bear.ext8-binomial3" "")) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil))) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.invoke (⟨ "zkl_5c318b2e032d1e0f9a2f55b8815b11755921d7ae0813e90fab4342215729000c", .local, [(.polynomial "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper)) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def protocol0Signature : ProtocolSignature where
  name := "zkl_027a2c514d3bdf8305ddf3314b67ffc4a92fb3fe0b021880127a83013a686404"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index, (.service "random.koala-bear.ext8-binomial3/0")]
  outputs := [(.vector "koala-bear.ext8-binomial3"), (.oracle (.table (.field "koala-bear.ext8-binomial3") none)), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.field "koala-bear.ext8-binomial3"), .index, (.vector "koala-bear.ext8-binomial3"), .index]
  inputScopes := [[0], [0], [1], [0, 1], [1]]
  outputScopes := [[0], [1], [0], [1], [0], [1], [0, 1], [0, 1], [0, 1], [0, 1]]

def protocol0Body : Region protocolDialect protocol0Signature.inputs protocol0Signature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 3) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.guard 1 "s2") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 3) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.guard 0 "s5") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 32) rfl) .nil .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_efc5ece4a9b8074e3e7d2a732607ad124d6dff15f36a8e9dc596d88df0573550", .local, [(.vector "koala-bear.ext8-binomial3")], [.index] ⟩ : Helper) rfl 0 "s8") (.cons (.there (.there (.there (.there (.there .here))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "s10") .nil .nil <|
  .letOp (.guard 0 "s10") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.assemble (.field "koala-bear.ext8-binomial3") [0, 1]) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil <|
  .letOp (.mark "s13") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_c3169a788d16114055a6dcd17778ae22d9676c00065943d6b8246ea4c514dfa6", .local, [(.field "koala-bear.ext8-binomial3"), .index], [(.field "koala-bear.ext8-binomial3"), .index] ⟩ : Helper) rfl 0 "s13") (.cons .here (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "s15") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_c3169a788d16114055a6dcd17778ae22d9676c00065943d6b8246ea4c514dfa6", .local, [(.field "koala-bear.ext8-binomial3"), .index], [(.field "koala-bear.ext8-binomial3"), .index] ⟩ : Helper) rfl 1 "s15") (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.assemble (.field "koala-bear.ext8-binomial3") [0, 1]) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.assemble .index [0, 1]) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.mark "s19") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_c97799520c7003578d28af2a16eeebea354b88059ae6ee44e5912a4212abf651", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 0 "s19") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.sequenceEmpty (.table (.field "koala-bear.ext8-binomial3") none) 3 [0, 1]) ⟨⟨2, [] ⟩, 2, [7, 1, 16] ⟩) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.sequenceEmpty (.table (.field "koala-bear.ext8-binomial3") none) 3 [0, 1]) ⟨⟨2, [] ⟩, 2, [7, 1, 17] ⟩) .nil .nil <|
  .letOp (.mark "s27") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_82d4f61df0504a5e4381e3fd226e2a5b64bf67e87429b2feabc0d4ed0629be57", .local, [.index], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 0 "s27") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil) .nil <|
  .letOp (.mark "s29") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_82d4f61df0504a5e4381e3fd226e2a5b64bf67e87429b2feabc0d4ed0629be57", .local, [.index], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 1 "s29") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.assemble (.field "koala-bear.ext8-binomial3") [0, 1]) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldConstant "koala-bear.ext8-binomial3" 1) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldConstant "koala-bear.ext8-binomial3" 1) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "koala-bear.ext8-binomial3") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s36") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_a14c556d4abc6083c08616c54f7346c2cf2a3ae5f52aa3d4d28b079f9c3d719f", .local, [(.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 0 "s36") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldConstant "koala-bear.ext8-binomial3" 1) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldConstant "koala-bear.ext8-binomial3" 1) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "koala-bear.ext8-binomial3") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s41") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_a14c556d4abc6083c08616c54f7346c2cf2a3ae5f52aa3d4d28b079f9c3d719f", .local, [(.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 1 "s41") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.assemble (.field "koala-bear.ext8-binomial3") [0, 1]) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s46") .nil .nil <|
  .letOp (.repeat (⟨ [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), .index, (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3"), (.service "random.koala-bear.ext8-binomial3/0")], [0, 1], [[0], [0], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]], 3⟩ : RepeatSpec) "s46") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))) .nil)))))))))) (.cons (.letOp (.mark "") .nil .nil (.letOp (.calculate (.invoke (⟨ "zkl_ba5165e8a5166d242bec0ad9c1a2d8b4be9869965e35cf771ca0cdc9860d6769", .math, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3")] ⟩ : Helper)) rfl) (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil (.letOp (.mark "s49") .nil .nil (.letOp (.oracle (.send (.table (.field "koala-bear.ext8-binomial3") none) 0 [1] [("rows", 32)]) ⟨⟨2, [] ⟩, 2, [7, 1, 30, 4, 0, 3, 1, 1] ⟩) (.cons .here (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil (.letOp (.mark "s51") .nil .nil (.letOp (.oracle (.sequenceAppend (.table (.field "koala-bear.ext8-binomial3") none) 3 [0, 1]) ⟨⟨2, [] ⟩, 2, [7, 1, 30, 4, 0, 3, 1, 2] ⟩) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)) .nil (.letOp (.mark "s54") .nil .nil (.letOp (.draw 1 "koala-bear.ext8-binomial3" "s54") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil) .nil (.letOp (.mark "s56_0") .nil .nil (.letOp (.exchange (.field "koala-bear.ext8-binomial3") 1 0 "s56_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "koala-bear.ext8-binomial3") [0]) (.cons .here .nil) .nil (.letOp (.mark "s58") .nil .nil (.letOp (.localCall (⟨ "zkl_91a9aadf1b0fc93d864d1fb54700c603b5573e69038cd1eb2fa4c116d5288df4", .local, [(.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 0 "s58") (.cons .here .nil) .nil (.letOp (.mark "s60") .nil .nil (.letOp (.localCall (⟨ "zkl_91a9aadf1b0fc93d864d1fb54700c603b5573e69038cd1eb2fa4c116d5288df4", .local, [(.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 1 "s60") (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.assemble (.field "koala-bear.ext8-binomial3") [0, 1]) (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.oracle (.shape (.table (.field "koala-bear.ext8-binomial3") none) "rows") ⟨⟨2, [] ⟩, 2, [7, 1, 30, 4, 0, 3, 1, 9] ⟩) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate .indexEqual rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil)) .nil (.letOp (.mark "s67") .nil .nil (.letOp (.guard 0 "s67") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) .nil)) .nil (.letOp (.mark "s69") .nil .nil (.letOp (.guard 1 "s69") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.indexConstant 1) rfl) .nil .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate .indexLogicalShiftRight rfl) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil (.letOp (.mark "s73") .nil .nil (.letOp (.localCall (⟨ "zkl_82d4f61df0504a5e4381e3fd226e2a5b64bf67e87429b2feabc0d4ed0629be57", .local, [.index], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 0 "s73") (.cons (.there (.there (.there (.there .here)))) .nil) .nil (.letOp (.mark "s75") .nil .nil (.letOp (.localCall (⟨ "zkl_82d4f61df0504a5e4381e3fd226e2a5b64bf67e87429b2feabc0d4ed0629be57", .local, [.index], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 1 "s75") (.cons (.there (.there (.there (.there (.there .here))))) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldEqual "koala-bear.ext8-binomial3") rfl) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))) .nil)) .nil (.letOp (.mark "s78") .nil .nil (.letOp (.guard 0 "s78") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldEqual "koala-bear.ext8-binomial3") rfl) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))) .nil)) .nil (.letOp (.mark "s80") .nil .nil (.letOp (.guard 1 "s80") (.cons .here .nil) .nil (.letOp (.mark "s81") .nil .nil (.letOp (.localCall (⟨ "zkl_a14c556d4abc6083c08616c54f7346c2cf2a3ae5f52aa3d4d28b079f9c3d719f", .local, [(.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 0 "s81") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))) .nil) .nil (.letOp (.mark "s83") .nil .nil (.letOp (.localCall (⟨ "zkl_a14c556d4abc6083c08616c54f7346c2cf2a3ae5f52aa3d4d28b079f9c3d719f", .local, [(.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 1 "s83") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.assemble (.field "koala-bear.ext8-binomial3") [0, 1]) (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.mark "s87") .nil .nil (.letOp (.localCall (⟨ "zkl_a14c556d4abc6083c08616c54f7346c2cf2a3ae5f52aa3d4d28b079f9c3d719f", .local, [(.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 0 "s87") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))) .nil) .nil (.letOp (.mark "s89") .nil .nil (.letOp (.localCall (⟨ "zkl_a14c556d4abc6083c08616c54f7346c2cf2a3ae5f52aa3d4d28b079f9c3d719f", .local, [(.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 1 "s89") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.assemble (.field "koala-bear.ext8-binomial3") [0, 1]) (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.invoke (⟨ "zkl_0f373e04763f76f5bc854b8bf9c944c1196fd15a82dfad4ad61d1f7bedb50c63", .math, [.index, (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [.boolean] ⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))) .nil)))))) .nil (.letOp (.mark "s94") .nil .nil (.letOp (.guard 0 "s94") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.invoke (⟨ "zkl_0f373e04763f76f5bc854b8bf9c944c1196fd15a82dfad4ad61d1f7bedb50c63", .math, [.index, (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [.boolean] ⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))) .nil)))))) .nil (.letOp (.mark "s96") .nil .nil (.letOp (.guard 1 "s96") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.oracle (.virtual ⟨ "zkl_31951b707ccfb62c7ac7e26ab2036ae9b332cef26f2c1a9300411ee5fea235f4", [(.oracle (.table (.field "koala-bear.ext8-binomial3") none)), (.field "koala-bear.ext8-binomial3"), .index, .index, (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index], (.table (.field "koala-bear.ext8-binomial3") none), "zkl_49518c8ca28853d5308e4676cd87321c967360523046281374cc9e81874fbdd3", [("rows", 3)], [("rows", 32)] ⟩ 0 [1]) ⟨⟨2, [] ⟩, 2, [7, 1, 30, 4, 0, 3, 1, 32] ⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))) .nil))))))))) .nil (.letOp (.mark "s99") .nil .nil (.letOp (.oracle (.sequenceAppend (.table (.field "koala-bear.ext8-binomial3") none) 3 [0, 1]) ⟨⟨2, [] ⟩, 2, [7, 1, 30, 4, 0, 3, 1, 33] ⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))) (.cons .here .nil)) .nil (.letOp (.mark "s102") .nil .nil (.letOp (.localCall (⟨ "zkl_aa0aec6615d49a948ab374adba233e906c2c6967a94858613b3ca4ddd06904c6", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 0 "s102") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) .nil))) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "koala-bear.ext8-binomial3") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "koala-bear.ext8-binomial3") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))) .nil)) .nil (.ret (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.there .here) (.cons .here .nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) .nil) <|
  .letOp (.mark "s112") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_82d4f61df0504a5e4381e3fd226e2a5b64bf67e87429b2feabc0d4ed0629be57", .local, [.index], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 0 "s112") (.cons (.there (.there (.there (.there .here)))) .nil) .nil <|
  .letOp (.mark "s114") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_82d4f61df0504a5e4381e3fd226e2a5b64bf67e87429b2feabc0d4ed0629be57", .local, [.index], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 1 "s114") (.cons (.there (.there (.there (.there (.there .here))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldEqual "koala-bear.ext8-binomial3") rfl) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) .nil <|
  .letOp (.mark "s117") .nil .nil <|
  .letOp (.guard 0 "s117") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldEqual "koala-bear.ext8-binomial3") rfl) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil <|
  .letOp (.mark "s119") .nil .nil <|
  .letOp (.guard 1 "s119") (.cons .here .nil) .nil <|
  .letOp (.mark "s120") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_3fc484f212417cf1807e4e56c56ebcd4de56544c720736160173309d3a8308a3", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.polynomial "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 0 "s120") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .letOp (.mark "s121") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_817516c442f78c72df2638838067ebdfea021bffc66f35fc6a1e0fd1f5063abe", .local, [(.polynomial "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 0 "s121") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "s123") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_e89a50287c9ee2bddba5ca02644e8e82b28f07304dc3bcccad00744aeea36fda", .local, [(.vector "koala-bear.ext8-binomial3"), .index], [(.vector "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 0 "s123") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s125_0") .nil .nil <|
  .letOp (.exchange (.vector "koala-bear.ext8-binomial3") 0 1 "s125_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.vector "koala-bear.ext8-binomial3") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "s127") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_efc5ece4a9b8074e3e7d2a732607ad124d6dff15f36a8e9dc596d88df0573550", .local, [(.vector "koala-bear.ext8-binomial3")], [.index] ⟩ : Helper) rfl 1 "s127") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s130") .nil .nil <|
  .letOp (.guard 1 "s130") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.assemble (.vector "koala-bear.ext8-binomial3") [0, 1]) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 0) rfl) .nil .nil <|
  .letOp (.mark "s134") .nil .nil <|
  .letOp (.oracle (.sequenceAt (.table (.field "koala-bear.ext8-binomial3") none) 3 [0, 1]) ⟨⟨2, [] ⟩, 2, [7, 1, 49] ⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.singleton (.table (.field "koala-bear.ext8-binomial3") none)) 0 [1]) ⟨⟨2, [] ⟩, 2, [7, 1, 50] ⟩) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1]) ⟨⟨2, [] ⟩, 2, [7, 1, 51] ⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1]) ⟨⟨2, [] ⟩, 2, [7, 1, 52] ⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))) .nil) .nil <|
  .ret (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) .nil))))))))))

def protocol1Signature : ProtocolSignature where
  name := "zkl_5bdb55a745abe137c9027bb7f7baa1d02e1dde834266d27198609cdbce18f830"
  roles := ["role00000000", "role00000001"]
  inputs := [.index, (.service "random.koala-bear.ext8-binomial3/0")]
  outputs := [.indices]
  inputScopes := [[0, 1], [1]]
  outputScopes := [[0, 1]]

def protocol1Body : Region protocolDialect protocol1Signature.inputs protocol1Signature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 8) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.guard 1 "s2") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 8) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.guard 0 "s5") (.cons .here .nil) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b6310h7072696d6974697665737h696e64696365735h656d707479", .local, [], [.indices] ⟩ : Helper) rfl 0 "s6") .nil .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b6310h7072696d6974697665737h696e64696365735h656d707479", .local, [], [.indices] ⟩ : Helper) rfl 1 "s8") .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.assemble .indices [0, 1]) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s12") .nil .nil <|
  .letOp (.repeat (⟨ [.indices], [(.service "random.koala-bear.ext8-binomial3/0")], [0, 1], [[0, 1]], 8⟩ : RepeatSpec) "s12") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))) (.cons (.letOp (.mark "") .nil .nil (.letOp (.calculate (.indexConstant 32) rfl) .nil .nil (.letOp (.mark "s13") .nil .nil (.letOp (.query 1 (.sampleIndex "random.koala-bear.ext8-binomial3/0") "s13") (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil (.letOp (.mark "s15_0") .nil .nil (.letOp (.exchange .index 1 0 "s15_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict .index [0]) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.assemble .index [0, 1]) (.cons .here (.cons (.there (.there .here)) .nil)) .nil (.letOp (.mark "s19") .nil .nil (.letOp (.localCall (⟨ "s3h7a6b6310h7072696d6974697665737h696e64696365736h617070656e64", .local, [.indices, .index], [.indices] ⟩ : Helper) rfl 0 "s19") (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here .nil)) .nil (.letOp (.mark "s21") .nil .nil (.letOp (.localCall (⟨ "s3h7a6b6310h7072696d6974697665737h696e64696365736h617070656e64", .local, [.indices, .index], [.indices] ⟩ : Helper) rfl 1 "s21") (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there .here) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.assemble .indices [0, 1]) (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))))))))))))))) .nil) <|
  .ret (.cons .here .nil)

def protocol2Signature : ProtocolSignature where
  name := "zkl_fe1dbc0863e9ce6597f78199145977ba10bcf6691b6ad36d1041feedc52b31f6"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "koala-bear.ext8-binomial3"), (.oracle (.table (.field "koala-bear.ext8-binomial3") none)), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.field "koala-bear.ext8-binomial3"), .index, (.vector "koala-bear.ext8-binomial3"), .index, .indices]
  outputs := [(.vector "koala-bear.ext8-binomial3"), (.oracle (.table (.field "koala-bear.ext8-binomial3") none)), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.field "koala-bear.ext8-binomial3"), .index, (.vector "koala-bear.ext8-binomial3"), .indices, .index, .index]
  inputScopes := [[0], [1], [0], [1], [0], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]]
  outputScopes := [[0], [1], [0], [1], [0], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]]

def protocol2Body : Region protocolDialect protocol2Signature.inputs protocol2Signature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.singleton (.table (.field "koala-bear.ext8-binomial3") none)) 0 [1] [("rows", 32)]) ⟨⟨29, [] ⟩, 29, [7, 1, 0] ⟩) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1] [("rows", 32)]) ⟨⟨29, [] ⟩, 29, [7, 1, 1] ⟩) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1] [("rows", 32)]) ⟨⟨29, [] ⟩, 29, [7, 1, 2] ⟩) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b6310h7072696d6974697665737h696e64696365736h6c656e677468", .local, [.indices], [.index] ⟩ : Helper) rfl 1 "s0") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 8) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.guard 1 "s3") (.cons .here .nil) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b6310h7072696d6974697665737h696e64696365736h6c656e677468", .local, [.indices], [.index] ⟩ : Helper) rfl 0 "s4") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 8) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.guard 0 "s7") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 32) rfl) .nil .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.localCall (⟨ "s3h66726917h626f756e6465645f706f736974696f6e73", .local, [.indices, .index], [.boolean] ⟩ : Helper) rfl 1 "s9") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.guard 1 "s11") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 32) rfl) .nil .nil <|
  .letOp (.mark "s13") .nil .nil <|
  .letOp (.localCall (⟨ "s3h66726917h626f756e6465645f706f736974696f6e73", .local, [.indices, .index], [.boolean] ⟩ : Helper) rfl 0 "s13") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s15") .nil .nil <|
  .letOp (.guard 0 "s15") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 8) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.singleton (.table (.field "koala-bear.ext8-binomial3") none)) 0 [1]) ⟨⟨29, [] ⟩, 29, [7, 1, 18] ⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1]) ⟨⟨29, [] ⟩, 29, [7, 1, 19] ⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1]) ⟨⟨29, [] ⟩, 29, [7, 1, 20] ⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil) .nil <|
  .ret (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))))))))))))

def protocol3Signature : ProtocolSignature where
  name := "zkl_f7f6685fe66aaf3cf40ed2536ccbcf40f97f242773e81303113589b9da931aa0"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "koala-bear.ext8-binomial3"), (.oracle (.table (.field "koala-bear.ext8-binomial3") none)), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.field "koala-bear.ext8-binomial3"), .index, (.vector "koala-bear.ext8-binomial3"), .indices, .index, .index, .boolean, (.vector "koala-bear.ext8-binomial3")]
  outputs := [.boolean, (.vector "koala-bear.ext8-binomial3")]
  inputScopes := [[0], [1], [0], [1], [0], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [1], [1]]
  outputScopes := [[1], [1]]

def protocol3Body : Region protocolDialect protocol3Signature.inputs protocol3Signature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.singleton (.table (.field "koala-bear.ext8-binomial3") none)) 0 [1] [("rows", 32)]) ⟨⟨34, [] ⟩, 34, [7, 1, 0] ⟩) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1] [("rows", 32)]) ⟨⟨34, [] ⟩, 34, [7, 1, 1] ⟩) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1] [("rows", 32)]) ⟨⟨34, [] ⟩, 34, [7, 1, 2] ⟩) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke (⟨ "zkl_d996c673878fadd82bc5da874ec28c7e0038e1489dbd5901f3eaef6a271fde3e", .math, [.index, .index], [.boolean] ⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.guard 1 "s3") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.sequenceLength (.table (.field "koala-bear.ext8-binomial3") none) 3) ⟨⟨34, [] ⟩, 34, [7, 1, 5] ⟩) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil)) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.guard 1 "s8") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.sequenceLength (.table (.field "koala-bear.ext8-binomial3") none) 3) ⟨⟨34, [] ⟩, 34, [7, 1, 8] ⟩) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "s13") .nil .nil <|
  .letOp (.guard 1 "s13") (.cons .here .nil) .nil <|
  .letOp (.mark "s15") .nil .nil <|
  .letOp (.localCall (⟨ "s3h7a6b6310h7072696d6974697665737h696e64696365736h6c656e677468", .local, [.indices], [.index] ⟩ : Helper) rfl 1 "s15") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "s18") .nil .nil <|
  .letOp (.guard 1 "s18") (.cons .here .nil) .nil <|
  .letOp (.mark "s20") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_efc5ece4a9b8074e3e7d2a732607ad124d6dff15f36a8e9dc596d88df0573550", .local, [(.vector "koala-bear.ext8-binomial3")], [.index] ⟩ : Helper) rfl 1 "s20") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s23") .nil .nil <|
  .letOp (.guard 1 "s23") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke (⟨ "zkl_c6bd4a70513c0e60a81af5917db503ec406ca6b7bc6e2fdcce6b66384a2bcc40", .math, [(.field "koala-bear.ext8-binomial3"), .index], [.index] ⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 32) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s28") .nil .nil <|
  .letOp (.guard 1 "s28") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.shape (.table (.field "koala-bear.ext8-binomial3") none) "rows") ⟨⟨34, [] ⟩, 34, [7, 1, 22] ⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke (⟨ "zkl_c6bd4a70513c0e60a81af5917db503ec406ca6b7bc6e2fdcce6b66384a2bcc40", .math, [(.field "koala-bear.ext8-binomial3"), .index], [.index] ⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s34") .nil .nil <|
  .letOp (.guard 1 "s34") (.cons .here .nil) .nil <|
  .letOp (.mark "s36") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_59770f895f4a65e43d6bfdf2cbc5814fe95b7e42f1c760b4bf05d976566f4545", .local, [.boolean, (.vector "koala-bear.ext8-binomial3"), .index], [.boolean] ⟩ : Helper) rfl 1 "s36") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))) .nil))) .nil <|
  .letOp (.mark "s37") .nil .nil <|
  .letOp (.guard 1 "s37") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexWrappingSubtract rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s42") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_a020b68fa3c7229c3a465edef5f5e01391f88527db4b82d2b62005f9ced9ff86", .local, [], [(.vector "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 1 "s42") .nil .nil <|
  .letOp (.mark "s54") .nil .nil <|
  .letOp (.repeat (⟨ [(.vector "koala-bear.ext8-binomial3")], [(.oracle (.table (.field "koala-bear.ext8-binomial3") none)), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.field "koala-bear.ext8-binomial3"), .index, (.vector "koala-bear.ext8-binomial3"), .indices, .boolean, (.vector "koala-bear.ext8-binomial3"), .index], [0, 1], [[1]], 8⟩ : RepeatSpec) "s54") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))))) (.cons (.there .here) .nil)))))))))))) (.cons (.letOp (.mark "s56") .nil .nil (.letOp (.localCall (⟨ "s3h7a6b6310h7072696d6974697665737h696e64696365733h676574", .local, [.indices, .index], [.index] ⟩ : Helper) rfl 1 "s56") (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons .here .nil)) .nil (.letOp (.mark "s59") .nil .nil (.letOp (.oracle (.query (.table (.field "koala-bear.ext8-binomial3") none) (some 1)) ⟨⟨34, [] ⟩, 34, [7, 1, 31, 4, 0, 3, 1, 1] ⟩) (.cons (.there (.there (.there .here))) (.cons .here .nil)) .nil (.letOp (.mark "s61") .nil .nil (.letOp (.localCall (⟨ "zkl_a4de6c653f3dd98800c1f0f224fb298886bf002c3b67044fb5d4d3400ec6d6d4", .local, [.boolean, (.vector "koala-bear.ext8-binomial3"), .index, (.field "koala-bear.ext8-binomial3")], [.boolean] ⟩ : Helper) rfl 1 "s61") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there .here)) (.cons .here .nil)))) .nil (.letOp (.mark "s62") .nil .nil (.letOp (.guard 1 "s62") (.cons .here .nil) .nil (.letOp (.mark "s63") .nil .nil (.letOp (.localCall (⟨ "zkl_daa4cc1b0228f87a89c04d62b4b161ffd93cfdc07ffcd4c34bb70b214836fc85", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.vector "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 1 "s63") (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.invoke (⟨ "zkl_c6bd4a70513c0e60a81af5917db503ec406ca6b7bc6e2fdcce6b66384a2bcc40", .math, [(.field "koala-bear.ext8-binomial3"), .index], [.index] ⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict .index [1]) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.invoke (⟨ "zkl_262408e7c1d541225e833ebfbee1716171d6581b8912fbf3dd09c1587c9cb24d", .math, [(.field "koala-bear.ext8-binomial3"), .index], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "koala-bear.ext8-binomial3") [1]) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.invoke (⟨ "s3h6672698h706169725f6c6f77", .math, [.index, .index], [.index] ⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there .here)) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.indexConstant 0) rfl) .nil .nil (.letOp (.mark "s78") .nil .nil (.letOp (.oracle (.sequenceAt (.table (.field "koala-bear.ext8-binomial3") none) 3 [0, 1]) ⟨⟨34, [] ⟩, 34, [7, 1, 31, 4, 0, 3, 1, 11] ⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.oracle (.shape (.table (.field "koala-bear.ext8-binomial3") none) "rows") ⟨⟨34, [] ⟩, 34, [7, 1, 31, 4, 0, 3, 1, 12] ⟩) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.indexConstant 1) rfl) .nil .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate .indexLogicalShiftRight rfl) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate .indexEqual rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.letOp (.mark "s84") .nil .nil (.letOp (.guard 1 "s84") (.cons .here .nil) .nil (.letOp (.mark "s85") .nil .nil (.letOp (.oracle (.query (.table (.field "koala-bear.ext8-binomial3") none) (some 1)) ⟨⟨34, [] ⟩, 34, [7, 1, 31, 4, 0, 3, 1, 17] ⟩) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.indexConstant 1) rfl) .nil .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate .indexLogicalShiftRight rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "koala-bear.ext8-binomial3") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)) .nil (.letOp (.mark "s96") .nil .nil (.letOp (.repeat (⟨ [(.field "koala-bear.ext8-binomial3"), .index, .index, (.field "koala-bear.ext8-binomial3")], [(.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3)], [0, 1], [[1], [1], [1], [1]], 3⟩ : RepeatSpec) "s96") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))) .nil))))))) (.cons (.letOp (.mark "") .nil .nil (.letOp (.calculate (.indexConstant 1) rfl) .nil .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate .indexWrappingAdd rfl) (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.mark "s101") .nil .nil (.letOp (.oracle (.sequenceAt (.table (.field "koala-bear.ext8-binomial3") none) 3 [0, 1]) ⟨⟨34, [] ⟩, 34, [7, 1, 31, 4, 0, 3, 1, 21, 4, 0, 3, 1, 2] ⟩) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.oracle (.shape (.table (.field "koala-bear.ext8-binomial3") none) "rows") ⟨⟨34, [] ⟩, 34, [7, 1, 31, 4, 0, 3, 1, 21, 4, 0, 3, 1, 3] ⟩) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate .indexEqual rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil (.letOp (.mark "s105") .nil .nil (.letOp (.guard 1 "s105") (.cons .here .nil) .nil (.letOp (.mark "s106") .nil .nil (.letOp (.oracle (.query (.table (.field "koala-bear.ext8-binomial3") none) (some 1)) ⟨⟨34, [] ⟩, 34, [7, 1, 31, 4, 0, 3, 1, 21, 4, 0, 3, 1, 6] ⟩) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldEqual "koala-bear.ext8-binomial3") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil (.letOp (.mark "s109") .nil .nil (.letOp (.guard 1 "s109") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.invoke (⟨ "s3h6672698h706169725f6c6f77", .math, [.index, .index], [.index] ⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)) .nil (.letOp (.mark "s113") .nil .nil (.letOp (.oracle (.sequenceAt (.table (.field "koala-bear.ext8-binomial3") none) 3 [0, 1]) ⟨⟨34, [] ⟩, 34, [7, 1, 31, 4, 0, 3, 1, 21, 4, 0, 3, 1, 10] ⟩) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.oracle (.shape (.table (.field "koala-bear.ext8-binomial3") none) "rows") ⟨⟨34, [] ⟩, 34, [7, 1, 31, 4, 0, 3, 1, 21, 4, 0, 3, 1, 11] ⟩) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.indexConstant 1) rfl) .nil .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate .indexLogicalShiftRight rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate .indexEqual rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.letOp (.mark "s119") .nil .nil (.letOp (.guard 1 "s119") (.cons .here .nil) .nil (.letOp (.mark "s120") .nil .nil (.letOp (.oracle (.query (.table (.field "koala-bear.ext8-binomial3") none) (some 1)) ⟨⟨34, [] ⟩, 34, [7, 1, 31, 4, 0, 3, 1, 21, 4, 0, 3, 1, 16] ⟩) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.indexConstant 1) rfl) .nil .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate .indexLogicalShiftRight rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "koala-bear.ext8-binomial3") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) .nil)) .nil (.ret (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there .here) (.cons .here .nil))))))))))))))))))))))))))))))))))))))))))))) .nil) (.letOp (.mark "s132") .nil .nil (.letOp (.localCall (⟨ "zkl_a2cb18beedc26c3b2940b6a483d3dac2dfdfc2ee3b57a534fa8a67065bc2fc54", .local, [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index, .index], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 1 "s132") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) (.cons (.there .here) .nil)))) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldEqual "koala-bear.ext8-binomial3") rfl) (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "s135") .nil .nil (.letOp (.guard 1 "s135") (.cons .here .nil) .nil (.ret (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) .nil)))))))))))))))))))))))))))))))))))))))))))))))))))) .nil) <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanConstant true) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict .boolean [1]) (.cons .here .nil) .nil <|
  .ret (.cons .here (.cons (.there (.there .here)) .nil))

def protocol4Signature : ProtocolSignature where
  name := "zkl_ffec0327b57535f490a7399445686fa21555651e621d47ab96236ca36f1dc4dd"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "koala-bear.ext8-binomial3"), (.oracle (.table (.field "koala-bear.ext8-binomial3") none)), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.field "koala-bear.ext8-binomial3"), .index, (.vector "koala-bear.ext8-binomial3"), .indices, .index, .index]
  outputs := [.boolean, (.vector "koala-bear.ext8-binomial3")]
  inputScopes := [[0], [1], [0], [1], [0], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]]
  outputScopes := [[1], [1]]

def protocol4Body : Region protocolDialect protocol4Signature.inputs protocol4Signature.outputs :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.singleton (.table (.field "koala-bear.ext8-binomial3") none)) 0 [1] [("rows", 32)]) ⟨⟨32, [] ⟩, 32, [7, 1, 0] ⟩) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1] [("rows", 32)]) ⟨⟨32, [] ⟩, 32, [7, 1, 1] ⟩) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1] [("rows", 32)]) ⟨⟨32, [] ⟩, 32, [7, 1, 2] ⟩) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall (⟨ "zkl_a020b68fa3c7229c3a465edef5f5e01391f88527db4b82d2b62005f9ced9ff86", .local, [], [(.vector "koala-bear.ext8-binomial3")] ⟩ : Helper) rfl 1 "s0") .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanConstant false) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.singleton (.table (.field "koala-bear.ext8-binomial3") none)) 0 [1]) ⟨⟨32, [] ⟩, 32, [7, 1, 5] ⟩) (.cons (.there (.there (.there (.there .here)))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1]) ⟨⟨32, [] ⟩, 32, [7, 1, 6] ⟩) (.cons (.there (.there (.there (.there (.there .here))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1]) ⟨⟨32, [] ⟩, 32, [7, 1, 7] ⟩) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.protocolApply (⟨ "zkl_f7f6685fe66aaf3cf40ed2536ccbcf40f97f242773e81303113589b9da931aa0", ["role00000000", "role00000001"], [(.vector "koala-bear.ext8-binomial3"), (.oracle (.table (.field "koala-bear.ext8-binomial3") none)), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.field "koala-bear.ext8-binomial3"), .index, (.vector "koala-bear.ext8-binomial3"), .indices, .index, .index, .boolean, (.vector "koala-bear.ext8-binomial3")], [.boolean, (.vector "koala-bear.ext8-binomial3")], [[0], [1], [0], [1], [0], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [1], [1]], [[1], [1]] ⟩ : ProtocolSignature) [0, 1] "s3") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))))))))))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

def protocol5Signature : ProtocolSignature where
  name := "zkl_5be81258fbd44da038012fc7680dce446a9d3c1f187a820b4a63d44cd345c871"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index, .index, (.service "random.koala-bear.ext8-binomial3/0")]
  outputs := [.boolean, .indices, .indices, (.vector "koala-bear.ext8-binomial3")]
  inputScopes := [[0], [0], [1], [0, 1], [0, 1], [1]]
  outputScopes := [[1], [0], [1], [1]]

def protocol5Body : Region protocolDialect protocol5Signature.inputs protocol5Signature.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.protocolApply (⟨ "zkl_027a2c514d3bdf8305ddf3314b67ffc4a92fb3fe0b021880127a83013a686404", ["role00000000", "role00000001"], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index, (.service "random.koala-bear.ext8-binomial3/0")], [(.vector "koala-bear.ext8-binomial3"), (.oracle (.table (.field "koala-bear.ext8-binomial3") none)), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.field "koala-bear.ext8-binomial3"), .index, (.vector "koala-bear.ext8-binomial3"), .index], [[0], [0], [1], [0, 1], [1]], [[0], [1], [0], [1], [0], [1], [0, 1], [0, 1], [0, 1], [0, 1]] ⟩ : ProtocolSignature) [0, 1] "s0") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.singleton (.table (.field "koala-bear.ext8-binomial3") none)) 0 [1] [("rows", 32)]) ⟨⟨1, [] ⟩, 1, [7, 1, 1] ⟩) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1] [("rows", 32)]) ⟨⟨1, [] ⟩, 1, [7, 1, 2] ⟩) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1] [("rows", 32)]) ⟨⟨1, [] ⟩, 1, [7, 1, 3] ⟩) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "label_71756572696573") .nil .nil <|
  .letOp (.protocolApply (⟨ "zkl_5bdb55a745abe137c9027bb7f7baa1d02e1dde834266d27198609cdbce18f830", ["role00000000", "role00000001"], [.index, (.service "random.koala-bear.ext8-binomial3/0")], [.indices], [[0, 1], [1]], [[0, 1]] ⟩ : ProtocolSignature) [0, 1] "label_71756572696573") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.singleton (.table (.field "koala-bear.ext8-binomial3") none)) 0 [1]) ⟨⟨1, [] ⟩, 1, [7, 1, 5] ⟩) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1]) ⟨⟨1, [] ⟩, 1, [7, 1, 6] ⟩) (.cons (.there (.there (.there (.there .here)))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1]) ⟨⟨1, [] ⟩, 1, [7, 1, 7] ⟩) (.cons (.there (.there (.there (.there (.there .here))))) .nil) .nil <|
  .letOp (.mark "s4") .nil .nil <|
  .letOp (.protocolApply (⟨ "zkl_fe1dbc0863e9ce6597f78199145977ba10bcf6691b6ad36d1041feedc52b31f6", ["role00000000", "role00000001"], [(.vector "koala-bear.ext8-binomial3"), (.oracle (.table (.field "koala-bear.ext8-binomial3") none)), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.field "koala-bear.ext8-binomial3"), .index, (.vector "koala-bear.ext8-binomial3"), .index, .indices], [(.vector "koala-bear.ext8-binomial3"), (.oracle (.table (.field "koala-bear.ext8-binomial3") none)), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.field "koala-bear.ext8-binomial3"), .index, (.vector "koala-bear.ext8-binomial3"), .indices, .index, .index], [[0], [1], [0], [1], [0], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]], [[0], [1], [0], [1], [0], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]] ⟩ : ProtocolSignature) [0, 1] "s4") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))))))))))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.singleton (.table (.field "koala-bear.ext8-binomial3") none)) 0 [1] [("rows", 32)]) ⟨⟨1, [] ⟩, 1, [7, 1, 9] ⟩) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1] [("rows", 32)]) ⟨⟨1, [] ⟩, 1, [7, 1, 10] ⟩) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.input (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1] [("rows", 32)]) ⟨⟨1, [] ⟩, 1, [7, 1, 11] ⟩) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.singleton (.table (.field "koala-bear.ext8-binomial3") none)) 0 [1]) ⟨⟨1, [] ⟩, 1, [7, 1, 12] ⟩) (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1]) ⟨⟨1, [] ⟩, 1, [7, 1, 13] ⟩) (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.oracle (.components (.sequence (.table (.field "koala-bear.ext8-binomial3") none) 3) 0 [1]) ⟨⟨1, [] ⟩, 1, [7, 1, 14] ⟩) (.cons (.there (.there (.there (.there .here)))) .nil) .nil <|
  .letOp (.mark "s6") .nil .nil <|
  .letOp (.protocolApply (⟨ "zkl_ffec0327b57535f490a7399445686fa21555651e621d47ab96236ca36f1dc4dd", ["role00000000", "role00000001"], [(.vector "koala-bear.ext8-binomial3"), (.oracle (.table (.field "koala-bear.ext8-binomial3") none)), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.sequence (.vector "koala-bear.ext8-binomial3")), (.oracleSequence (.table (.field "koala-bear.ext8-binomial3") none) 3), (.field "koala-bear.ext8-binomial3"), .index, (.vector "koala-bear.ext8-binomial3"), .indices, .index, .index], [.boolean, (.vector "koala-bear.ext8-binomial3")], [[0], [1], [0], [1], [0], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]], [[1], [1]] ⟩ : ProtocolSignature) [0, 1] "s6") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) .nil)))))))))))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict .indices [0]) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict .indices [1]) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))) .nil) .nil <|
  .ret (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there .here))) .nil))))

def runSignature : ProtocolSignature where
  name := "s7h6578616d706c653h467269"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index, .index, (.service "random.koala-bear.ext8-binomial3/0")]
  outputs := [.boolean]
  inputScopes := [[0], [0, 1], [0, 1], [0, 1], [1]]
  outputScopes := [[1]]

def runBody : Region protocolDialect runSignature.inputs runSignature.outputs :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.protocolApply (⟨ "zkl_5be81258fbd44da038012fc7680dce446a9d3c1f187a820b4a63d44cd345c871", ["role00000000", "role00000001"], [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index, .index, (.service "random.koala-bear.ext8-binomial3/0")], [.boolean, .indices, .indices, (.vector "koala-bear.ext8-binomial3")], [[0], [0], [1], [0, 1], [0, 1], [1]], [[1], [0], [1], [1]] ⟩ : ProtocolSignature) [0, 1] "s0") (.cons .here (.cons (.there .here) (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)))))) .nil <|
  .ret (.cons .here .nil)

def oracle0Signature : OracleSignature :=
  ⟨"zkl_31951b707ccfb62c7ac7e26ab2036ae9b332cef26f2c1a9300411ee5fea235f4", [(.oracle (.table (.field "koala-bear.ext8-binomial3") none)), (.field "koala-bear.ext8-binomial3"), .index, .index, (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index], (.table (.field "koala-bear.ext8-binomial3") none), "zkl_49518c8ca28853d5308e4676cd87321c967360523046281374cc9e81874fbdd3", [("rows", 3)], [("rows", 32)]⟩

def oracle0Body : Region protocolDialect oracle0Signature.inputs [oracle0Signature.kind.answer] :=
  .letOp (.calculate (.invoke (⟨ "s3h6672698h706169725f6c6f77", .math, [.index, .index], [.index] ⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.calculate .indexLogicalShiftRight rfl) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .letOp (.calculate .indexWrappingAdd rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.oracle (.query (.table (.field "koala-bear.ext8-binomial3") none) none) ⟨⟨16, [] ⟩, 16, [7, 1, 4] ⟩) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.oracle (.query (.table (.field "koala-bear.ext8-binomial3") none) none) ⟨⟨16, [] ⟩, 16, [7, 1, 5] ⟩) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there .here) .nil)) .nil <|
  .letOp (.calculate (.invoke (⟨ "zkl_7687774cc1014f46884b89c91fc63d3def7566efa921884515ed50af7c46dfca", .math, [(.field "koala-bear.ext8-binomial3"), .index], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .letOp (.calculate (.fieldMultiply "koala-bear.ext8-binomial3") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.calculate (.invoke (⟨ "zkl_1d5c68c5e36ee11e4cbcec8bd6616e4424fe384afe270d5217a19883323f5700", .math, [(.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3")], [(.field "koala-bear.ext8-binomial3")] ⟩ : Helper)) rfl) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) (.cons .here .nil))))) .nil <|
  .ret (.cons .here .nil)

end ZkcExamples.Structured.FriSourceBodies
