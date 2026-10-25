module

public import Zkc.Executable.Program

@[expose] public section

/-! Validator data from the retained `zkc.program/0` candidate of the native
deployment. Regenerate with bridges/executable/check.py --write; the Lean rule
and its proofs are separate. The bridge checks exact regeneration against the
compiler. -/

namespace ZkcExamples.Executable.SumcheckProofProgramData
open Zkc.Construction Zkc.Executable

/-- SHA-256 of the exact `zkc.program/0` bytes this data was read from. -/
def program : String := "sha256:16a63417a62f65de160d326542dd881df74e2b805ec73dee945f0e95dc0640d0"

/-- The local function `zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f`. -/
def function0 : Function :=
  ⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩], [
    .operation "s0" "zkl_binding_7" [] [] ["v74"],
    .ret ["v74"]]⟩

/-- The local function `zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d`. -/
def function1 : Function :=
  ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [("v105", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v106", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩], [
    .operation "s0" "zkl_binding_11" [] ["v105", "v106"] ["v107"],
    .ret ["v107"]]⟩

/-- The local function `zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc`. -/
def function2 : Function :=
  ⟨"zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", [("v108", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v109", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v110", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data .boolean, "native.bool/0"⟩], [
    .operation "lc_7_lc_2_s1" "zkl_binding_1" [] ["v109"] ["v111"],
    .operation "lc_7_lc_2_s2" "zkl_binding_0" [.text "1"] [] ["v112"],
    .operation "lc_70_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_2_s0" "zkl_binding_0" [.text "0"] [] ["v113"],
    .operation "lc_114_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_2_s1_35_s3h7a6b637h696e64696365734h6c657373_2_s0" "zkl_binding_5" [] ["v113", "v112"] ["v114"],
    .cond "lc_70_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_2_s3" "v114" ["v111"] [.operation "lc_70_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_2_s4" "zkl_binding_0" [.text "64"] [] ["v115"], .operation "lc_114_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_2_s5_35_s3h7a6b637h696e64696365734h6c657373_2_s0" "zkl_binding_5" [] ["v111", "v115"] ["v116"], .yield ["v116"]] [.constant "lc_70_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_2_s7" "v117" false, .yield ["v117"]] ["v118"],
    .cond "lc_71_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s11" "v118" ["v108", "v112"] [.operation "lc_71_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s12" "zkl_binding_1" [] ["v108"] ["v119"], .operation "lc_71_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s13" "zkl_binding_2" [] ["v119", "v112"] ["v120"], .operation "lc_71_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s14" "zkl_binding_0" [.text "0"] [] ["v121"], .operation "lc_71_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s15" "zkl_binding_3" [] ["v120", "v121"] ["v122"], .yield ["v122"]] [.constant "lc_71_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s17" "v123" false, .yield ["v123"]] ["v124"],
    .cond "lc_71_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s22" "v124" ["v108", "v111", "v112"] [.operation "lc_71_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s23" "zkl_binding_1" [] ["v108"] ["v125"], .operation "lc_71_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s24" "zkl_binding_4" [] ["v125", "v112"] ["v126"], .operation "lc_h_12c01db8f313ed943761ac0825838046ef00d84dcfc058d37638790cc3129f63" "zkl_binding_0" [.text "64"] [] ["v127"], .operation "lc_69_lc_h_4dc29171484fe119bcb93517e77d9153355950c493d148d41fd9d9a365c69100" "zkl_binding_5" [] ["v111", "v127"] ["v128"], .cond "lc_h_ba024a064679a3fe66fecfab04dec1132110a3ba8fddb077813a152e1b668dca" "v128" [] [.yield []] [.stop "lc_69_lc_h_58e72c9acd76f03349acc9cf4c9d15a9441abdaa22fba3359347216ef9db5f0a" "reject"] [], .operation "lc_h_8dcefa9b40eae178651dda47a36ea831755cf841f98330d144debb1e3aad6d1d" "zkl_binding_0" [.text "1"] [] ["v129"], .operation "lc_h_df5032c8b3f220134d35e026578513ffad7e3c5084a7ffe3655d8ac28427f99c" "zkl_binding_0" [.text "0"] [] ["v130"], .iterate "lc_h_cc6d91652ca4ff7bf2ba0f19aa7f2760bcd0fb0a1a8c61744ca0d0530083347b" "v131" "v130" "v111" [("v132", "v129")] [] [.operation "lc_h_68e8fb9b46f6b7404759f774f058338e987717644b620b67ba5fd83ce52a8f0c" "zkl_binding_0" [.text "2"] [] ["v133"], .operation "lc_h_76ab93e2d1b1533accac225dc9e12f20d34da19e5814f1225ad143954fee9593" "zkl_binding_6" [] ["v132", "v133"] ["v134"], .yield ["v134"]] ["v135"], .operation "lc_71_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s26" "zkl_binding_3" [] ["v126", "v135"] ["v136"], .yield ["v136"]] [.constant "lc_71_lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s28" "v137" false, .yield ["v137"]] ["v138"],
    .cond "lc_7_lc_2_s6" "v138" ["v108", "v109", "v110"] [.operation "lc_60_lc_2_s7_44_s8h73756d636865636b11h636865636b5f7461626c65_2_s1" "zkl_binding_1" [] ["v109"] ["v139"], .operation "lc_60_lc_2_s7_44_s8h73756d636865636b11h636865636b5f7461626c65_2_s2" "zkl_binding_0" [.text "1"] [] ["v140"], .operation "lc_69_lc_h_725764acc0c65074a290eb5fb8937fbc15f1d2c572432a1dc25fff0111a10ea0" "zkl_binding_0" [.text "0"] [] ["v141"], .operation "lc_69_lc_h_b60025e678c8d6a1b6c7530d08db66794f015c953a01d619baa0cf95ef4b4e9e" "zkl_binding_5" [] ["v141", "v140"] ["v142"], .cond "lc_69_lc_h_d22d27aaf8ba9abc236f0ae4ed7a62e5247b1960d453f16b7ffdad9e0e4d6c34" "v142" ["v139"] [.operation "lc_69_lc_h_3129d68b797a42b649b723e9d531c8d67aeda51d8d82d0f989506b3be415ba97" "zkl_binding_0" [.text "64"] [] ["v143"], .operation "lc_69_lc_h_481eceb6c9b5386a8e136527d9018f0dcd3d386f42e7cfb37aa004553ebab5f0" "zkl_binding_5" [] ["v139", "v143"] ["v144"], .yield ["v144"]] [.constant "lc_69_lc_h_3c58e279990c973f17902dc16f133c1dfb2e5a80d01c07c34d0bdb11b22fc5cc" "v145" false, .yield ["v145"]] ["v146"], .cond "lc_69_lc_h_d2378f087638edb3c24471d22ef2790a253bc31af674891c9785d82f0ab9117e" "v146" ["v108", "v140"] [.operation "lc_69_lc_h_1b855b7fd960b9b70670ae6ed68a8a2726bb0ff402179935457b4e65634a229d" "zkl_binding_1" [] ["v108"] ["v147"], .operation "lc_69_lc_h_b971262b7091c2f3f8d6a0cb80e9f2e109f3493c52be0916de61158af276692d" "zkl_binding_2" [] ["v147", "v140"] ["v148"], .operation "lc_69_lc_h_094abd3d210bde771584972e180305fa14fa715b6083707b3e92938723e8ec98" "zkl_binding_0" [.text "0"] [] ["v149"], .operation "lc_69_lc_h_fa9773a3edcab33a42563b8007fbcb4e323710ade2e3b040d842cd2147eb8870" "zkl_binding_3" [] ["v148", "v149"] ["v150"], .yield ["v150"]] [.constant "lc_69_lc_h_288827d96280fddd25be6fcaadda72d8dc32724235b8c09b2f8b11ce0ce16f8d" "v151" false, .yield ["v151"]] ["v152"], .cond "lc_69_lc_h_e8609657f0fa9d39be08f303a386cd15899cf418c641c907fa591455517b3e8d" "v152" ["v108", "v139", "v140"] [.operation "lc_69_lc_h_a0ba19b9aeeb198cf2f42aa508f85b2e40937802fb07149fdfd402112466de72" "zkl_binding_1" [] ["v108"] ["v153"], .operation "lc_69_lc_h_9f90d3103e63ecc5b4fc2e1ccead106a7734e356b493b94b2f1f4e1e9bad45b4" "zkl_binding_4" [] ["v153", "v140"] ["v154"], .operation "lc_69_lc_h_88f4b315df9c56be6cb17f0ab000c4fbc63699dfe75fd735eac7ae878c2a6bb5" "zkl_binding_0" [.text "64"] [] ["v155"], .operation "lc_69_lc_h_e829052ee4069fe4a17e4abf61016a16fc71347704d60f4300c5b9d8dc324254" "zkl_binding_5" [] ["v139", "v155"] ["v156"], .cond "lc_69_lc_h_97b568a82f1ddfbea0ec8e0024bff8dacfddcc9110914b8e62c5dd9b41565ebe" "v156" [] [.yield []] [.stop "lc_69_lc_h_6bcbbe63e6f23bab69f210d14f59bfbf391ff19fdf6c3d6e0335883f97a12ea6" "reject"] [], .operation "lc_69_lc_h_d661c0236de91afc99a19161d479fcfa6149f3b76082d610691ed5da79b470b5" "zkl_binding_0" [.text "1"] [] ["v157"], .operation "lc_69_lc_h_c3ba063e21c30f213092dcbedaeb98ed295d0c4d6b50a6bcc14af5ad59b29aaa" "zkl_binding_0" [.text "0"] [] ["v158"], .iterate "lc_69_lc_h_3df4d169d0ca65016a66b2a5d82cf6155e0c0b3715c90faf31f5a69355f24b2f" "v159" "v158" "v139" [("v160", "v157")] [] [.operation "lc_69_lc_h_906a82e412d1c7c25d1caec21d0c1325b2328d4cf2ca245d7ef33ed6bc34d4af" "zkl_binding_0" [.text "2"] [] ["v161"], .operation "lc_69_lc_h_f1dba30b151924c507693ee879cec5394cda04846b7026cd538ff7657ebf6510" "zkl_binding_6" [] ["v160", "v161"] ["v162"], .yield ["v162"]] ["v163"], .operation "lc_69_lc_h_6bd04eb984e50d34c372ad80bd3ec94cdced49cbf9105b98cb2f50684aa9e328" "zkl_binding_3" [] ["v154", "v163"] ["v164"], .yield ["v164"]] [.constant "lc_69_lc_h_0ef31258126ccdbb788e4f3d952407710687ce3ba44549c69ec4cf502fc48bab" "v165" false, .yield ["v165"]] ["v166"], .cond "lc_115_lc_2_s7_44_s8h73756d636865636b11h636865636b5f7461626c65_2_s3_46_s3h7a6b6311h6d756c74696c696e6561725h7461626c65_2_s1" "v166" [] [.yield []] [.stop "lc_h_29e05a7ad16fcc60243f446083e66d7c36ebfd8bcacd02b18947f631b9ec7f7e" "reject"] [], .operation "lc_69_lc_h_21ac35ce962ffcdb820a0d23254b12be23fe91448d8e2dcafb0af590cee88ca5" "_finite_binding_0" [] ["v109"] ["v167"], .operation "lc_69_lc_h_41d726ae4cc1bd21657c0c281c3ee4c40b907fc3f7798f1638938f4c47a391c2" "_finite_binding_1" [.text "0"] [] ["v168"], .iterate "lc_69_lc_h_c3c605656583ef6d82548d356fbafaf736b806710d67f99cad4edde486e6e192" "v169" "v168" "v167" [("v170", "v108"), ("v171", "v139"), ("v172", "v140")] ["v109", "v167"] [.operation "lc_69_lc_h_3adb11b87c24f5ee7609f78e2b6296ec233b0869a34c58215a4fe23d60a24094" "_finite_binding_2" [] ["v109", "v169"] ["v173"], .operation "lc_69_lc_h_f7e8625e30d3e362263409688953e828d0eab871e73eee92588a71b9b566dd70" "zkl_binding_0" [.text "0"] [] ["v174"], .operation "lc_69_lc_h_82910649653b3478917c5d65c1542eb2c007aee49a9a8e709b53716df6472125" "zkl_binding_5" [] ["v174", "v171"] ["v175"], .cond "lc_69_lc_h_dc59353d160052667e217a02186d99a31eb3721f919e9ac4e2dc0bc83dc7f4d1" "v175" [] [.yield []] [.stop "lc_69_lc_h_1d4abf66d7b3d78a7daf513c4cce8d7d01ea5a1aa3fcd9c859b09403c354683c" "reject"] [], .operation "lc_69_lc_h_a146c6c5cdc9162cce3bfe8046431184898edc21d4ec4e272327faf0fe648ec4" "zkl_binding_9" [] ["v170"] ["v176", "v177"], .operation "lc_h_ef2d6f22d524dc85bb4ba47ce1a8ae59c00ac28113c631b95b562918b89e9993" "_map_binding_0" [] ["v176"] ["v178"], .operation "lc_h_59fd71c474e4676f4c50f519fa41a39441030cbfe9aeb3a2763d33f3e957bfab" "_map_binding_0" [] ["v177"] ["v179"], .operation "lc_h_07f368a9768ca79ddb5a006a6f36d289cde8a68f862322cfbb177758fbfa00c7" "_map_binding_1" [] ["v178", "v179"] ["v180"], .operation "lc_h_d6ecf1e05e4cb30870b1a25dc08cba9ed1ba510b5edef9dfb73db027f241f4be" "_map_binding_2" [] ["v180"] [], .operation "lc_h_fe950e294369e76a67bffb0cf24043063d36756f9376ca1b5e4d8ddcd9178b6b" "_map_binding_3" [.text "[\"zkc.ring/0\",[\"bls12-381.fr\",\"bls12-381.fr\",\"bls12-381.fr\"],[[\"input\",0],[\"input\",1],[\"input\",2],[\"neg\",0],[\"add\",1,3],[\"mul\",4,2],[\"add\",0,5]],[6]]"] ["v178", "v176", "v177", "v173"] ["v181"], .operation "lc_69_lc_h_061bb4095386582ab31a2235903ee3b4765d0e151c4c0a0d84ae0519c747a5ac" "zkl_binding_0" [.text "1"] [] ["v182"], .operation "lc_69_lc_h_cd41c3e3414dd29c415f831c7441c0dc504fb92b77eb36d2810df8df7c201e74" "zkl_binding_10" [] ["v171", "v182"] ["v183"], .yield ["v181", "v183", "v172"]] ["v184", "v185", "v186"], .operation "lc_60_lc_2_s7_44_s8h73756d636865636b11h636865636b5f7461626c65_2_s9" "zkl_binding_8" [] ["v184"] ["v187"], .operation "lc_61_lc_2_s7_44_s8h73756d636865636b11h636865636b5f7461626c65_3_s11" "zkl_binding_12" [] ["v187", "v110"] ["v188"], .yield ["v188"]] [.constant "lc_7_lc_2_s9" "v189" false, .yield ["v189"]] ["v190"],
    .ret ["v190"]]⟩

/-- The local function `_calculation_3`. -/
def function3 : Function :=
  ⟨"_calculation_3", [("v387", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v388", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v389", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [], [
    .operation "lc_6_kernel_6_kernel_1_0" "_kernel_binding_6" [] ["v387", "v388"] ["v390"],
    .operation "lc_6_kernel_6_kernel_1_1" "_kernel_binding_5" [] ["v389", "v390"] ["v391"],
    .cond "guard_control" "v391" [] [.yield []] [.stop "apply_18_label_726564756365_s24" "reject"] [],
    .ret []]⟩

/-- The local function `_calculation_4`. -/
def function4 : Function :=
  ⟨"_calculation_4", [("v392", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v393", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v394", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩], [
    .operation "lc_6_kernel_6_kernel_1_0" "_kernel_binding_9" [.text "1"] [] ["v395"],
    .operation "lc_6_kernel_6_kernel_1_1" "_kernel_binding_8" [] ["v395", "v392"] ["v396"],
    .operation "lc_6_kernel_6_kernel_1_2" "_kernel_binding_7" [] ["v396", "v393"] ["v397"],
    .operation "lc_6_kernel_6_kernel_1_3" "_kernel_binding_7" [] ["v392", "v394"] ["v398"],
    .operation "lc_6_kernel_6_kernel_1_4" "_kernel_binding_6" [] ["v397", "v398"] ["v399"],
    .ret ["v399"]]⟩

/-- The local function `_transcript_1`. -/
def function5 : Function :=
  ⟨"_transcript_1", [("v422", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v423", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v424", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v425"],
    .operation "coordinate_0" "_transcript_3" [] ["v425", "v424"] ["v426"],
    .operation "transition" "_transcript_0" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩] ["v422", "v423", "v426"] ["v427"],
    .ret ["v427"]]⟩

/-- The local function `_transcript_4`. -/
def function6 : Function :=
  ⟨"_transcript_4", [("v428", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v429", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v430", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v431"],
    .operation "coordinate_0" "_transcript_3" [] ["v431", "v430"] ["v432"],
    .operation "transition" "_transcript_0" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩] ["v428", "v429", "v432"] ["v433"],
    .ret ["v433"]]⟩

/-- The local function `_transcript_6`. -/
def function7 : Function :=
  ⟨"_transcript_6", [("v434", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v435", ⟨.data .index, "native.index/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v436"],
    .operation "coordinate_0" "_transcript_3" [] ["v436", "v435"] ["v437"],
    .operation "transition" "_transcript_5" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["query", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_6368616c6c656e6765", "input_5", "random.bls12-381.fr/0", "draw", "role00000001"]⟩] ["v434", "v437"] ["v438", "v439"],
    .ret ["v438", "v439"]]⟩

/-- The local function `_transcript_7`. -/
def function8 : Function :=
  ⟨"_transcript_7", [("v440", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v441", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v442", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v443"],
    .operation "coordinate_0" "_transcript_3" [] ["v443", "v442"] ["v444"],
    .operation "transition" "_transcript_0" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩] ["v440", "v441", "v444"] ["v445"],
    .ret ["v445"]]⟩

def validator : Validator where
  entry := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071"
  role := "role00000001"
  symbol := "_math_1"
  inputs := [("v400", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v401", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v402", ⟨.data .index, "native.index/0"⟩), ("v403", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)]
  results := [⟨.data .boolean, "native.bool/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩]
  body := [
    .call "apply_18_label_726564756365_s12" "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f" [] ["v404"],
    .loop "apply_18_label_726564756365_s15" "v402" 2 "v405" [("v406", "v404"), ("v407", "v401"), ("v408", "v403")] [] [.receive "apply_18_label_726564756365_label_726f756e64_0" "apply_18_label_726564756365_label_726f756e64_0" "role00000000" "v409" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, .call "_transcript_12" "_transcript_1" ["v408", "v409", "v405"] ["v410"], .receive "apply_18_label_726564756365_label_726f756e64_1" "apply_18_label_726564756365_label_726f756e64_1" "role00000000" "v411" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, .call "_transcript_13" "_transcript_4" ["v410", "v411", "v405"] ["v412"], .call "apply_18_label_726564756365_s24" "_calculation_3" ["v409", "v411", "v407"] [], .call "_transcript_14" "_transcript_6" ["v412", "v405"] ["v413", "v414"], .call "_transcript_15" "_transcript_7" ["v414", "v413", "v405"] ["v415"], .call "apply_18_label_726564756365_s33" "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d" ["v406", "v413"] ["v416"], .call "calculation_0" "_calculation_4" ["v413", "v409", "v411"] ["v417"], .yield ["v416", "v417", "v415"]] ["v418", "v419", "v420"],
    .call "s7" "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc" ["v400", "v418", "v419"] ["v421"],
    .ret ["v421", "v420"]]
  functions := [function0, function1, function2, function3, function4, function5, function6, function7, function8]
  bindings := [
    ⟨"_map_binding_3", "numerical.map", ["bls12-381.fr", "110"], "arkworks/numerical.map", []⟩,
    ⟨"_map_binding_2", "control.require", [], "arkworks/control.require", []⟩,
    ⟨"_map_binding_1", "index.equal", [], "native/index.equal", []⟩,
    ⟨"_map_binding_0", "vector.length", ["bls12-381.fr"], "arkworks/vector.length", []⟩,
    ⟨"_kernel_binding_7", "field.mul", ["bls12-381.fr"], "arkworks/field.mul", []⟩,
    ⟨"_kernel_binding_8", "field.sub", ["bls12-381.fr"], "arkworks/field.sub", []⟩,
    ⟨"_kernel_binding_9", "field.constant", ["bls12-381.fr"], "arkworks/field.constant", []⟩,
    ⟨"_kernel_binding_5", "field.equal", ["bls12-381.fr"], "arkworks/field.equal", []⟩,
    ⟨"_kernel_binding_6", "field.add", ["bls12-381.fr"], "arkworks/field.add", []⟩,
    ⟨"_transcript_5", "transcript.native.indexed.challenge", ["merlin3.bls12-381.fr64be/0"], "arkworks/transcript.native.indexed.challenge", []⟩,
    ⟨"_transcript_3", "indices.append", [], "native/indices.append", []⟩,
    ⟨"_transcript_2", "indices.empty", [], "native/indices.empty", []⟩,
    ⟨"_transcript_0", "transcript.native.indexed.observe.data", ["merlin3.bls12-381.fr64be/0", "field:bls12-381.fr"], "arkworks/transcript.native.indexed.observe.data", [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩]⟩,
    ⟨"_finite_binding_2", "vector.get", ["bls12-381.fr"], "arkworks/vector.get", []⟩,
    ⟨"_finite_binding_1", "index.constant", [], "native/index.constant", []⟩,
    ⟨"_finite_binding_0", "vector.length", ["bls12-381.fr"], "arkworks/vector.length", []⟩,
    ⟨"zkl_binding_12", "field.equal", ["bls12-381.fr"], "arkworks/field.equal", []⟩,
    ⟨"zkl_binding_11", "vector.append", ["bls12-381.fr"], "arkworks/vector.append", []⟩,
    ⟨"zkl_binding_10", "index.sub", [], "native/index.sub", []⟩,
    ⟨"zkl_binding_9", "vector.split", ["bls12-381.fr"], "arkworks/vector.split", []⟩,
    ⟨"zkl_binding_8", "vector.sum", ["bls12-381.fr"], "arkworks/vector.sum", []⟩,
    ⟨"zkl_binding_7", "vector.empty", ["bls12-381.fr"], "arkworks/vector.empty", []⟩,
    ⟨"zkl_binding_6", "index.mul", [], "native/index.mul", []⟩,
    ⟨"zkl_binding_5", "index.less", [], "native/index.less", []⟩,
    ⟨"zkl_binding_4", "index.div", [], "native/index.div", []⟩,
    ⟨"zkl_binding_3", "index.equal", [], "native/index.equal", []⟩,
    ⟨"zkl_binding_2", "index.mod", [], "native/index.mod", []⟩,
    ⟨"zkl_binding_1", "vector.length", ["bls12-381.fr"], "arkworks/vector.length", []⟩,
    ⟨"zkl_binding_0", "index.constant", [], "native/index.constant", []⟩]

end ZkcExamples.Executable.SumcheckProofProgramData
