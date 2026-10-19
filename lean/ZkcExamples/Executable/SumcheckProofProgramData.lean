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
def program : String := "sha256:13ebe5bb7e06e8f0cbf05cb8bfb6cf18aa285cd094d043b0d14b730e49485e3f"

/-- The local function `zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46`. -/
def function0 : Function :=
  ⟨"zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46", [], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩], [
    .operation "s0" "zkl_binding_7" [] [] ["v83"],
    .ret ["v83"]]⟩

/-- The local function `zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58`. -/
def function1 : Function :=
  ⟨"zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58", [("v116", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v117", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩], [
    .operation "s0" "zkl_binding_11" [] ["v116", "v117"] ["v118"],
    .ret ["v118"]]⟩

/-- The local function `zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc`. -/
def function2 : Function :=
  ⟨"zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", [("v119", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v120", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v121", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data .boolean, "native.bool/0"⟩], [
    .operation "lc_2_s1" "zkl_binding_1" [] ["v120"] ["v122"],
    .operation "lc_2_s2" "zkl_binding_0" [.text "1"] [] ["v123"],
    .operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_2_s0" "zkl_binding_0" [.text "0"] [] ["v124"],
    .operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_2_s1_35_s3h7a6b637h696e64696365734h6c657373_2_s0" "zkl_binding_5" [] ["v124", "v123"] ["v125"],
    .cond "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_2_s3" "v125" ["v122"] [.operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_2_s4" "zkl_binding_0" [.text "64"] [] ["v126"], .operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_2_s5_35_s3h7a6b637h696e64696365734h6c657373_2_s0" "zkl_binding_5" [] ["v122", "v126"] ["v127"], .yield ["v127"]] [.constant "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_2_s7" "v128" false, .yield ["v128"]] ["v129"],
    .cond "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s11" "v129" ["v119", "v123"] [.operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s12" "zkl_binding_1" [] ["v119"] ["v130"], .operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s13" "zkl_binding_2" [] ["v130", "v123"] ["v131"], .operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s14" "zkl_binding_0" [.text "0"] [] ["v132"], .operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s15" "zkl_binding_3" [] ["v131", "v132"] ["v133"], .yield ["v133"]] [.constant "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s17" "v134" false, .yield ["v134"]] ["v135"],
    .cond "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s22" "v135" ["v119", "v122", "v123"] [.operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s23" "zkl_binding_1" [] ["v119"] ["v136"], .operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s24" "zkl_binding_4" [] ["v136", "v123"] ["v137"], .operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s25_44_s3h7a6b6311h6d756c74696c696e6561724h726f7773_2_s0" "zkl_binding_0" [.text "64"] [] ["v138"], .operation "lc_h_4dc29171484fe119bcb93517e77d9153355950c493d148d41fd9d9a365c69100" "zkl_binding_5" [] ["v122", "v138"] ["v139"], .cond "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s25_44_s3h7a6b6311h6d756c74696c696e6561724h726f7773_2_s2" "v139" [] [.yield []] [.stop "lc_h_58e72c9acd76f03349acc9cf4c9d15a9441abdaa22fba3359347216ef9db5f0a" "reject"] [], .operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s25_44_s3h7a6b6311h6d756c74696c696e6561724h726f7773_2_s3" "zkl_binding_0" [.text "1"] [] ["v140"], .operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s25_44_s3h7a6b6311h6d756c74696c696e6561724h726f7773_2_s5" "zkl_binding_0" [.text "0"] [] ["v141"], .iterate "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s25_44_s3h7a6b6311h6d756c74696c696e6561724h726f7773_2_s6" "v142" "v141" "v122" [("v143", "v140")] [] [.operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s25_44_s3h7a6b6311h6d756c74696c696e6561724h726f7773_2_s7" "zkl_binding_0" [.text "2"] [] ["v144"], .operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s25_44_s3h7a6b6311h6d756c74696c696e6561724h726f7773_2_s8" "zkl_binding_6" [] ["v143", "v144"] ["v145"], .yield ["v145"]] ["v146"], .operation "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s26" "zkl_binding_3" [] ["v137", "v146"] ["v147"], .yield ["v147"]] [.constant "lc_2_s3_54_s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065_3_s28" "v148" false, .yield ["v148"]] ["v149"],
    .cond "lc_2_s6" "v149" ["v119", "v120", "v121"] [.operation "lc_2_s7_44_s8h73756d636865636b11h636865636b5f7461626c65_2_s1" "zkl_binding_1" [] ["v120"] ["v150"], .operation "lc_2_s7_44_s8h73756d636865636b11h636865636b5f7461626c65_2_s2" "zkl_binding_0" [.text "1"] [] ["v151"], .operation "lc_h_725764acc0c65074a290eb5fb8937fbc15f1d2c572432a1dc25fff0111a10ea0" "zkl_binding_0" [.text "0"] [] ["v152"], .operation "lc_h_b60025e678c8d6a1b6c7530d08db66794f015c953a01d619baa0cf95ef4b4e9e" "zkl_binding_5" [] ["v152", "v151"] ["v153"], .cond "lc_h_d22d27aaf8ba9abc236f0ae4ed7a62e5247b1960d453f16b7ffdad9e0e4d6c34" "v153" ["v150"] [.operation "lc_h_3129d68b797a42b649b723e9d531c8d67aeda51d8d82d0f989506b3be415ba97" "zkl_binding_0" [.text "64"] [] ["v154"], .operation "lc_h_481eceb6c9b5386a8e136527d9018f0dcd3d386f42e7cfb37aa004553ebab5f0" "zkl_binding_5" [] ["v150", "v154"] ["v155"], .yield ["v155"]] [.constant "lc_h_3c58e279990c973f17902dc16f133c1dfb2e5a80d01c07c34d0bdb11b22fc5cc" "v156" false, .yield ["v156"]] ["v157"], .cond "lc_h_d2378f087638edb3c24471d22ef2790a253bc31af674891c9785d82f0ab9117e" "v157" ["v119", "v151"] [.operation "lc_h_1b855b7fd960b9b70670ae6ed68a8a2726bb0ff402179935457b4e65634a229d" "zkl_binding_1" [] ["v119"] ["v158"], .operation "lc_h_b971262b7091c2f3f8d6a0cb80e9f2e109f3493c52be0916de61158af276692d" "zkl_binding_2" [] ["v158", "v151"] ["v159"], .operation "lc_h_094abd3d210bde771584972e180305fa14fa715b6083707b3e92938723e8ec98" "zkl_binding_0" [.text "0"] [] ["v160"], .operation "lc_h_fa9773a3edcab33a42563b8007fbcb4e323710ade2e3b040d842cd2147eb8870" "zkl_binding_3" [] ["v159", "v160"] ["v161"], .yield ["v161"]] [.constant "lc_h_288827d96280fddd25be6fcaadda72d8dc32724235b8c09b2f8b11ce0ce16f8d" "v162" false, .yield ["v162"]] ["v163"], .cond "lc_h_e8609657f0fa9d39be08f303a386cd15899cf418c641c907fa591455517b3e8d" "v163" ["v119", "v150", "v151"] [.operation "lc_h_a0ba19b9aeeb198cf2f42aa508f85b2e40937802fb07149fdfd402112466de72" "zkl_binding_1" [] ["v119"] ["v164"], .operation "lc_h_9f90d3103e63ecc5b4fc2e1ccead106a7734e356b493b94b2f1f4e1e9bad45b4" "zkl_binding_4" [] ["v164", "v151"] ["v165"], .operation "lc_h_88f4b315df9c56be6cb17f0ab000c4fbc63699dfe75fd735eac7ae878c2a6bb5" "zkl_binding_0" [.text "64"] [] ["v166"], .operation "lc_h_e829052ee4069fe4a17e4abf61016a16fc71347704d60f4300c5b9d8dc324254" "zkl_binding_5" [] ["v150", "v166"] ["v167"], .cond "lc_h_97b568a82f1ddfbea0ec8e0024bff8dacfddcc9110914b8e62c5dd9b41565ebe" "v167" [] [.yield []] [.stop "lc_h_6bcbbe63e6f23bab69f210d14f59bfbf391ff19fdf6c3d6e0335883f97a12ea6" "reject"] [], .operation "lc_h_d661c0236de91afc99a19161d479fcfa6149f3b76082d610691ed5da79b470b5" "zkl_binding_0" [.text "1"] [] ["v168"], .operation "lc_h_c3ba063e21c30f213092dcbedaeb98ed295d0c4d6b50a6bcc14af5ad59b29aaa" "zkl_binding_0" [.text "0"] [] ["v169"], .iterate "lc_h_3df4d169d0ca65016a66b2a5d82cf6155e0c0b3715c90faf31f5a69355f24b2f" "v170" "v169" "v150" [("v171", "v168")] [] [.operation "lc_h_906a82e412d1c7c25d1caec21d0c1325b2328d4cf2ca245d7ef33ed6bc34d4af" "zkl_binding_0" [.text "2"] [] ["v172"], .operation "lc_h_f1dba30b151924c507693ee879cec5394cda04846b7026cd538ff7657ebf6510" "zkl_binding_6" [] ["v171", "v172"] ["v173"], .yield ["v173"]] ["v174"], .operation "lc_h_6bd04eb984e50d34c372ad80bd3ec94cdced49cbf9105b98cb2f50684aa9e328" "zkl_binding_3" [] ["v165", "v174"] ["v175"], .yield ["v175"]] [.constant "lc_h_0ef31258126ccdbb788e4f3d952407710687ce3ba44549c69ec4cf502fc48bab" "v176" false, .yield ["v176"]] ["v177"], .cond "lc_2_s7_44_s8h73756d636865636b11h636865636b5f7461626c65_2_s3_46_s3h7a6b6311h6d756c74696c696e6561725h7461626c65_2_s1" "v177" [] [.yield []] [.stop "lc_2_s7_44_s8h73756d636865636b11h636865636b5f7461626c65_2_s3_46_s3h7a6b6311h6d756c74696c696e6561725h7461626c65_9_s1_reject" "reject"] [], .operation "lc_h_21ac35ce962ffcdb820a0d23254b12be23fe91448d8e2dcafb0af590cee88ca5" "_finite_binding_0" [] ["v120"] ["v178"], .operation "lc_h_41d726ae4cc1bd21657c0c281c3ee4c40b907fc3f7798f1638938f4c47a391c2" "_finite_binding_1" [.text "0"] [] ["v179"], .iterate "lc_h_c3c605656583ef6d82548d356fbafaf736b806710d67f99cad4edde486e6e192" "v180" "v179" "v178" [("v181", "v119"), ("v182", "v150"), ("v183", "v151")] ["v120", "v178"] [.operation "lc_h_3adb11b87c24f5ee7609f78e2b6296ec233b0869a34c58215a4fe23d60a24094" "_finite_binding_2" [] ["v120", "v180"] ["v184"], .operation "lc_h_f7e8625e30d3e362263409688953e828d0eab871e73eee92588a71b9b566dd70" "zkl_binding_0" [.text "0"] [] ["v185"], .operation "lc_h_82910649653b3478917c5d65c1542eb2c007aee49a9a8e709b53716df6472125" "zkl_binding_5" [] ["v185", "v182"] ["v186"], .cond "lc_h_dc59353d160052667e217a02186d99a31eb3721f919e9ac4e2dc0bc83dc7f4d1" "v186" [] [.yield []] [.stop "lc_h_1d4abf66d7b3d78a7daf513c4cce8d7d01ea5a1aa3fcd9c859b09403c354683c" "reject"] [], .operation "lc_h_a146c6c5cdc9162cce3bfe8046431184898edc21d4ec4e272327faf0fe648ec4" "zkl_binding_9" [] ["v181"] ["v187", "v188"], .operation "lc_h_7823b74a47b1a4ec5ba67f8d5136c6439fe16baac26e875ce57372f42f426dda" "_map_binding_0" [] ["v187"] ["v189"], .operation "lc_h_399db5d7a84f88323f3f97916e342052a9fa3c8ef257f68f529504a301cdb12f" "_map_binding_0" [] ["v188"] ["v190"], .operation "lc_h_fc14f6050d79dd5ec099aa334275c3254d58ad30b713cdbadb36ef1007f12048" "_map_binding_1" [] ["v189", "v190"] ["v191"], .operation "lc_h_0adace8b56b3f5dd7666883fdbdcf23fa523be75efda2af54905de5a86a3ef1c" "_map_binding_2" [] ["v191"] [], .operation "lc_h_f83aa9b22d531910323bbecc8e4e27cbb903251d6ea5c91b366d30510a5d6622" "_map_binding_3" [] ["v188", "v187"] ["v192"], .operation "lc_h_ab2ea60e6bf44b2fd910b8b1687fd0f7b2bd94aa1aa04c344ca6d5467f67dce6" "_map_binding_4" [] ["v192", "v184"] ["v193"], .operation "lc_h_478d85e97dd70633be8b718064db80a4ac5965beef6e0bd88475540fe1221cb7" "_map_binding_5" [] ["v187", "v193"] ["v194"], .operation "lc_h_061bb4095386582ab31a2235903ee3b4765d0e151c4c0a0d84ae0519c747a5ac" "zkl_binding_0" [.text "1"] [] ["v195"], .operation "lc_h_cd41c3e3414dd29c415f831c7441c0dc504fb92b77eb36d2810df8df7c201e74" "zkl_binding_10" [] ["v182", "v195"] ["v196"], .yield ["v194", "v196", "v183"]] ["v197", "v198", "v199"], .operation "lc_2_s7_44_s8h73756d636865636b11h636865636b5f7461626c65_2_s9" "zkl_binding_8" [] ["v197"] ["v200"], .operation "lc_2_s7_44_s8h73756d636865636b11h636865636b5f7461626c65_3_s11" "zkl_binding_12" [] ["v200", "v121"] ["v201"], .yield ["v201"]] [.constant "lc_2_s9" "v202" false, .yield ["v202"]] ["v203"],
    .ret ["v203"]]⟩

/-- The local function `_calculation_3`. -/
def function3 : Function :=
  ⟨"_calculation_3", [("v412", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v413", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v414", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [], [
    .operation "lc_6_kernel_6_kernel_1_0" "_kernel_binding_6" [] ["v412", "v413"] ["v415"],
    .operation "lc_6_kernel_6_kernel_1_1" "_kernel_binding_5" [] ["v414", "v415"] ["v416"],
    .cond "guard_control" "v416" [] [.yield []] [.stop "apply_18_label_726564756365_s24" "reject"] [],
    .ret []]⟩

/-- The local function `_calculation_4`. -/
def function4 : Function :=
  ⟨"_calculation_4", [("v417", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v418", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v419", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩], [
    .operation "lc_6_kernel_6_kernel_1_0" "_kernel_binding_9" [.text "1"] [] ["v420"],
    .operation "lc_6_kernel_6_kernel_1_1" "_kernel_binding_8" [] ["v420", "v417"] ["v421"],
    .operation "lc_6_kernel_6_kernel_1_2" "_kernel_binding_7" [] ["v421", "v418"] ["v422"],
    .operation "lc_6_kernel_6_kernel_1_3" "_kernel_binding_7" [] ["v417", "v419"] ["v423"],
    .operation "lc_6_kernel_6_kernel_1_4" "_kernel_binding_6" [] ["v422", "v423"] ["v424"],
    .ret ["v424"]]⟩

/-- The local function `_transcript_1`. -/
def function5 : Function :=
  ⟨"_transcript_1", [("v447", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v448", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v449", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v450"],
    .operation "coordinate_0" "_transcript_3" [] ["v450", "v449"] ["v451"],
    .operation "transition" "_transcript_0" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩] ["v447", "v448", "v451"] ["v452"],
    .ret ["v452"]]⟩

/-- The local function `_transcript_4`. -/
def function6 : Function :=
  ⟨"_transcript_4", [("v453", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v454", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v455", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v456"],
    .operation "coordinate_0" "_transcript_3" [] ["v456", "v455"] ["v457"],
    .operation "transition" "_transcript_0" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩] ["v453", "v454", "v457"] ["v458"],
    .ret ["v458"]]⟩

/-- The local function `_transcript_6`. -/
def function7 : Function :=
  ⟨"_transcript_6", [("v459", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v460", ⟨.data .index, "native.index/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v461"],
    .operation "coordinate_0" "_transcript_3" [] ["v461", "v460"] ["v462"],
    .operation "transition" "_transcript_5" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["query", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_6368616c6c656e6765", "input_5", "random.bls12-381.fr/0", "draw", "role00000001"]⟩] ["v459", "v462"] ["v463", "v464"],
    .ret ["v463", "v464"]]⟩

/-- The local function `_transcript_7`. -/
def function8 : Function :=
  ⟨"_transcript_7", [("v465", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v466", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v467", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "coordinates" "_transcript_2" [] [] ["v468"],
    .operation "coordinate_0" "_transcript_3" [] ["v468", "v467"] ["v469"],
    .operation "transition" "_transcript_0" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩] ["v465", "v466", "v469"] ["v470"],
    .ret ["v470"]]⟩

def validator : Validator where
  entry := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071"
  role := "role00000001"
  symbol := "_math_1"
  inputs := [("v425", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v426", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v427", ⟨.data .index, "native.index/0"⟩), ("v428", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)]
  results := [⟨.data .boolean, "native.bool/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩]
  body := [
    .call "apply_18_label_726564756365_s12" "zkl_411728361dd91cce996681067ff835983db4b50a2c76153019bcfb3dff123b46" [] ["v429"],
    .loop "apply_18_label_726564756365_s15" "v427" 2 "v430" [("v431", "v429"), ("v432", "v426"), ("v433", "v428")] [] [.receive "apply_18_label_726564756365_label_726f756e64_0" "apply_18_label_726564756365_label_726f756e64_0" "role00000000" "v434" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, .call "_transcript_12" "_transcript_1" ["v433", "v434", "v430"] ["v435"], .receive "apply_18_label_726564756365_label_726f756e64_1" "apply_18_label_726564756365_label_726f756e64_1" "role00000000" "v436" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, .call "_transcript_13" "_transcript_4" ["v435", "v436", "v430"] ["v437"], .call "apply_18_label_726564756365_s24" "_calculation_3" ["v434", "v436", "v432"] [], .call "_transcript_14" "_transcript_6" ["v437", "v430"] ["v438", "v439"], .call "_transcript_15" "_transcript_7" ["v439", "v438", "v430"] ["v440"], .call "apply_18_label_726564756365_s33" "zkl_e9d4e02b4f3bba21b953f31470da5acb0cd796fdc4c7898da74fbc3f5af04e58" ["v431", "v438"] ["v441"], .call "calculation_0" "_calculation_4" ["v438", "v434", "v436"] ["v442"], .yield ["v441", "v442", "v440"]] ["v443", "v444", "v445"],
    .call "s7" "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc" ["v425", "v443", "v444"] ["v446"],
    .ret ["v446", "v445"]]
  functions := [function0, function1, function2, function3, function4, function5, function6, function7, function8]
  bindings := [
    ⟨"_kernel_binding_7", "field.mul", ["bls12-381.fr"], "arkworks/field.mul"⟩,
    ⟨"_kernel_binding_8", "field.sub", ["bls12-381.fr"], "arkworks/field.sub"⟩,
    ⟨"_kernel_binding_9", "field.constant", ["bls12-381.fr"], "arkworks/field.constant"⟩,
    ⟨"_kernel_binding_5", "field.equal", ["bls12-381.fr"], "arkworks/field.equal"⟩,
    ⟨"_kernel_binding_6", "field.add", ["bls12-381.fr"], "arkworks/field.add"⟩,
    ⟨"_transcript_5", "transcript.native.indexed.challenge", ["merlin3.bls12-381.fr64be/0"], "arkworks/transcript.native.indexed.challenge"⟩,
    ⟨"_transcript_3", "indices.append", [], "native/indices.append"⟩,
    ⟨"_transcript_2", "indices.empty", [], "native/indices.empty"⟩,
    ⟨"_transcript_0", "transcript.native.indexed.observe.data", ["merlin3.bls12-381.fr64be/0", "field:bls12-381.fr"], "arkworks/transcript.native.indexed.observe.data"⟩,
    ⟨"_map_binding_5", "vector.add", ["bls12-381.fr"], "arkworks/vector.add"⟩,
    ⟨"_map_binding_4", "vector.scale", ["bls12-381.fr"], "arkworks/vector.scale"⟩,
    ⟨"_map_binding_3", "vector.sub", ["bls12-381.fr"], "arkworks/vector.sub"⟩,
    ⟨"_map_binding_2", "control.require", [], "arkworks/control.require"⟩,
    ⟨"_map_binding_1", "index.equal", [], "native/index.equal"⟩,
    ⟨"_map_binding_0", "vector.length", ["bls12-381.fr"], "arkworks/vector.length"⟩,
    ⟨"_finite_binding_2", "vector.get", ["bls12-381.fr"], "arkworks/vector.get"⟩,
    ⟨"_finite_binding_1", "index.constant", [], "native/index.constant"⟩,
    ⟨"_finite_binding_0", "vector.length", ["bls12-381.fr"], "arkworks/vector.length"⟩,
    ⟨"zkl_binding_12", "field.equal", ["bls12-381.fr"], "arkworks/field.equal"⟩,
    ⟨"zkl_binding_11", "vector.append", ["bls12-381.fr"], "arkworks/vector.append"⟩,
    ⟨"zkl_binding_10", "index.sub", [], "native/index.sub"⟩,
    ⟨"zkl_binding_9", "vector.split", ["bls12-381.fr"], "arkworks/vector.split"⟩,
    ⟨"zkl_binding_8", "vector.sum", ["bls12-381.fr"], "arkworks/vector.sum"⟩,
    ⟨"zkl_binding_7", "vector.empty", ["bls12-381.fr"], "arkworks/vector.empty"⟩,
    ⟨"zkl_binding_6", "index.mul", [], "native/index.mul"⟩,
    ⟨"zkl_binding_5", "index.less", [], "native/index.less"⟩,
    ⟨"zkl_binding_4", "index.div", [], "native/index.div"⟩,
    ⟨"zkl_binding_3", "index.equal", [], "native/index.equal"⟩,
    ⟨"zkl_binding_2", "index.mod", [], "native/index.mod"⟩,
    ⟨"zkl_binding_1", "vector.length", ["bls12-381.fr"], "arkworks/vector.length"⟩,
    ⟨"zkl_binding_0", "index.constant", [], "native/index.constant"⟩]

end ZkcExamples.Executable.SumcheckProofProgramData
