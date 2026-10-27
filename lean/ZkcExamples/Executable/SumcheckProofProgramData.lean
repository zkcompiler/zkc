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
def program : String := "sha256:23a639f3a3147c01ad7af520c865946dac5898b3505dcfec90e16c80edfb2d2a"

/-- The local function `zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f`. -/
def function0 : Function :=
  ⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", [], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩], [
    .operation "lc_2_s0" "zkl_binding_7" [] [] ["v71"],
    .ret ["v71"]]⟩

/-- The local function `zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d`. -/
def function1 : Function :=
  ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [("v110", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v111", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩], [
    .operation "lc_2_s0" "zkl_binding_11" [] ["v110", "v111"] ["v112"],
    .ret ["v112"]]⟩

/-- The local function `zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc`. -/
def function2 : Function :=
  ⟨"zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", [("v113", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v114", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v115", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data .boolean, "native.bool/0"⟩], [
    .operation "lc_2_s1" "zkl_binding_1" [] ["v114"] ["v116"],
    .operation "lc_2_s2" "zkl_binding_0" [.text "1"] [] ["v117"],
    .operation "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_2_s0" "zkl_binding_0" [.text "0"] [] ["v118"],
    .operation "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_2_s1_35_s3h7a6b637h696e64696365734h6c657373_2_s0" "zkl_binding_5" [] ["v118", "v117"] ["v119"],
    .cond "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_2_s3" "v119" ["v116"] [.operation "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_2_s4" "zkl_binding_0" [.text "64"] [] ["v120"], .operation "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_2_s5_35_s3h7a6b637h696e64696365734h6c657373_2_s0" "zkl_binding_5" [] ["v116", "v120"] ["v121"], .yield ["v121"]] [.constant "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_2_s7" "v122" false, .yield ["v122"]] ["v123"],
    .cond "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s11" "v123" ["v113", "v117"] [.operation "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s12" "zkl_binding_1" [] ["v113"] ["v124"], .operation "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s13" "zkl_binding_2" [] ["v124", "v117"] ["v125"], .operation "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s14" "zkl_binding_0" [.text "0"] [] ["v126"], .operation "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s15" "zkl_binding_3" [] ["v125", "v126"] ["v127"], .yield ["v127"]] [.constant "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s17" "v128" false, .yield ["v128"]] ["v129"],
    .cond "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s22" "v129" ["v113", "v116", "v117"] [.operation "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s23" "zkl_binding_1" [] ["v113"] ["v130"], .operation "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s24" "zkl_binding_4" [] ["v130", "v117"] ["v131"], .operation "lc_h_83c0ff67e4a5d43ca5b2dcc732569f0b16ace54d3d66745dfb2bf6af88c7bfac" "zkl_binding_0" [.text "64"] [] ["v132"], .operation "lc_h_700c487caa92f44049e0cbbde8bfc07d4c541d4642a3d48ee38a7d33d2016ff0" "zkl_binding_5" [] ["v116", "v132"] ["v133"], .cond "lc_h_a8a13c3d34c85a1f9b12b1e3144fb75d882fee85adfd313d426555b7066b2159" "v133" [] [.yield []] [.stop "lc_h_898e3188ac38c91ded30d292ff5deb69eaa765af20e4ff929b79759e3d7c5da2" "reject"] [], .operation "lc_h_0b6ca402f268884662d3793f6c4957e7c2825bcdcc9e1b505acd6c51778176e2" "zkl_binding_0" [.text "1"] [] ["v134"], .operation "lc_h_2cf35f7795bb2aec47e6de54ecbeaf76807f9cd3250edf8a57befd40b64aff12" "zkl_binding_0" [.text "0"] [] ["v135"], .iterate "lc_h_2758562dd482f61942dca1d31cdf4136264df6830fb5de8d7a1515c122471322" "v136" "v135" "v116" [("v137", "v134")] [] [.operation "lc_h_8108dffc1e853902580a9a53c2f5cea26b5d2fab33a559fee9817e80c5b09203" "zkl_binding_0" [.text "2"] [] ["v138"], .operation "lc_h_9dde6db1c8668affe577b97798d6dc62d43d74bbc269ffc4bf209ebc0362a001" "zkl_binding_6" [] ["v137", "v138"] ["v139"], .yield ["v139"]] ["v140"], .operation "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s26" "zkl_binding_3" [] ["v131", "v140"] ["v141"], .yield ["v141"]] [.constant "lc_2_s3_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s28" "v142" false, .yield ["v142"]] ["v143"],
    .cond "lc_2_s6" "v143" ["v113", "v114", "v115"] [.operation "lc_2_s7_68_zkl_3b67bb5451d0deeed7ab9379c12e7c154a5c16946b7db9b65bc0d4be6b613f1d_2_s1" "zkl_binding_1" [] ["v114"] ["v144"], .operation "lc_2_s7_68_zkl_3b67bb5451d0deeed7ab9379c12e7c154a5c16946b7db9b65bc0d4be6b613f1d_2_s2" "zkl_binding_0" [.text "1"] [] ["v145"], .operation "lc_h_77723898cbb10e5aff9733bef87788f5d641ab4e1388335c9e67343fad3197e5" "zkl_binding_0" [.text "0"] [] ["v146"], .operation "lc_h_9165f59058251d0f2b506ce3a95009cfc5300d565227918acd93923751abba90" "zkl_binding_5" [] ["v146", "v145"] ["v147"], .cond "lc_h_6d252b3de587ac427590a77b4dc1b272c6d18090fe4216a2039f2b350e80cad9" "v147" ["v144"] [.operation "lc_h_ea0e4d359a4a75473a01fcbf2ceb29ddc21a96ee3eec0a8c0fd82cebd3da57a4" "zkl_binding_0" [.text "64"] [] ["v148"], .operation "lc_h_1d7d37728131a6e13d829d031ed584be9fabf25f5833527002b917cebce29854" "zkl_binding_5" [] ["v144", "v148"] ["v149"], .yield ["v149"]] [.constant "lc_h_ec5fcd6d2f69398008d4f6d997431ca85296fa1b266558d4937b70fa9873b0b2" "v150" false, .yield ["v150"]] ["v151"], .cond "lc_h_51fc36a2d11e0dd3213ed3aa3c6498c71f3305f73f63395f0585a82750acb807" "v151" ["v113", "v145"] [.operation "lc_h_b45cd73c76b8a9a9cee956578efa06540cf7f5bf5fcf83ae53792f6b611cea62" "zkl_binding_1" [] ["v113"] ["v152"], .operation "lc_h_853aadc2a98de1a525b804b733cef066082a6c008d2bf87a3a967aaab70b1ffc" "zkl_binding_2" [] ["v152", "v145"] ["v153"], .operation "lc_h_18566df492072dc587307fd0616f230674d1563a15d692ca31ad1093092f5c4b" "zkl_binding_0" [.text "0"] [] ["v154"], .operation "lc_h_959beb16ea8684393f2b065b9e2253fcfa52b64cf89289ee8797df2c221acc02" "zkl_binding_3" [] ["v153", "v154"] ["v155"], .yield ["v155"]] [.constant "lc_h_cb0bdefacbe95cb3b383be2def05426ada7f8ced12a7729ac2c59defc37c17ca" "v156" false, .yield ["v156"]] ["v157"], .cond "lc_h_ac3fe6edfab1b0933ae0b9fbdf4dff62adae32a5c9c4a92db77c96e2bcc24d1d" "v157" ["v113", "v144", "v145"] [.operation "lc_h_eaaaa754e4fcf9bb71bcd4397a66d0bffe2fd221d05ad16978e2e5e4ecaebf67" "zkl_binding_1" [] ["v113"] ["v158"], .operation "lc_h_16046cc05ad7a2ad7cc79bbeee845197528ba32faab3436cebbeaed8bd0b7783" "zkl_binding_4" [] ["v158", "v145"] ["v159"], .operation "lc_h_6d64195d08a32c6dc983ab6e9cdf3457269dcf8847a3c58b7c647ce70239ef05" "zkl_binding_0" [.text "64"] [] ["v160"], .operation "lc_h_45b5a421dc09b3517639ddfddcb1f3479e9981364d53edc51d7c03ac78d2f1b9" "zkl_binding_5" [] ["v144", "v160"] ["v161"], .cond "lc_h_6c2f93e6cea2412ddd23acdf95fa1b93daf47ad16de5e2e3f09df56824bda5ec" "v161" [] [.yield []] [.stop "lc_h_1eabdfe972bae68f0e2968b8205939a0ceb248dd05f818562dc0181f9185ae58" "reject"] [], .operation "lc_h_9b62e2b7002318c12f4b218ee1140072afddbc4d1251859a847b3664d1db5b01" "zkl_binding_0" [.text "1"] [] ["v162"], .operation "lc_h_fdcd94321f6e2472a38a7da1e3813a67e9852c6d49d3d70babfd70d9cbc107f1" "zkl_binding_0" [.text "0"] [] ["v163"], .iterate "lc_h_6ee567cec9218371a97366e963d26131358b5e155ac0087ef4347d441ade5540" "v164" "v163" "v144" [("v165", "v162")] [] [.operation "lc_h_c0b5941603792444ecae255c1f23bdd2c873357a44a2ede7dad2657e7e97341f" "zkl_binding_0" [.text "2"] [] ["v166"], .operation "lc_h_22cb61b11a51c99c2bddf4655cb18c0649a1a6cb811af764e8cc00365bc12d61" "zkl_binding_6" [] ["v165", "v166"] ["v167"], .yield ["v167"]] ["v168"], .operation "lc_h_ce2a6345f2fd00aaa3161fdf68e4272f68c141a96a9e76182e28084d50b44e4c" "zkl_binding_3" [] ["v159", "v168"] ["v169"], .yield ["v169"]] [.constant "lc_h_3299a3a80983b4fb332985580b917b9727820123af1d3abe028e9c01936b7c6a" "v170" false, .yield ["v170"]] ["v171"], .cond "lc_h_87d58fd92d1d9d8f24090394c8440a8b046d5a1578b365850248f697c3042440" "v171" [] [.yield []] [.stop "lc_h_c3681843b330eea8f3df35a1104416bc23ee87bf2888ed4db17db6a95f6331a1" "reject"] [], .operation "lc_h_27d89c983c1b3d57e0b724cc37643bf0e2f2f4174ece8597ae24bb111ce6f9e5_finite_0" "_finite_binding_4" [] ["v114"] ["v172"], .operation "lc_h_27d89c983c1b3d57e0b724cc37643bf0e2f2f4174ece8597ae24bb111ce6f9e5_finite_1" "_finite_binding_5" [.text "0"] [] ["v173"], .iterate "lc_h_27d89c983c1b3d57e0b724cc37643bf0e2f2f4174ece8597ae24bb111ce6f9e5_finite_2" "v174" "v173" "v172" [("v175", "v113"), ("v176", "v144"), ("v177", "v145")] ["v114", "v172"] [.operation "lc_h_27d89c983c1b3d57e0b724cc37643bf0e2f2f4174ece8597ae24bb111ce6f9e5_finite_3" "_finite_binding_6" [] ["v114", "v174"] ["v178"], .operation "lc_h_6f2b9ef5a1075c7d7b256e179f97d4175a48bd6607591619cd34eeefedf24886" "zkl_binding_0" [.text "0"] [] ["v179"], .operation "lc_h_0ca782755fa5761781a438f21ba891ce6052c9614562f7cc7e5672f972141d1b" "zkl_binding_5" [] ["v179", "v176"] ["v180"], .cond "lc_h_188eb235fcaadd585f0e23d66ca8a1dbb6c835e55b6aba6ebbad11c74d91b6d0" "v180" [] [.yield []] [.stop "lc_h_36dd7567f881adc823c4b65cd755b12970cae9d597c24248495cf0557aa79bed" "reject"] [], .operation "lc_h_76a30aa2fe1f6a52c7814099f7d1a543606411718cc8c4387e7f67e65e09ae07" "zkl_binding_9" [] ["v175"] ["v181", "v182"], .operation "lc_h_35ce1c676b6ea35786cfa36f6f2999df7c03432df09d659f1642cf445996d44d_finite_0" "_finite_binding_7" [] ["v181"] ["v183"], .operation "lc_h_35ce1c676b6ea35786cfa36f6f2999df7c03432df09d659f1642cf445996d44d_finite_1" "_finite_binding_7" [] ["v182"] ["v184"], .operation "lc_h_35ce1c676b6ea35786cfa36f6f2999df7c03432df09d659f1642cf445996d44d_finite_2" "_finite_binding_8" [] ["v183", "v184"] ["v185"], .operation "lc_h_35ce1c676b6ea35786cfa36f6f2999df7c03432df09d659f1642cf445996d44d_finite_3" "_finite_binding_9" [] ["v185"] [], .operation "lc_h_35ce1c676b6ea35786cfa36f6f2999df7c03432df09d659f1642cf445996d44d_finite_4" "_finite_binding_10" [.text "[\"zkc.ring/0\",[\"bls12-381.fr\",\"bls12-381.fr\",\"bls12-381.fr\"],[[\"input\",0],[\"input\",1],[\"input\",2],[\"neg\",0],[\"add\",1,3],[\"mul\",4,2],[\"add\",0,5]],[6]]"] ["v183", "v181", "v182", "v178"] ["v186"], .operation "lc_h_ea672dc13cd82a991536f0f38d68c928af9c14bb700a4cb8ef997360884e9a68" "zkl_binding_0" [.text "1"] [] ["v187"], .operation "lc_h_99e6e04ee527076d8d5d68baadc670d7c8f0efe90fea7eed040c2fd336d318d9" "zkl_binding_10" [] ["v176", "v187"] ["v188"], .yield ["v186", "v188", "v177"]] ["v189", "v190", "v191"], .operation "lc_2_s7_68_zkl_3b67bb5451d0deeed7ab9379c12e7c154a5c16946b7db9b65bc0d4be6b613f1d_2_s9" "zkl_binding_8" [] ["v189"] ["v192"], .operation "lc_2_s7_68_zkl_3b67bb5451d0deeed7ab9379c12e7c154a5c16946b7db9b65bc0d4be6b613f1d_3_s11" "zkl_binding_12" [] ["v192", "v115"] ["v193"], .yield ["v193"]] [.constant "lc_2_s9" "v194" false, .yield ["v194"]] ["v195"],
    .ret ["v195"]]⟩

/-- The local function `_calculation_3`. -/
def function3 : Function :=
  ⟨"_calculation_3", [("v337", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v338", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v339", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [], [
    .operation "lc_11_computation_6_kernel_1_0" "_numerical_binding_0" [] ["v337", "v338"] ["v340"],
    .operation "lc_11_computation_6_kernel_1_1" "_numerical_binding_8" [] ["v339", "v340"] ["v341"],
    .cond "guard_control" "v341" [] [.yield []] [.stop "apply_18_label_726564756365_s24" "reject"] [],
    .ret []]⟩

/-- The local function `_calculation_4`. -/
def function4 : Function :=
  ⟨"_calculation_4", [("v342", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v343", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v344", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩], [
    .operation "lc_11_computation_6_kernel_1_0" "_numerical_binding_9" [.text "1"] [] ["v345"],
    .operation "lc_11_computation_6_kernel_1_1" "_numerical_binding_2" [] ["v345", "v342"] ["v346"],
    .operation "lc_11_computation_6_kernel_1_2" "_numerical_binding_1" [] ["v346", "v343"] ["v347"],
    .operation "lc_11_computation_6_kernel_1_3" "_numerical_binding_1" [] ["v342", "v344"] ["v348"],
    .operation "lc_11_computation_6_kernel_1_4" "_numerical_binding_0" [] ["v347", "v348"] ["v349"],
    .ret ["v349"]]⟩

/-- The local function `_transcript_0`. -/
def function5 : Function :=
  ⟨"_transcript_0", [("v350", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v351", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v352", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v353"],
    .operation "lc_12_coordinate_0" "_transcript_2" [] ["v353", "v352"] ["v354"],
    .operation "lc_10_transition" "_transcript_3" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩] ["v350", "v351", "v354"] ["v355"],
    .ret ["v355"]]⟩

/-- The local function `_transcript_4`. -/
def function6 : Function :=
  ⟨"_transcript_4", [("v356", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v357", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v358", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v359"],
    .operation "lc_12_coordinate_0" "_transcript_2" [] ["v359", "v358"] ["v360"],
    .operation "lc_10_transition" "_transcript_3" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩] ["v356", "v357", "v360"] ["v361"],
    .ret ["v361"]]⟩

/-- The local function `_transcript_5`. -/
def function7 : Function :=
  ⟨"_transcript_5", [("v362", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v363", ⟨.data .index, "native.index/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v364"],
    .operation "lc_12_coordinate_0" "_transcript_2" [] ["v364", "v363"] ["v365"],
    .operation "lc_10_transition" "_transcript_6" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["query", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_6368616c6c656e6765", "input_5", "random.bls12-381.fr/0", "draw", "role00000001"]⟩] ["v362", "v365"] ["v366", "v367"],
    .ret ["v366", "v367"]]⟩

/-- The local function `_transcript_7`. -/
def function8 : Function :=
  ⟨"_transcript_7", [("v368", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v369", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v370", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v371"],
    .operation "lc_12_coordinate_0" "_transcript_2" [] ["v371", "v370"] ["v372"],
    .operation "lc_10_transition" "_transcript_3" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s15"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩] ["v368", "v369", "v372"] ["v373"],
    .ret ["v373"]]⟩

def validator : Validator where
  entry := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071"
  role := "role00000001"
  symbol := "_math_1"
  inputs := [("v31", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v32", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v33", ⟨.data .index, "native.index/0"⟩), ("v34", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)]
  results := [⟨.data .boolean, "native.bool/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩]
  body := [
    .call "apply_18_label_726564756365_s12" "zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f" [] ["v35"],
    .loop "apply_18_label_726564756365_s15" "v33" 2 "v36" [("v37", "v35"), ("v38", "v32"), ("v39", "v34")] [] [.receive "apply_18_label_726564756365_label_726f756e64_0" "apply_18_label_726564756365_label_726f756e64_0" "role00000000" "v40" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, .call "_transcript_12" "_transcript_0" ["v39", "v40", "v36"] ["v41"], .receive "apply_18_label_726564756365_label_726f756e64_1" "apply_18_label_726564756365_label_726f756e64_1" "role00000000" "v42" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, .call "_transcript_13" "_transcript_4" ["v41", "v42", "v36"] ["v43"], .call "apply_18_label_726564756365_s24" "_calculation_3" ["v40", "v42", "v38"] [], .call "_transcript_14" "_transcript_5" ["v43", "v36"] ["v44", "v45"], .call "_transcript_15" "_transcript_7" ["v45", "v44", "v36"] ["v46"], .call "apply_18_label_726564756365_s33" "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d" ["v37", "v44"] ["v47"], .call "calculation_0" "_calculation_4" ["v44", "v40", "v42"] ["v48"], .yield ["v47", "v48", "v46"]] ["v49", "v50", "v51"],
    .call "s7" "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc" ["v31", "v49", "v50"] ["v52"],
    .ret ["v52", "v51"]]
  functions := [function0, function1, function2, function3, function4, function5, function6, function7, function8]
  bindings := [
    ⟨"_finite_binding_10", "numerical.map", ["bls12-381.fr", "110"], "arkworks/numerical.map", []⟩,
    ⟨"_finite_binding_9", "control.require", [], "arkworks/control.require", []⟩,
    ⟨"_finite_binding_8", "index.equal", [], "native/index.equal", []⟩,
    ⟨"_finite_binding_7", "vector.length", ["bls12-381.fr"], "arkworks/vector.length", []⟩,
    ⟨"_finite_binding_6", "vector.get", ["bls12-381.fr"], "arkworks/vector.get", []⟩,
    ⟨"_finite_binding_5", "index.constant", [], "native/index.constant", []⟩,
    ⟨"_finite_binding_4", "vector.length", ["bls12-381.fr"], "arkworks/vector.length", []⟩,
    ⟨"_transcript_6", "transcript.native.indexed.challenge", ["merlin3.bls12-381.fr64be/0"], "arkworks/transcript.native.indexed.challenge", []⟩,
    ⟨"_transcript_3", "transcript.native.indexed.observe.data", ["merlin3.bls12-381.fr64be/0", "field:bls12-381.fr"], "arkworks/transcript.native.indexed.observe.data", [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩]⟩,
    ⟨"_transcript_2", "indices.append", [], "native/indices.append", []⟩,
    ⟨"_transcript_1", "indices.empty", [], "native/indices.empty", []⟩,
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
    ⟨"zkl_binding_0", "index.constant", [], "native/index.constant", []⟩,
    ⟨"_numerical_binding_0", "field.add", ["bls12-381.fr"], "arkworks/field.add", []⟩,
    ⟨"_numerical_binding_1", "field.mul", ["bls12-381.fr"], "arkworks/field.mul", []⟩,
    ⟨"_numerical_binding_2", "field.sub", ["bls12-381.fr"], "arkworks/field.sub", []⟩,
    ⟨"_numerical_binding_8", "field.equal", ["bls12-381.fr"], "arkworks/field.equal", []⟩,
    ⟨"_numerical_binding_9", "field.constant", ["bls12-381.fr"], "arkworks/field.constant", []⟩]

end ZkcExamples.Executable.SumcheckProofProgramData
