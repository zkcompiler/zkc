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
def program : String := "sha256:0f3306f658c7e5ece5da8ffd6b4df2df6f213a4dc8cba3404ad010b09fb2530d"

/-- The local function `zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0`. -/
def function0 : Function :=
  ⟨"zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", [("v71", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩, ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩], [
    .operation "lc_2_s0" "zkl_binding_7" [] [] ["v72"],
    .ret ["v72", "v71"]]⟩

/-- The local function `zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07`. -/
def function1 : Function :=
  ⟨"zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", [("v74", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v75", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩, ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩], [
    .ret ["v74", "v75"]]⟩

/-- The local function `zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d`. -/
def function2 : Function :=
  ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [("v114", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v115", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩], [
    .operation "lc_2_s0" "zkl_binding_11" [] ["v114", "v115"] ["v116"],
    .ret ["v116"]]⟩

/-- The local function `zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9`. -/
def function3 : Function :=
  ⟨"zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", [("v117", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v118", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩, ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩], [
    .ret ["v117", "v118"]]⟩

/-- The local function `zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc`. -/
def function4 : Function :=
  ⟨"zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", [("v119", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v120", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v121", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data .boolean, "native.bool/0"⟩], [
    .operation "lc_2_s3" "zkl_binding_1" [] ["v120"] ["v122"],
    .operation "lc_2_s4" "zkl_binding_0" [.text "1"] [] ["v123"],
    .operation "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_2_s0" "zkl_binding_0" [.text "0"] [] ["v124"],
    .operation "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_2_s1_35_s3h7a6b637h696e64696365734h6c657373_2_s0" "zkl_binding_5" [] ["v124", "v123"] ["v125"],
    .cond "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_2_s3" "v125" ["v122"] [.operation "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_2_s4" "zkl_binding_0" [.text "64"] [] ["v127"], .operation "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_2_s5_35_s3h7a6b637h696e64696365734h6c657373_2_s0" "zkl_binding_5" [] ["v122", "v127"] ["v128"], .yield ["v128"]] [.constant "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_2_s7" "v129" false, .yield ["v129"]] ["v126"],
    .cond "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s11" "v126" ["v119", "v123"] [.operation "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s12" "zkl_binding_1" [] ["v119"] ["v131"], .operation "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s13" "zkl_binding_2" [] ["v131", "v123"] ["v132"], .operation "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s14" "zkl_binding_0" [.text "0"] [] ["v133"], .operation "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s15" "zkl_binding_3" [] ["v132", "v133"] ["v134"], .yield ["v134"]] [.constant "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s17" "v135" false, .yield ["v135"]] ["v130"],
    .cond "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s22" "v130" ["v119", "v122", "v123"] [.operation "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s23" "zkl_binding_1" [] ["v119"] ["v137"], .operation "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s24" "zkl_binding_4" [] ["v137", "v123"] ["v138"], .operation "lc_h_553e1ced916885c4de876b66ad643e5151b7a91456bce7936c650b01bcf553ec" "zkl_binding_0" [.text "64"] [] ["v139"], .operation "lc_h_1231585da622505ddc067a82933f3e84ef34cd3a6a34dfc9d8492c4c12d173fb" "zkl_binding_5" [] ["v122", "v139"] ["v140"], .cond "lc_h_1bad62be48a3ff2ca5c5d70f47597f860b02ed955836988ca18e2213fe55c8af" "v140" [] [.yield []] [.stop "lc_h_0d998b419a649650043d84cf7e8d335727bba352eb7b937dba393725a6bc407a" "reject"] [], .operation "lc_h_15caa1324bd358095dd329e89d32ed911079352b95c798ca9c4c69d09f60c5dd" "zkl_binding_0" [.text "1"] [] ["v141"], .operation "lc_h_04f859f10884406b6df2e756e308764b9c5811ed986741fdfb1cf02adeeb3ab9" "zkl_binding_0" [.text "0"] [] ["v142"], .iterate "lc_h_0e45111e6bd6bcafba9130427ebd124d3ae9f93173a63b46165e98a4116483c3" "v144" "v142" "v122" [("v145", "v141")] [] [.operation "lc_h_3c6a91ce14ebc3754b692779dc81206b376949d2507ad874e9f4d06042cb30c4" "zkl_binding_0" [.text "2"] [] ["v146"], .operation "lc_h_c30530a602a85beb62473d35599d0eddbccdbe99c26a42d2a2ee8527faa32839" "zkl_binding_6" [] ["v145", "v146"] ["v147"], .yield ["v147"]] ["v143"], .operation "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s26" "zkl_binding_3" [] ["v138", "v143"] ["v148"], .yield ["v148"]] [.constant "lc_2_s5_68_zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655_3_s28" "v149" false, .yield ["v149"]] ["v136"],
    .cond "lc_2_s9" "v136" ["v119", "v120", "v121"] [.operation "lc_3_s12_68_zkl_967e003dd39c9e1730d1e9e543081e08e351228ff07f85fb14e1e88dbded8a99_2_s0" "zkl_binding_1" [] ["v120"] ["v151"], .operation "lc_3_s12_68_zkl_967e003dd39c9e1730d1e9e543081e08e351228ff07f85fb14e1e88dbded8a99_2_s1" "zkl_binding_0" [.text "1"] [] ["v152"], .operation "lc_h_38117909c407d8959f18de0bb24097d7c351772bae45bac3ace43823eddbe1aa" "zkl_binding_0" [.text "0"] [] ["v153"], .operation "lc_h_eb050228dd02b5e688e1cdeac2890a151703319afec6d1ff6eac306586147e3b" "zkl_binding_5" [] ["v153", "v152"] ["v154"], .cond "lc_h_8e0c096ef4a224514aed0e21b9d291d9023fd4ef7e8957e4eef0d9154afa682c" "v154" ["v151"] [.operation "lc_h_b7d29f573d8aac4ef48abb41d65bee7cba8aec28088092de20b5da55d5ebcab9" "zkl_binding_0" [.text "64"] [] ["v156"], .operation "lc_h_7abc3ae32a1a3bb4bbdab8046af48e7e9db5a1eac836e212572fa447a4ba9258" "zkl_binding_5" [] ["v151", "v156"] ["v157"], .yield ["v157"]] [.constant "lc_h_adfc46797502855bf5836a1e90e8aa7e7ec5f00a94e551d25ab9eec6ae99afe4" "v158" false, .yield ["v158"]] ["v155"], .cond "lc_h_07f548928ec63908608a445a968c5cabc3592c72946c51348654e4281b3be567" "v155" ["v119", "v152"] [.operation "lc_h_3d0c45299dc11d4c9c8d112fa4e8e1335fd752566d9b9d9264b5f2ff055c7598" "zkl_binding_1" [] ["v119"] ["v160"], .operation "lc_h_4b153a978e3d9f4509cd6def6e419960b4edf444ae60dbb0af70b8a9d1f95370" "zkl_binding_2" [] ["v160", "v152"] ["v161"], .operation "lc_h_9520647fadb09c276615a95615a77dd4946e1ab4f59a4f5fab634afd3623ed8a" "zkl_binding_0" [.text "0"] [] ["v162"], .operation "lc_h_0312f950ccf25bfb2fb9fc800a630900e7e493f5adf82f543d289a16e5ea99b8" "zkl_binding_3" [] ["v161", "v162"] ["v163"], .yield ["v163"]] [.constant "lc_h_22ca58aff8be0780e04d40f6604297830eb4bae6171eb128e0695b9ef02bd764" "v164" false, .yield ["v164"]] ["v159"], .cond "lc_h_1d708b7cebcd51d07b316041823f3f68479d201c359d62322ebabf17219c77f5" "v159" ["v119", "v151", "v152"] [.operation "lc_h_2dd839389e3e6d68e097ead5dbbfee0b5f4e75f874d9b3777324171f550c1f5c" "zkl_binding_1" [] ["v119"] ["v166"], .operation "lc_h_7046ce61c710aaa1b0c62ea8db33a5276c81d4eb8f2b367f3743ba629d53910c" "zkl_binding_4" [] ["v166", "v152"] ["v167"], .operation "lc_h_c5531e046b643086a49a211c2edda79456befc3aefbd536864a1785e3b0edc9c" "zkl_binding_0" [.text "64"] [] ["v168"], .operation "lc_h_6b40124c2d1d335fe24780634c5319d49f3a484455b6abfedcf842d0238adc50" "zkl_binding_5" [] ["v151", "v168"] ["v169"], .cond "lc_h_abd8cb4be48cdfd6d8f3264eab4cdd8f3b4d18c24b9fb0f521d39183f1237e6a" "v169" [] [.yield []] [.stop "lc_h_5f383712548ec72fb6a0dcdaa46fd8c773393818a0cce79445e4fe86ee66ab78" "reject"] [], .operation "lc_h_cc5c48f7856f38623d0acf34bc93a0a86977f1fef1e659a222ef43924de766d4" "zkl_binding_0" [.text "1"] [] ["v170"], .operation "lc_h_de0fa4ae7bac44594ac3fa540cdb2be7ec14b124cf873cb7265b0fd57108b320" "zkl_binding_0" [.text "0"] [] ["v171"], .iterate "lc_h_98acc9475b14fa6694fe5489333f1c3a62058b59c8acefa36d865d15858a1c6a" "v173" "v171" "v151" [("v174", "v170")] [] [.operation "lc_h_727791c853a42193f6dc7dddd2774ef13f3d6be5d38b8f59ed69fcc7fc36cfa6" "zkl_binding_0" [.text "2"] [] ["v175"], .operation "lc_h_aacbd0325d1caf75f0afa5a4907a3e1ff7aacea8e8e7aafdbfb8c9666ae92823" "zkl_binding_6" [] ["v174", "v175"] ["v176"], .yield ["v176"]] ["v172"], .operation "lc_h_ae76d18d8462f3d2021936c0d4c710ad1df2d976642689b2f153e52c5d75a677" "zkl_binding_3" [] ["v167", "v172"] ["v177"], .yield ["v177"]] [.constant "lc_h_6569e7b44aad8a67382b005c3dbb96d284c3cf70d65a5f29dbfea5173635e740" "v178" false, .yield ["v178"]] ["v165"], .cond "lc_h_9b81a2df4bc2ccbda77e7b88bfa675ebfeabee895d72182d22f6d8161d982514" "v165" [] [.yield []] [.stop "lc_h_04bbc53c47bfba3c4ea0bc1ede63296acc694e91785e2ca54bf334ead0d193ae" "reject"] [], .operation "lc_h_2c51d529375b0323ac2e09cec2adb371ac754050613cd9bbc9e9d109b2bb8b9d_finite_0" "_finite_binding_4" [] ["v120"] ["v179"], .operation "lc_h_2c51d529375b0323ac2e09cec2adb371ac754050613cd9bbc9e9d109b2bb8b9d_finite_1" "_finite_binding_5" [.text "0"] [] ["v180"], .iterate "lc_h_2c51d529375b0323ac2e09cec2adb371ac754050613cd9bbc9e9d109b2bb8b9d_finite_2" "v184" "v180" "v179" [("v185", "v119"), ("v186", "v151"), ("v187", "v152")] ["v120", "v179"] [.operation "lc_h_2c51d529375b0323ac2e09cec2adb371ac754050613cd9bbc9e9d109b2bb8b9d_finite_3" "_finite_binding_6" [] ["v120", "v184"] ["v188"], .operation "lc_h_2a379d3c2c74d2eddad8f319a678f09112d515ebae9447e68a7592af7e994c1f" "zkl_binding_0" [.text "0"] [] ["v189"], .operation "lc_h_db98653406abd7d3046b2288d86d4816a13c3811ae07d2e77c1d909f42bd21ff" "zkl_binding_5" [] ["v189", "v186"] ["v190"], .cond "lc_h_79f87d9263099aa619ee7f00b22159935f6566c9cfa2109c1a79c84900725e86" "v190" [] [.yield []] [.stop "lc_h_3377f3aefc04f76b2132e084d268823f37c82a34278e8666d1e288fc95694065" "reject"] [], .operation "lc_h_b7d81ece5653103276afbd50d8146bc55660ac91e9583880f5c4f9992a8d7f73" "zkl_binding_9" [] ["v185"] ["v191", "v192"], .operation "lc_h_5dafc9da2e58c03cb32b17a9f432a65b89f11111749f3c4dfc012937498e6556_finite_0" "_finite_binding_7" [] ["v191"] ["v193"], .operation "lc_h_5dafc9da2e58c03cb32b17a9f432a65b89f11111749f3c4dfc012937498e6556_finite_1" "_finite_binding_7" [] ["v192"] ["v194"], .operation "lc_h_5dafc9da2e58c03cb32b17a9f432a65b89f11111749f3c4dfc012937498e6556_finite_2" "_finite_binding_8" [] ["v193", "v194"] ["v195"], .operation "lc_h_5dafc9da2e58c03cb32b17a9f432a65b89f11111749f3c4dfc012937498e6556_finite_3" "_finite_binding_9" [] ["v195"] [], .operation "lc_h_5dafc9da2e58c03cb32b17a9f432a65b89f11111749f3c4dfc012937498e6556_finite_4" "_finite_binding_10" [.text "[\"zkc.ring/0\",[\"bls12-381.fr\",\"bls12-381.fr\",\"bls12-381.fr\"],[[\"input\",0],[\"input\",1],[\"input\",2],[\"neg\",0],[\"add\",1,3],[\"mul\",4,2],[\"add\",0,5]],[6]]"] ["v193", "v191", "v192", "v188"] ["v196"], .operation "lc_h_4fae4761817b749014d6f8cce15cebd92a4bfada0e4621604c29f1ad5b6217f5" "zkl_binding_0" [.text "1"] [] ["v197"], .operation "lc_h_f87c9c907e0cbf47ef73ca6c058c1a864de87c6872e0bb4077d7375d58734bd2" "zkl_binding_10" [] ["v186", "v197"] ["v198"], .yield ["v196", "v198", "v187"]] ["v181", "v182", "v183"], .operation "lc_3_s12_68_zkl_967e003dd39c9e1730d1e9e543081e08e351228ff07f85fb14e1e88dbded8a99_2_s7" "zkl_binding_8" [] ["v181"] ["v199"], .operation "lc_3_s12_68_zkl_967e003dd39c9e1730d1e9e543081e08e351228ff07f85fb14e1e88dbded8a99_2_s8" "zkl_binding_12" [] ["v199", "v121"] ["v200"], .yield ["v200"]] [.constant "lc_3_s14" "v201" false, .yield ["v201"]] ["v150"],
    .ret ["v150"]]⟩

/-- The local function `_calculation_3`. -/
def function5 : Function :=
  ⟨"_calculation_3", [("v343", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v344", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v345", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [], [
    .operation "lc_11_computation_6_kernel_1_0" "_numerical_binding_0" [] ["v343", "v344"] ["v346"],
    .operation "lc_11_computation_6_kernel_1_1" "_numerical_binding_8" [] ["v345", "v346"] ["v347"],
    .cond "guard_control" "v347" [] [.yield []] [.stop "apply_18_label_726564756365_s27" "reject"] [],
    .ret []]⟩

/-- The local function `_calculation_4`. -/
def function6 : Function :=
  ⟨"_calculation_4", [("v348", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v349", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v350", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩], [
    .operation "lc_11_computation_6_kernel_1_0" "_numerical_binding_9" [.text "1"] [] ["v351"],
    .operation "lc_11_computation_6_kernel_1_1" "_numerical_binding_2" [] ["v351", "v348"] ["v352"],
    .operation "lc_11_computation_6_kernel_1_2" "_numerical_binding_1" [] ["v352", "v349"] ["v353"],
    .operation "lc_11_computation_6_kernel_1_3" "_numerical_binding_1" [] ["v348", "v350"] ["v354"],
    .operation "lc_11_computation_6_kernel_1_4" "_numerical_binding_0" [] ["v353", "v354"] ["v355"],
    .ret ["v355"]]⟩

/-- The local function `_transcript_0`. -/
def function7 : Function :=
  ⟨"_transcript_0", [("v356", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v357", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v358", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v359"],
    .operation "lc_12_coordinate_0" "_transcript_2" [] ["v359", "v358"] ["v360"],
    .operation "lc_10_transition" "_transcript_3" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s18"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩] ["v356", "v357", "v360"] ["v361"],
    .ret ["v361"]]⟩

/-- The local function `_transcript_4`. -/
def function8 : Function :=
  ⟨"_transcript_4", [("v362", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v363", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v364", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v365"],
    .operation "lc_12_coordinate_0" "_transcript_2" [] ["v365", "v364"] ["v366"],
    .operation "lc_10_transition" "_transcript_3" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s18"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩] ["v362", "v363", "v366"] ["v367"],
    .ret ["v367"]]⟩

/-- The local function `_transcript_5`. -/
def function9 : Function :=
  ⟨"_transcript_5", [("v368", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v369", ⟨.data .index, "native.index/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v370"],
    .operation "lc_12_coordinate_0" "_transcript_2" [] ["v370", "v369"] ["v371"],
    .operation "lc_10_transition" "_transcript_6" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s18"⟩], ["query", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_6368616c6c656e6765", "input_6", "random.bls12-381.fr/0", "draw", "role00000001"]⟩] ["v368", "v371"] ["v372", "v373"],
    .ret ["v372", "v373"]]⟩

/-- The local function `_transcript_7`. -/
def function10 : Function :=
  ⟨"_transcript_7", [("v374", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v375", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v376", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v377"],
    .operation "lc_12_coordinate_0" "_transcript_2" [] ["v377", "v376"] ["v378"],
    .operation "lc_10_transition" "_transcript_3" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s18"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩] ["v374", "v375", "v378"] ["v379"],
    .ret ["v379"]]⟩

def validator : Validator where
  entry := "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071"
  role := "role00000001"
  symbol := "_math_1"
  inputs := [("v31", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v32", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v33", ⟨.data .index, "native.index/0"⟩), ("v34", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩)]
  results := [⟨.data .boolean, "native.bool/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩]
  body := [
    .call "s3" "zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0" ["v32"] ["v35", "v36"],
    .call "apply_18_label_726564756365_s12" "zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07" ["v35", "v36"] ["v37", "v38"],
    .loop "apply_18_label_726564756365_s18" "v33" 2 "v39" [("v40", "v37"), ("v41", "v38"), ("v42", "v34")] [] [.receive "apply_18_label_726564756365_label_726f756e64_0" "apply_18_label_726564756365_label_726f756e64_0" "role00000000" "v43" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, .call "_transcript_12" "_transcript_0" ["v42", "v43", "v39"] ["v44"], .receive "apply_18_label_726564756365_label_726f756e64_1" "apply_18_label_726564756365_label_726f756e64_1" "role00000000" "v45" ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, .call "_transcript_13" "_transcript_4" ["v44", "v45", "v39"] ["v46"], .call "apply_18_label_726564756365_s27" "_calculation_3" ["v43", "v45", "v41"] [], .call "_transcript_14" "_transcript_5" ["v46", "v39"] ["v47", "v48"], .call "_transcript_15" "_transcript_7" ["v48", "v47", "v39"] ["v49"], .call "apply_18_label_726564756365_s36" "zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d" ["v40", "v47"] ["v50"], .call "calculation_0" "_calculation_4" ["v47", "v43", "v45"] ["v51"], .yield ["v50", "v51", "v49"]] ["v52", "v53", "v54"],
    .call "apply_18_label_726564756365_s48" "zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9" ["v52", "v53"] ["v55", "v56"],
    .call "s9" "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc" ["v31", "v55", "v56"] ["v57"],
    .ret ["v57", "v54"]]
  functions := [function0, function1, function2, function3, function4, function5, function6, function7, function8, function9, function10]
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
