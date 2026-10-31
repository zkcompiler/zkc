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
def program : String := "sha256:655e03d730eaf11e700b4f7a3c1b5c325832b425bdd5c45ab24b74feb7d36a85"

/-- The local function `zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0`. -/
def function0 : Function :=
  ⟨"zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", [("v0", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩, ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩], [
    .operation "lc_2_s0" "zkl_binding_7" [] [] ["v1"],
    .ret ["v1", "v0"]]⟩

/-- The local function `zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07`. -/
def function1 : Function :=
  ⟨"zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", [("v0", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v1", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩, ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩], [
    .ret ["v0", "v1"]]⟩

/-- The local function `zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d`. -/
def function2 : Function :=
  ⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", [("v0", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v1", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩], [
    .operation "lc_2_s0" "zkl_binding_11" [] ["v0", "v1"] ["v2"],
    .ret ["v2"]]⟩

/-- The local function `zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9`. -/
def function3 : Function :=
  ⟨"zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", [("v0", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v1", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩, ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩], [
    .ret ["v0", "v1"]]⟩

/-- The local function `zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc`. -/
def function4 : Function :=
  ⟨"zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc", [("v0", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v1", ⟨.data (.vector "bls12-381.fr"), "arkworks.fr-vector/0"⟩), ("v2", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data .boolean, "native.bool/0"⟩], [
    .operation "lc_2_s3" "zkl_binding_1" [] ["v1"] ["v3"],
    .operation "lc_2_s4" "zkl_binding_0" [.text "1"] [] ["v4"],
    .operation "lc_h_BWqq3JFRd0Ik7JUWjPCQ2Hy75rembHrWo_3zHPZf81s" "zkl_binding_0" [.text "0"] [] ["v5"],
    .operation "lc_h_DGInLMj35ON7z2MN0fltZT9tGSpiJtj2sO3CsYiBVH0" "zkl_binding_5" [] ["v5", "v4"] ["v6"],
    .cond "lc_h_lLdBhdYvCLGx0F87yPDilzgvgUBeTTCQrJ0Y3rZWd7o" "v6" ["v3"] [.operation "lc_h_ocKhM1qSgU58I51qvBeU7v0cRvOLKPn9obR-e_xGG-Y" "zkl_binding_0" [.text "64"] [] ["v8"], .operation "lc_h_tHUrytv_-BZ9oDvf7vEiCS_1rfoVCIfC_PP1DkOgZyw" "zkl_binding_5" [] ["v3", "v8"] ["v9"], .yield ["v9"]] [.constant "lc_h_MOKio3m33u2wQUJFfoJWKqHqKEUQMJMd3CRF_xXYO7A" "v10" false, .yield ["v10"]] ["v7"],
    .cond "lc_h_LKd3TULl6QMYTkGa8plPREgZ3YKvdU9-mxB3Tx5V9sA" "v7" ["v0", "v4"] [.operation "lc_h_yIx4chuGAUYufaArkZKKbgys89ll_dwiJJNl4RaAQig" "zkl_binding_1" [] ["v0"] ["v12"], .operation "lc_h_2-CzDzeu10YNe8edRPbIh1KVsKD78guXRD73kxWky6k" "zkl_binding_2" [] ["v12", "v4"] ["v13"], .operation "lc_h_MuGT5-2QSGX-JjYs4ONhg4vd6tH-UQ2z6NjFyGtQdFk" "zkl_binding_0" [.text "0"] [] ["v14"], .operation "lc_h_Y5V8D3cV3ETeTmZhVX5TaVI_UPaKDaC9sb23luifXBs" "zkl_binding_3" [] ["v13", "v14"] ["v15"], .yield ["v15"]] [.constant "lc_h_jO9WsyBRw4ISqew2mlitRf4bpSKF8TWcDQdBsuvEeHw" "v16" false, .yield ["v16"]] ["v11"],
    .cond "lc_h_7MkscHqXdB3s3wcKaKTfP6UGsY1TIZEVNKRM6nkh1mQ" "v11" ["v0", "v3", "v4"] [.operation "lc_h_HMNoOMRT_tLSehCtZrYwyA5TLUiNYXxw-DWEtIwBJ8M" "zkl_binding_1" [] ["v0"] ["v18"], .operation "lc_h_jHTdJ3vzgWIkkoUF3e1HEKhw0EKsTI_DzX61u01DsUY" "zkl_binding_4" [] ["v18", "v4"] ["v19"], .operation "lc_h_VT4c7ZFohcTeh2tmrWQ-UVG3qRRWvOeTbGULAbz1U-w" "zkl_binding_0" [.text "64"] [] ["v20"], .operation "lc_h_EjFYXaYiUF3cBnqCkz8-hO80zTpqNN_J2EksTBLRc_s" "zkl_binding_5" [] ["v3", "v20"] ["v21"], .cond "lc_h_G61ivkij_yylxdcPR1l_hgsC7ZVYNpiMoY4iE_5VyK8" "v21" [] [.yield []] [.stop "lc_h_DZmLQZpkllAEPYTPfo0zVye7o1Lre5N9ujk3Jaa8QHo" "reject"] [], .operation "lc_h_FcqhMkvTWAld0ynonTLtkRB5NSuVx5jKnExp0J9gxd0" "zkl_binding_0" [.text "1"] [] ["v22"], .operation "lc_h_BPhZ8QiEQGtt8udW4wh2S5xYEe2YZ0H9-xzwKt7rOrk" "zkl_binding_0" [.text "0"] [] ["v23"], .iterate "lc_h_DkURHmvWvK-6kTBCfr0STTrp-TFzpjtGFl6YpBFkg8M" "v25" "v23" "v3" [("v26", "v22")] [] [.operation "lc_h_PGqRzhTrw3VLaSd53IEgazdpSdJQeth06fTQYELLMMQ" "zkl_binding_0" [.text "2"] [] ["v27"], .operation "lc_h_wwUwpgKoW-tiRz01WZ0O3bzNvpnCakLSou6FJ_qjKDk" "zkl_binding_6" [] ["v26", "v27"] ["v28"], .yield ["v28"]] ["v24"], .operation "lc_h_4xw7Cx6AgBpZYPNXucB75r0WgE7fZKptbrHJntPmx-E" "zkl_binding_3" [] ["v19", "v24"] ["v29"], .yield ["v29"]] [.constant "lc_h_V1lB06u_xpW_ZHoHxPUEUOnpMgkf0ALg1Ofg5QjgEeQ" "v30" false, .yield ["v30"]] ["v17"],
    .cond "lc_2_s9" "v17" ["v0", "v1", "v2"] [.operation "lc_h_9eP4MTqUAgaA_AIe-bNBwJr7iSjLjAmKOQHC03xOsQ8" "zkl_binding_1" [] ["v1"] ["v32"], .operation "lc_h_iMyHZpIeFrNF8MDxPUFwVDWNBXytFuxtHueuBXpk4tA" "zkl_binding_0" [.text "1"] [] ["v33"], .operation "lc_h_OBF5CcQH2JWfGN4LskCX18NRdyuuRbrDrOQ4I-3b4ao" "zkl_binding_0" [.text "0"] [] ["v34"], .operation "lc_h_6wUCKN0CteaI4c3qwokKFRcDMZr-xtH_bqwwZYYUfjs" "zkl_binding_5" [] ["v34", "v33"] ["v35"], .cond "lc_h_jgwJbvSiJFFK7Q4hudKR2QI_1O9-iVfk7vDZFUr6aCw" "v35" ["v32"] [.operation "lc_h_t9KfVz2KrE70irtB1lvufLqK7CgIgJLeILXaVdXryrk" "zkl_binding_0" [.text "64"] [] ["v37"], .operation "lc_h_erw64yoaO7S72rgEavSOfp21oerINuISVy-kR6S6klg" "zkl_binding_5" [] ["v32", "v37"] ["v38"], .yield ["v38"]] [.constant "lc_h_rfxGeXUChVv1g2oekOiqfn7F8AqU5VHSWrnuxq6Zr-Q" "v39" false, .yield ["v39"]] ["v36"], .cond "lc_h_B_VIko7GOQhgikRaloxcq8NZLHKUbFE0hlTkKBs75Wc" "v36" ["v0", "v33"] [.operation "lc_h_PQxFKZ3BHUycjREvpOjhM1_XUlZtm52SZLXy_wVcdZg" "zkl_binding_1" [] ["v0"] ["v41"], .operation "lc_h_SxU6l449n0UJzW3vbkGZYLTt9ESuYNuwr3C4qdH5U3A" "zkl_binding_2" [] ["v41", "v33"] ["v42"], .operation "lc_h_lSBkf62wnCdmFalWFad91JRuGrT1mk9fq2NK_TYj7Yo" "zkl_binding_0" [.text "0"] [] ["v43"], .operation "lc_h_AxL5UMzyW_svufyACmMJAOfkk_Wt-C9UPSiaFuXqmbg" "zkl_binding_3" [] ["v42", "v43"] ["v44"], .yield ["v44"]] [.constant "lc_h_IspYr_i-B4DgTUD2YEKXgw60uuYXHrEo4GlbnvAr12Q" "v45" false, .yield ["v45"]] ["v40"], .cond "lc_h_HXCLfOvNUdB7MWBBgj8_aEedIBw1nWIyLrq_FyGcd_U" "v40" ["v0", "v32", "v33"] [.operation "lc_h_Ldg5OJ4-bWjgl-rV27_uC19Odfh02bN3cyQXH1UMH1w" "zkl_binding_1" [] ["v0"] ["v47"], .operation "lc_h_cEbOYccQqqGwxi6o2zOlJ2yB1OuPKzZ_N0O6Yp1TkQw" "zkl_binding_4" [] ["v47", "v33"] ["v48"], .operation "lc_h_xVMeBGtkMIakmiEcLt2nlFa-_DrvvVNoZKF4XjsO3Jw" "zkl_binding_0" [.text "64"] [] ["v49"], .operation "lc_h_a0ASTC0dM1_iR4BjTFMZ1J86SERVtqv-3PhC0COK3FA" "zkl_binding_5" [] ["v32", "v49"] ["v50"], .cond "lc_h_q9jLS-SM39bY8yZOq0zdjztNGMJLn7D1IdORg_Ejfmo" "v50" [] [.yield []] [.stop "lc_h_Xzg3ElSOxy-2oNzapG_Yx3M5OBigzOeUReT-hu5mq3g" "reject"] [], .operation "lc_h_zFxI94VvOGI9Cs80vJOgqGl38f7x5lmiIu9Dkk3nZtQ" "zkl_binding_0" [.text "1"] [] ["v51"], .operation "lc_h_3g-krnusRFlKw_pUDNsr5-wUsSTPhzy3JlsP1XEIsyA" "zkl_binding_0" [.text "0"] [] ["v52"], .iterate "lc_h_mKzJR1sU-maU_lSJMz8cOmIFi1nIrO-jbYZdFYWKHGo" "v54" "v52" "v32" [("v55", "v51")] [] [.operation "lc_h_cneRyFOkIZP23H3d0ndO8T89a-XTi49Z7Wn8x_w2z6Y" "zkl_binding_0" [.text "2"] [] ["v56"], .operation "lc_h_qsvQMl0cr3Xwr6WkkHo-H_eqzqjo56r9v7jJZmrpKCM" "zkl_binding_6" [] ["v55", "v56"] ["v57"], .yield ["v57"]] ["v53"], .operation "lc_h_rnbRjYRi89ICGTbA1McQrR3y2XZkJomy8VPlLF11pnc" "zkl_binding_3" [] ["v48", "v53"] ["v58"], .yield ["v58"]] [.constant "lc_h_ZWnntEqtimc4KwBcPbuW0oTDz3DWWl8p2_6lFzY150A" "v59" false, .yield ["v59"]] ["v46"], .cond "lc_h_m4Gi30vCzL2nfnuIv6Z16_6r7oldchgtIvbYFh2YJRQ" "v46" [] [.yield []] [.stop "lc_h_BLvFPEe_ujxOoLwe3mMpasxpTpF4XiylS_M06tDRk64" "reject"] [], .operation "lc_h_LFHVKTdbAyOsLgnOwq2zcax1QFBhPNm7yenRCbK7i50_finite_0" "_finite_binding_4" [] ["v1"] ["v60"], .operation "lc_h_LFHVKTdbAyOsLgnOwq2zcax1QFBhPNm7yenRCbK7i50_finite_1" "_finite_binding_5" [.text "0"] [] ["v61"], .iterate "lc_h_LFHVKTdbAyOsLgnOwq2zcax1QFBhPNm7yenRCbK7i50_finite_2" "v65" "v61" "v60" [("v66", "v0"), ("v67", "v32"), ("v68", "v33")] ["v1", "v60"] [.operation "lc_h_LFHVKTdbAyOsLgnOwq2zcax1QFBhPNm7yenRCbK7i50_finite_3" "_finite_binding_6" [] ["v1", "v65"] ["v69"], .operation "lc_h_TfxgOc1TBPxgXGTUOMzvwylhkVt--o6YV3vdhkTY5ac" "zkl_binding_0" [.text "0"] [] ["v70"], .operation "lc_h_0P7xz20M34tqOe7truTjfy4fJeMFrDVBY3uQhWGfeuU" "zkl_binding_5" [] ["v70", "v67"] ["v71"], .cond "lc_h_YYh891RDZwJv9xSUbCfkZB8nGWiNUVaXoEVWPsLCHpA" "v71" [] [.yield []] [.stop "lc_h_VF6TdWJkuCiNqE1tmgU-izgJleWxGcibLZ_TmP49hYg" "reject"] [], .operation "lc_h_JGnVqeeIy1mZv7zFDI29uF_EAaFjM9KSh41aqRT6xyc" "zkl_binding_9" [] ["v66"] ["v72", "v73"], .operation "lc_h_i-vXrHRBSkXtoMS8VXWMhET1TkfiTBsZJJQDdcmsAuc_finite_0" "_finite_binding_7" [] ["v72"] ["v74"], .operation "lc_h_i-vXrHRBSkXtoMS8VXWMhET1TkfiTBsZJJQDdcmsAuc_finite_1" "_finite_binding_7" [] ["v73"] ["v75"], .operation "lc_h_i-vXrHRBSkXtoMS8VXWMhET1TkfiTBsZJJQDdcmsAuc_finite_2" "_finite_binding_8" [] ["v74", "v75"] ["v76"], .operation "lc_h_i-vXrHRBSkXtoMS8VXWMhET1TkfiTBsZJJQDdcmsAuc_finite_3" "_finite_binding_9" [] ["v76"] [], .operation "lc_h_i-vXrHRBSkXtoMS8VXWMhET1TkfiTBsZJJQDdcmsAuc_finite_4" "_finite_binding_10" [.text "[\"zkc.ring/0\",[\"bls12-381.fr\",\"bls12-381.fr\",\"bls12-381.fr\"],[[\"input\",0],[\"input\",1],[\"input\",2],[\"neg\",0],[\"add\",1,3],[\"mul\",4,2],[\"add\",0,5]],[6]]"] ["v74", "v72", "v73", "v69"] ["v77"], .operation "lc_h_K2vms9OLRH0bq_NsseSSe7aBdSFxd-KUvh7YI6MTGWs" "zkl_binding_0" [.text "1"] [] ["v78"], .operation "lc_h_dK39woJwZDX2j33dRBZhu26ML6pPffEo-SXhnywVW7I" "zkl_binding_10" [] ["v67", "v78"] ["v79"], .yield ["v77", "v79", "v68"]] ["v62", "v63", "v64"], .operation "lc_h_HRdkszpIxCCgr3JzxhKeKHHgZMz9v8Obu8RRSXVOBmA" "zkl_binding_8" [] ["v62"] ["v80"], .operation "lc_h_hYU58ZP6DhOfOTqM7i_qbCj_MZUxCJNCbwYJAmAn73M" "zkl_binding_12" [] ["v80", "v2"] ["v81"], .yield ["v81"]] [.constant "lc_3_s14" "v82" false, .yield ["v82"]] ["v31"],
    .ret ["v31"]]⟩

/-- The local function `_calculation_3`. -/
def function5 : Function :=
  ⟨"_calculation_3", [("v0", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v1", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v2", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [], [
    .operation "lc_11_computation_6_kernel_1_0" "_numerical_binding_0" [] ["v0", "v1"] ["v3"],
    .operation "lc_11_computation_6_kernel_1_1" "_numerical_binding_8" [] ["v2", "v3"] ["v4"],
    .cond "guard_control" "v4" [] [.yield []] [.stop "apply_18_label_726564756365_s27" "reject"] [],
    .ret []]⟩

/-- The local function `_calculation_4`. -/
def function6 : Function :=
  ⟨"_calculation_4", [("v0", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v1", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v2", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩], [
    .operation "lc_11_computation_6_kernel_1_0" "_numerical_binding_9" [.text "1"] [] ["v3"],
    .operation "lc_11_computation_6_kernel_1_1" "_numerical_binding_2" [] ["v3", "v0"] ["v4"],
    .operation "lc_11_computation_6_kernel_1_2" "_numerical_binding_1" [] ["v4", "v1"] ["v5"],
    .operation "lc_11_computation_6_kernel_1_3" "_numerical_binding_1" [] ["v0", "v2"] ["v6"],
    .operation "lc_11_computation_6_kernel_1_4" "_numerical_binding_0" [] ["v5", "v6"] ["v7"],
    .ret ["v7"]]⟩

/-- The local function `_transcript_0`. -/
def function7 : Function :=
  ⟨"_transcript_0", [("v0", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v1", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v2", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v3"],
    .operation "lc_12_coordinate_0" "_transcript_2" [] ["v3", "v2"] ["v4"],
    .operation "lc_10_transition" "_transcript_3" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s18"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_0", "label_726f756e64_0", "role00000000", "role00000001"]⟩] ["v0", "v1", "v4"] ["v5"],
    .ret ["v5"]]⟩

/-- The local function `_transcript_4`. -/
def function8 : Function :=
  ⟨"_transcript_4", [("v0", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v1", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v2", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v3"],
    .operation "lc_12_coordinate_0" "_transcript_2" [] ["v3", "v2"] ["v4"],
    .operation "lc_10_transition" "_transcript_3" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s18"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_726f756e64_1", "label_726f756e64_1", "role00000000", "role00000001"]⟩] ["v0", "v1", "v4"] ["v5"],
    .ret ["v5"]]⟩

/-- The local function `_transcript_5`. -/
def function9 : Function :=
  ⟨"_transcript_5", [("v0", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v1", ⟨.data .index, "native.index/0"⟩)], [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩, ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v2"],
    .operation "lc_12_coordinate_0" "_transcript_2" [] ["v2", "v1"] ["v3"],
    .operation "lc_10_transition" "_transcript_6" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s18"⟩], ["query", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_6368616c6c656e6765", "input_6", "random.bls12-381.fr/0", "draw", "role00000001"]⟩] ["v0", "v3"] ["v4", "v5"],
    .ret ["v4", "v5"]]⟩

/-- The local function `_transcript_7`. -/
def function10 : Function :=
  ⟨"_transcript_7", [("v0", ⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩), ("v1", ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩), ("v2", ⟨.data .index, "native.index/0"⟩)], [⟨.transcript "merlin3.bls12-381.fr64be/0", "host.resource/0"⟩], [
    .operation "lc_11_coordinates" "_transcript_1" [] [] ["v3"],
    .operation "lc_12_coordinate_0" "_transcript_2" [] ["v3", "v2"] ["v4"],
    .operation "lc_10_transition" "_transcript_3" [.template ⟨"zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", [⟨"apply", "zkl_ba110e6c2c5207ba20905eec0c37f2bbf16736574645c8de8dee0d5abb5f2071", "label_726564756365"⟩, ⟨"repeat", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "s18"⟩], ["message", "zkl_6489eec61b35dc83c10f78141ab9b724ba83c1e9d722a7d909e3ba149ae99ae5", "label_64656c6976657279_0", "label_64656c6976657279_0", "role00000001", "role00000000"]⟩] ["v0", "v1", "v4"] ["v5"],
    .ret ["v5"]]⟩

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
