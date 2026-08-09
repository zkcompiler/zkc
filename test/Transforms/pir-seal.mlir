// RUN: zkc-opt %pir-seal-full %s | FileCheck %s
//
// The v4 seal boundary stamps one six-section vocabulary table and preserves
// the exact reduction, material attachment, and terminal rule that justified
// closure.  No operation-local digest mirrors or split registries remain.

// CHECK: pir.sealed "schnorr"
// CHECK-SAME: vocab {check_contracts = {"zkc.check.schnorr-equation"
// CHECK-SAME: claim_profiles = {opaque_relation
// CHECK-SAME: construction_profiles = {
// CHECK-SAME: reduction_contracts = {sigma =
// CHECK-SAME: terminal_rules = {"zkc.terminal.schnorr-evaluation"
// CHECK: %[[REL:.+]] = pir.instantiate "dlog" anchors
// CHECK: pir.check "equation" contract "zkc.check.schnorr-equation"
// CHECK: %[[EVAL:.+]] = pir.reduce "sigma" contract "sigma"
// CHECK: pir.material_bind {{.*}} to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"
// CHECK: pir.discharge %[[EVAL]] : <"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
pir.protocol "schnorr" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} {
  %relation = pir.instantiate "dlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %statement = pir.bind %t0 "statement" : "tg" stage instance
  %t2, %commitment = pir.slot %t1 "commitment" : "tg" in "sigma" as "a"
  %t3, %challenge = pir.chal %t2 deps(%statement, %commitment : !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "schnorr.challenge" space "2305843009213693952"
  %t4, %response = pir.slot %t3 "response" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %evaluation = pir.reduce "sigma" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}

// A relation whose endpoint closure is intentionally not modeled is not
// disguised as a proof.  Analysis mode records the residual explicitly.
// CHECK: pir.sealed "analysis"
// CHECK-SAME: policy "analysis_only_artifact"
// CHECK: pir.residual {{.*}} : <"opaque_relation"> route "relation-endpoint-unmodeled"
pir.protocol "analysis" kappa {codecs = {}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.end %t0
  pir.residual %relation : !pir.claim<"opaque_relation"> route "relation-endpoint-unmodeled"
}
