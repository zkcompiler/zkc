// The shared seal engine accepts dotted construction namespaces, preserves
// discardable author metadata without perturbing identity, and rechecks the
// artifact it minted.
// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: FileCheck %s < %t.sealed
// RUN: zkc-opt %pir-recheck-full %t.sealed -o /dev/null
//
// The canonical encoder walks typed inherent state only (docs/spec/carrier.md
// §6), so a discardable attribute must never reach the identity. Sealing a
// stripped twin must yield a different artifact text (the note is really
// there) but the same id. The reference twin has no counterpart on purpose:
// its input representation cannot carry discardable metadata, so the policy
// is a carrier concern, not encoding-function semantics.
// RUN: sed 's/ attributes {pir.test_note = "preserve-me"}//' %s > %t.stripped
// RUN: zkc-opt %pir-seal-full %t.stripped -o %t.stripped.sealed
// RUN: not diff %t.sealed %t.stripped.sealed
// RUN: zkc-translate --id %t.sealed -o %t.id
// RUN: zkc-translate --id %t.stripped.sealed -o %t.stripped.id
// RUN: diff %t.id %t.stripped.id
// RUN: sed 's/"const:g", "witness:w"/"slot:commit_A", "witness:w"/' %t.sealed > %t.temporal-tamper
// RUN: not zkc-opt %pir-recheck-full %t.temporal-tamper 2>&1 | FileCheck %s --check-prefix=TEMPORAL-TAMPER
// RUN: sed 's/"zkc.hole.sigma-commit" = "sha256:[0-9a-f]*"/"zkc.hole.sigma-commit" = "sha256:0000000000000000000000000000000000000000000000000000000000000000"/' %t.sealed > %t.contract-tamper
// RUN: not zkc-opt %pir-recheck-full %t.contract-tamper 2>&1 | FileCheck %s --check-prefix=CONTRACT-TAMPER

// CHECK: pir.sealed "schnorr-namespaced"
// CHECK-SAME: hole_contracts = {"zkc.hole.sigma-commit" = "sha256:
// CHECK-SAME: "zkc.hole.sigma-response" = "sha256:
// CHECK-SAME: routes {instances = {prover.commit = {contract = "zkc.hole.sigma-commit"
// CHECK-SAME: prover.response = {contract = "zkc.hole.sigma-response", inputs = ["chal:c", "prover.commit.1"]}
// CHECK-SAME: attributes {pir.test_note = "preserve-me"}
// CHECK: binding "prover.commit.0"
// CHECK: binding "prover.response.0"
// TEMPORAL-TAMPER: [zkc-E223] route instance 'prover.commit' input #0 references event 'slot:commit_A' that is not earlier than its first materialization point
// CONTRACT-TAMPER: [zkc-E248] 'zkc.hole.sigma-commit' content digest does not match the loaded registry

pir.protocol "schnorr-namespaced"
    kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {prover.commit = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}, prover.response = {contract = "zkc.hole.sigma-response", inputs = ["chal:c", "prover.commit.1"]}}, witnesses = [["w", "sigma-witness"]]}
    attributes {pir.test_note = "preserve-me"} {
  %relation = pir.instantiate "dlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "commit_A" : "tg" in "sig" as "a" binding "prover.commit.0"
  %t3, %c = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "schnorr.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "resp_z" : "scalar" binding "prover.response.0"
  pir.check "verify" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "verify"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %y to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "verify"}
}
