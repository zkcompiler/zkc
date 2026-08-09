// REQUIRES: uv
// The first routed protocol: Schnorr carrying its construction routes,
// so the prover endpoint is derivable. Routes are declared protocol
// content — the seal resolves the cited hole contracts into the sixth
// vocabulary section and the canonical encoding carries the section
// with its references normalized (label-free), byte-identical between
// the carrier and the reference twin.
// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: FileCheck %s < %t.sealed
// RUN: zkc-translate --canonical %t.sealed -o %t.zkc
// RUN: %uv python -m oracle.parity encode schnorr-routed > %t.oracle
// RUN: diff %t.zkc %t.oracle
// RUN: zkc-translate --id %t.sealed -o %t.zkc-id
// RUN: %uv python -m oracle.parity id schnorr-routed > %t.oracle-id
// RUN: diff %t.zkc-id %t.oracle-id
//
// Both endpoint projections of the one seal, byte-identical between
// the implementations: the verifier as before, and the prover — the
// dual orchestration with its holes, witness ABI, and counterparty
// rows (docs/spec/endpoints.md §6.1; docs/spec/carrier.md §6.1).
// RUN: zkc-opt %pir-project-full %t.sealed > %t.verifier
// RUN: zkc-translate --oir-canonical %t.verifier -o %t.v.zkc
// RUN: %uv python -m oracle.parity oir-encode schnorr-routed > %t.v.oracle
// RUN: diff %t.v.zkc %t.v.oracle
// RUN: zkc-opt %pir-project-prover-full %t.sealed > %t.prover
// RUN: FileCheck %s --check-prefix=PROVER < %t.prover
// RUN: zkc-translate --oir-canonical %t.prover -o %t.p.zkc
// RUN: %uv python -m oracle.parity oir-prover-encode schnorr-routed > %t.p.oracle
// RUN: diff %t.p.zkc %t.p.oracle
// RUN: zkc-translate --oir-id %t.prover -o %t.p-id.zkc
// RUN: %uv python -m oracle.parity oir-prover-id schnorr-routed > %t.p-id.oracle
// RUN: diff %t.p-id.zkc %t.p-id.oracle
//
// PROVER: oir.artifact "schnorr"
// PROVER-SAME: endpoint "prover_skeleton"
// PROVER: counterparty = [
// PROVER-SAME: [4, "assert_eq"]
// PROVER-SAME: witness_labels = {{\[\[}}"w", "sigma-witness"]]
// PROVER: %arg1: !oir.handle<"sigma-witness">
// PROVER: oir.hole_call "commit" kind "commit"
// PROVER: oir.write {{.*}} as "commit_A" class "tg" src [1]
// PROVER: oir.squeeze {{.*}} "c" : "scalar"
// PROVER: oir.hole_call "resp" kind "evaluate"
// PROVER: oir.write {{.*}} as "resp_z" class "scalar" src [3]
// PROVER: oir.end_stream
// PROVER: oir.finish
//
// The sixth section appears exactly because routes cite contracts, and
// the routed protocol's identity differs from the unrouted schnorr's.
// CHECK: pir.sealed "schnorr"
// CHECK-SAME: hole_contracts = {"zkc.hole.sigma-commit" = "sha256:
// CHECK-SAME: "zkc.hole.sigma-response" = "sha256:
// CHECK-SAME: routes {instances = {commit = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}, resp = {contract = "zkc.hole.sigma-response", inputs = ["chal:c", "commit.1"]}}, witnesses = {{\[\[}}"w", "sigma-witness"]]}
// CHECK: pir.slot {{.*}} "commit_A" : "tg" in "sig" as "a" binding "commit.0"
// CHECK: pir.slot {{.*}} "resp_z" : "scalar" binding "resp.0"

pir.protocol "schnorr" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} routes {instances = {commit = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}, resp = {contract = "zkc.hole.sigma-response", inputs = ["chal:c", "commit.1"]}}, witnesses = [["w", "sigma-witness"]]} {
  %relation = pir.instantiate "dlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "commit_A" : "tg" in "sig" as "a" binding "commit.0"
  %t3, %c = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "schnorr.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "resp_z" : "scalar" binding "resp.0"
  pir.check "verify" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "verify"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %y to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "verify"}
}
