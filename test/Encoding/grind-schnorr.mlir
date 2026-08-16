// REQUIRES: uv
// Routed Schnorr with a grinding round: after the response, the prover
// publishes a nonce and the following proof-of-work challenge must
// derive to zero. The nonce slot is supplied by a `pow_search` hole —
// the one hole kind that receives the sponge, as a state-identical
// read-only peek (docs/spec/endpoints.md §6.2) — so this protocol is
// the smallest subject whose prover exercises the transcript-peek
// supplier path end to end. The `rs` and `pow_value` class names are
// pinned by the shared `zkc.check.pow-zero` contract; here they route
// to the toy codec.
// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: FileCheck %s < %t.sealed
// RUN: zkc-translate --canonical %t.sealed -o %t.zkc
// RUN: %uv python -m oracle.parity encode schnorr-grind > %t.oracle
// RUN: diff %t.zkc %t.oracle
// RUN: zkc-translate --id %t.sealed -o %t.zkc-id
// RUN: %uv python -m oracle.parity id schnorr-grind > %t.oracle-id
// RUN: diff %t.zkc-id %t.oracle-id
//
// Both endpoint projections, byte-identical between the
// implementations: the prover carries the peek hole with its sponge
// operand and state-identical sponge result.
// RUN: zkc-opt %pir-project-full %t.sealed > %t.verifier
// RUN: zkc-translate --oir-canonical %t.verifier -o %t.v.zkc
// RUN: %uv python -m oracle.parity oir-encode schnorr-grind > %t.v.oracle
// RUN: diff %t.v.zkc %t.v.oracle
// RUN: zkc-opt %pir-project-prover-full %t.sealed > %t.prover
// RUN: FileCheck %s --check-prefix=PROVER < %t.prover
// RUN: zkc-translate --oir-canonical %t.prover -o %t.p.zkc
// RUN: %uv python -m oracle.parity oir-prover-encode schnorr-grind > %t.p.oracle
// RUN: diff %t.p.zkc %t.p.oracle
//
// PROVER: oir.artifact "grind-schnorr"
// PROVER-SAME: endpoint "prover_skeleton"
// PROVER: oir.hole_call "grind" kind "pow_search"
// PROVER: oir.write {{.*}} as "nonce" class "rs"
// PROVER: oir.squeeze {{.*}} "pow" : "pow_value"
// PROVER: oir.end_stream
// PROVER: oir.finish
//
// CHECK: pir.sealed "grind-schnorr"
// CHECK-SAME: "zkc.hole.toy-pow" = "sha256:
// CHECK: pir.slot {{.*}} "nonce" : "rs" in "grind" as "nonce" binding "grind.0"

pir.protocol "grind-schnorr" kappa {codecs = {pow_value = "ts_be8", rs = "ts_be8", scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}, zero = {class = "pow_value", value = "0"}}, iv = "artifact-id", sponge = "toy_duplex"} routes {instances = {commit = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}, grind = {contract = "zkc.hole.toy-pow", params = {bits = "8"}, inputs = []}, resp = {contract = "zkc.hole.sigma-response", inputs = ["chal:c", "commit.1"]}}, witnesses = [["w", "sigma-witness"]]} {
  %relation = pir.instantiate "dlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "commit_A" : "tg" in "sig" as "a" binding "commit.0"
  %t3, %c = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "schnorr.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "resp_z" : "scalar" binding "resp.0"
  %t5, %nonce = pir.slot %t4 "nonce" : "rs" in "grind" as "nonce" binding "grind.0"
  %t6, %pow = pir.chal %t5 deps(%nonce : !pir.val<"rs">) "pow" : "pow_value" domain "grind.pow" space "256"
  pir.check "verify" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.check "pow_pin" contract "zkc.check.pow-zero" (%nonce, %pow : !pir.val<"rs">, !pir.val<"pow_value">) expr ["eq", ["in", 1], ["const", "zero"]]
  pir.end %t6
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "verify"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  %ground = pir.reduce "grind" contract "grinding_sigma" (%evaluation : !pir.claim<"schnorr_evaluation">) deps(%pow : !pir.val<"pow_value">) checks {pow_pin = "pow_pin"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %y to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %ground : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-grinding" checks {pow_pin = "pow_pin"}
}
