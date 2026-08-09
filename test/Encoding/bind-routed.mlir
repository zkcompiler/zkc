// A construction route whose input is a `bind:` reference.
//
// The canonical encoding normalizes six reference forms, and the routed corpus
// exercised four of them: `const:`, `witness:`, `chal:`, and the
// `<instance>.<n>` hole form. `bind:` and `slot:` appeared only in refusal
// tests, so their normalization — statement echo to event position — crossed
// the cross-implementation gate nowhere. This fixture is that gate for `bind:`.
// `slot:` remains uncovered: every scalar slot in the routed corpus is itself
// a hole output, so routing one is circular, and covering it needs a protocol
// with a slot that no hole produces.
// REQUIRES: uv

// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: zkc-translate --canonical %t.sealed -o %t.zkc
// RUN: %uv python -m oracle.parity encode bind-routed > %t.oracle
// RUN: diff %t.zkc %t.oracle
// RUN: zkc-translate --id %t.sealed -o %t.id
// RUN: %uv python -m oracle.parity id bind-routed > %t.id.oracle
// RUN: diff %t.id %t.id.oracle

pir.protocol "bind_routed" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} routes {instances = {commit = {contract = "zkc.hole.sigma-commit", inputs = ["bind:y", "witness:w"]}, resp = {contract = "zkc.hole.sigma-response", inputs = ["chal:c", "commit.1"]}}, witnesses = [["w", "sigma-witness"]]} {
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
