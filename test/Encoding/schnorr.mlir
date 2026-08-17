// REQUIRES: uv
// The canonical produced-claim witness for the encoding suite. Its terminal rule binds the
// relation statement to the verifier's public value, the producer message to
// the Schnorr commitment, and the producer challenge to the equation input.
// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: zkc-translate --canonical %t.sealed -o %t.zkc
// RUN: %uv python -m oracle.parity encode schnorr > %t.oracle
// RUN: diff %t.zkc %t.oracle
// RUN: zkc-translate --id %t.sealed -o %t.zkc-id
// RUN: %uv python -m oracle.parity id schnorr > %t.oracle-id
// RUN: diff %t.zkc-id %t.oracle-id
// RUN: zkc-opt %pir-project-full %t.sealed > %t.projected
// RUN: zkc-translate --oir-canonical %t.projected -o %t.oir.zkc
// RUN: %uv python -m oracle.parity oir-encode schnorr > %t.oir.oracle
// RUN: diff %t.oir.zkc %t.oir.oracle
// RUN: zkc-translate --oir-id %t.projected -o %t.oir-id.zkc
// RUN: %uv python -m oracle.parity oir-id schnorr > %t.oir-id.oracle
// RUN: diff %t.oir-id.zkc %t.oir-id.oracle
// RUN: rm -rf %t.artifacts
// The destination is named `--output-dir` because it is a directory
// where every sibling tool's `-o` is a file; `-o` remains as an alias
// and the rest of the suite still spells it that way, so both names are
// exercised.
// RUN: zkc-seal %s %zkc-seal-full --output-dir %t.artifacts
// RUN: not zkc-translate --id %s 2>&1 | FileCheck --check-prefix=UNSEALED %s
//
// UNSEALED: container carries no resolved-vocabulary table

pir.protocol "schnorr" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} {
  %relation = pir.instantiate "dlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "commit_A" : "tg" in "sig" as "a"
  %t3, %c = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "schnorr.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "resp_z" : "scalar"
  pir.check "verify" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "verify"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %y to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "verify"}
}
