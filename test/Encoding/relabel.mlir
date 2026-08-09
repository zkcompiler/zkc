// RUN: zkc-opt %pir-seal-full %s | FileCheck %s

// PIR is fully positional: author handles select SSA objects during
// construction but do not enter canonical bytes. These are the same closed
// Schnorr proof under a consistent renaming of source, event, check, reduction,
// membership, material-binding, and terminal-selector handles.
// CHECK: pir.sealed "a" id "[[ID:[0-9a-f]+]]"
// CHECK: pir.sealed "b" id "[[ID]]"

pir.protocol "a" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %statement = pir.bind %t0 "statement" : "tg" stage instance
  %t2, %commitment = pir.slot %t1 "commitment" : "tg" in "sigma" as "a"
  %t3, %challenge = pir.chal %t2 deps(%statement, %commitment : !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "schnorr.c" space "2305843009213693952"
  %t4, %response = pir.slot %t3 "response" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %evaluation = pir.reduce "sigma" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}

pir.protocol "b" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} {
  %renamed_relation = pir.instantiate "renamed_relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %renamed_statement = pir.bind %t0 "renamed_statement" : "tg" stage instance
  %t2, %renamed_commitment = pir.slot %t1 "renamed_commitment" : "tg" in "renamed_sigma" as "a"
  %t3, %renamed_challenge = pir.chal %t2 deps(%renamed_statement, %renamed_commitment : !pir.val<"tg">, !pir.val<"tg">) "renamed_challenge" : "scalar" domain "schnorr.c" space "2305843009213693952"
  %t4, %renamed_response = pir.slot %t3 "renamed_response" : "scalar"
  pir.check "renamed_equation" contract "zkc.check.schnorr-equation" (%renamed_statement, %renamed_commitment, %renamed_challenge, %renamed_response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %renamed_evaluation = pir.reduce "renamed_sigma" contract "sigma" (%renamed_relation : !pir.claim<"opaque_relation">) deps(%renamed_challenge : !pir.val<"scalar">) checks {equation = "renamed_equation"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %renamed_statement to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %renamed_evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "renamed_equation"}
}
