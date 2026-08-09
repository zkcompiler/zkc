// RUN: zkc-opt %pir-seal-full %pir-project-full %s | FileCheck %s
// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: %python %S/rewrite-pir-id.py %t.sealed %t.forged 0000000000000000000000000000000000000000000000000000000000000000
// RUN: not zkc-opt %pir-project-full %t.forged 2>&1 | FileCheck --check-prefix=IDENTITY %s
//
// Projection consumes a sealed protocol whose semantic closure is exact.
// The claim graph and material attachment remain source-artifact evidence;
// the verifier endpoint realizes every transcript/check obligation with src
// positions and carries the sealed id as provenance.

// IDENTITY: [zkc-E801] artifact id mismatch before write

// CHECK: pir.sealed "schnorr" id "[[PIR:[0-9a-f]{64}]]"
// CHECK: oir.artifact "schnorr" id "[[OIR:[0-9a-f]{64}]]" source "sha256:[[PIR]]" endpoint "verifier"
// CHECK: oir.program attributes {codecs = {scalar = "ts_be8", tg = "tg_be8"}, param_digests = ["codec:tg_be8=sha256:3350aaa6e9a9a99ed351e5da7429dc552e32597eef3990c26e7d414b8683c8aa", "codec:ts_be8=sha256:3350aaa6e9a9a99ed351e5da7429dc552e32597eef3990c26e7d414b8683c8aa", "sponge:toy_duplex=sha256:35aefee5b893ded95c3a1397e67477204f5f53711c9e7dc60d17efb6b2e26407"], statement_labels = ["statement"]}
// CHECK: ^bb0(%[[STATEMENT:.+]]: !oir.val<"tg", "public">, %[[STREAM:.+]]: !oir.stream):
// CHECK-NEXT: %[[SP0:.+]] = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
// CHECK-NEXT: %[[SP1:.+]] = oir.absorb %[[SP0]], %[[STATEMENT]] : <"tg", "public"> src [0]
// CHECK-NEXT: %[[S1:.+]], %[[COMMITMENT:.+]] = oir.read %[[STREAM]] "commitment" : "tg" src [1]
// CHECK-NEXT: %[[SP2:.+]] = oir.absorb %[[SP1]], %[[COMMITMENT]] : <"tg", "wire"> src [1]
// CHECK-NEXT: %[[SP3:.+]], %[[CHALLENGE:.+]] = oir.squeeze %[[SP2]] "challenge" : "scalar" count "1" domain "schnorr.challenge" rule "uniform" space "2305843009213693952" src [2]
// CHECK-NEXT: %[[S2:.+]], %[[RESPONSE:.+]] = oir.read %[[S1]] "response" : "scalar" src [3]
// CHECK-NEXT: %[[SP4:.+]] = oir.absorb %[[SP3]], %[[RESPONSE]] : <"scalar", "wire"> src [3]
// CHECK: oir.assert_eq {{.*}} as "equation" src [4]
// CHECK-NEXT: oir.expect_end %[[S2]]
// CHECK-NEXT: oir.decide %[[SP4]]

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
