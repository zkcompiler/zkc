// Synthetic carrier fixture for one generic construction-profile rule.  It is
// not a Plonky3, FRI, or SP1 verifier representation and executes no Poseidon2
// permutation.  All payload classes use the same Ext4 tuple shape solely to
// keep the fixture's codec boundary honest and minimal.
pir.protocol "tuple_bijection_v4" kappa {codecs = {ext_field = "plonky3_bb31_ext4_tuple", scalar = "plonky3_bb31_ext4_tuple", tg = "plonky3_bb31_ext4_tuple"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "plonky3_bb31_poseidon2_w16_r8_lenpad"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "dlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %statement = pir.bind %t0 "statement" : "tg" stage instance
  %t2, %commitment = pir.slot %t1 "commitment" : "tg" in "sigma" as "a"
  %t3, %challenge = pir.chal %t2 deps(%statement, %commitment : !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "fixture.ext4.challenge" space "16428751811598850197311699254593454081"
  %t4, %response = pir.slot %t3 "response" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %evaluation = pir.reduce "sigma" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%challenge : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %statement to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
