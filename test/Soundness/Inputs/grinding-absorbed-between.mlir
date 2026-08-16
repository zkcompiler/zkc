// The grinding spine with one absorbed prover message between the pow
// challenge and the challenge the grinding factor protects.  It is the
// generated frigrind spine with a single slot injected; it seals, because
// seal is structural and this is a well-formed protocol -- what it is not is
// a protocol whose query round has earned 2^-z, since varying the injected
// message redraws the query challenge from a different sponge state at no
// cost.  The derivation must refuse rather than price it.
pir.protocol "frigrind" kappa {codecs = {query_index = "ts_be8", rs = "ts_be8", ext_field = "ts_be8", pow_value = "ts_be8"}, constants = {zero = {class = "pow_value", value = "0"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %c = pir.instantiate "prox" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %f = pir.bind %t0 "f_root" : "rs" stage instance
  %t2, %fold1 = pir.chal %t1 deps(%f : !pir.val<"rs">) "fold" : "ext_field" domain "fri.fold" space "340282366762482138490186164457219031041"
  %t3, %g1 = pir.slot %t2 "g_root" : "rs" in "frij" as "g"
  %t4, %nonce = pir.slot %t3 "nonce" : "rs" in "grind" as "nonce"
  %t5, %pow = pir.chal %t4 deps(%nonce : !pir.val<"rs">) "pow" : "pow_value" domain "grind.pow" space "65536"
  pir.check "pow_pin" contract "zkc.check.pow-zero" (%nonce, %pow : !pir.val<"rs">, !pir.val<"pow_value">) expr ["eq", ["in", 1], ["const", "zero"]]
  %t5b, %extra = pir.slot %t5 "extra" : "rs"
  %t6, %query = pir.chal %t5b deps(%g1 : !pir.val<"rs">) "query" : "query_index" domain "fri.query" space "1024" mode ["vector", "2", "uniform_independent"]
  pir.check "consistency" contract "zkc.check.rs-equality" (%f, %g1 : !pir.val<"rs">, !pir.val<"rs">) expr ["eq", ["in", 0], ["in", 1]]
  pir.end %t6
  %e = pir.reduce "frij" contract "fri" (%c : !pir.claim<"opaque_relation">) deps(%fold1, %query : !pir.val<"ext_field">, !pir.val<"query_index">) checks {consistency = "consistency"} params {johnson_m = "3", johnson_eta = "1/256", johnson_delta = "9/10", log_blowup = "9", log_final_poly_len = "0"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"fri_query_consistent">
  %s = pir.reduce "grind" contract "grinding" (%e : !pir.claim<"fri_query_consistent">) deps(%pow : !pir.val<"pow_value">) checks {pow_pin = "pow_pin"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"fri_query_consistent">
  pir.material_bind %f to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"rs">
  pir.residual %s : !pir.claim<"fri_query_consistent"> route "fri-terminal-not-modeled"
}
