// Schnorr again, but its commit is routed through a contract that declares a
// static parameter and a semantic one. Everything else is the sealed routed
// protocol as it stands; the parameters are the subject.
//
// `mode` is an ordinary instance value. `reference_string` is a content
// reference: it names material the supplier is expected to hold, and it is the
// binding that has to survive projection, admission, and the supplier call for
// an endpoint to be executable away from the protocol that produced it.

pir.protocol "parameterized_schnorr" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} routes {instances = {commit = {contract = "zkc.hole.parameterized-commit", inputs = ["const:g", "witness:w"], params = {mode = "batched", reference_string = "sha256:2c26b46b68ffc68ff99b453c1d30413413422d706483bfa0f98a5e886266e7ae"}}, resp = {contract = "zkc.hole.sigma-response", inputs = ["chal:c", "commit.1"]}}, witnesses = [["w", "sigma-witness"]]} {
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
