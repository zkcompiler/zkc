// REQUIRES: uv
// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: zkc-translate --canonical %t.sealed -o %t.zkc
// RUN: %uv python -m oracle.parity encode chaum-pedersen > %t.oracle
// RUN: diff %t.zkc %t.oracle
// RUN: zkc-translate --id %t.sealed -o %t.zkc-id
// RUN: %uv python -m oracle.parity id chaum-pedersen > %t.oracle-id
// RUN: diff %t.zkc-id %t.oracle-id
// RUN: zkc-opt %pir-seal-full %pir-project-full %s -o %t.projected
// RUN: zkc-translate --oir-canonical %t.projected -o %t.oir.zkc
// RUN: %uv python -m oracle.parity oir-encode chaum-pedersen > %t.oir.oracle
// RUN: diff %t.oir.zkc %t.oir.oracle
// RUN: zkc-translate --oir-id %t.projected -o %t.oir-id.zkc
// RUN: %uv python -m oracle.parity oir-id chaum-pedersen > %t.oir-id.oracle
// RUN: diff %t.oir-id.zkc %t.oir-id.oracle
// RUN: rm -rf %t.artifacts
// RUN: zkc-seal %s %zkc-seal-full -o %t.artifacts

// Twin of reference/oracle/witnesses.py's CHAUM_PEDERSEN witness: the
// equality-of-discrete-logs sigma protocol (Damgaard Sec. 5 Exercise
// 1; Chaum-Pedersen CRYPTO '92) on the two-commitment DLEQ shape
// — two commitments A1 = g^r, A2 = h^r under ONE nonce, one
// challenge, one response z checked against both group equations, so
// the two checks bind a single exponent across both statement legs.
// Priced through the special-soundness entry (k = 2 with a shared
// commitment prefix) and the BGTZ SS => RBR edge to the FS soundness
// conclusion; executed by test/Oir/chaum-pedersen-exec.test.
//
// The soundness arithmetic these protocols carry had a reporting
// consumer that no longer ships, so the assertions that named its
// output are gone rather than left looking like evidence. What this
// file still proves is byte parity of the encoding and identity
// against the reference twin, which is what its RUN lines do.
//
pir.protocol "chaum_pedersen" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}, h = {class = "tg", value = "2077728439817762110"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %c = pir.instantiate "dleq" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:bba3f50128ba9db12704c2e35ac7966e21b9105c3c0b8a0ba0bfa83bdc02e18e"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y1 = pir.bind %t0 "y1" : "tg" stage instance
  %t2, %y2 = pir.bind %t1 "y2" : "tg" stage instance
  %t3, %a1 = pir.slot %t2 "commit_A1" : "tg" in "cp" as "a"
  %t4, %a2 = pir.slot %t3 "commit_A2" : "tg" in "cp" as "a" idx 1
  %t5, %ch = pir.chal %t4 deps(%y1, %y2, %a1, %a2 : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "cp.c" space "2305843009213693952"
  %t6, %z = pir.slot %t5 "resp_z" : "scalar"
  // g^z = A1 * y1^c.
  pir.check "verify1" contract "zkc.check.schnorr-equation" (%y1, %a1, %ch, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  // h^z = A2 * y2^c.
  pir.check "verify2" contract "zkc.check.schnorr-equation" (%y2, %a2, %ch, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "h"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t6
  %e = pir.reduce "cp" contract "sigma_dleq" (%c : !pir.claim<"opaque_relation">) deps(%ch, %z : !pir.val<"scalar">, !pir.val<"scalar">) checks {left_equation = "verify1", right_equation = "verify2"} params {left_statement = "sha256:9b6cefd1e5cc69489e2d7f3c535e4685ce72a3127a7204cf80b8f5584c46b6e5", right_statement = "sha256:f9e684572cd9cab72656f35172689132378428b721c9da103116e814e9effb6a"} anchors [{statement = "sha256:bba3f50128ba9db12704c2e35ac7966e21b9105c3c0b8a0ba0bfa83bdc02e18e"}] -> !pir.claim<"dleq_evaluation">
  pir.material_bind %y1 to "sha256:9b6cefd1e5cc69489e2d7f3c535e4685ce72a3127a7204cf80b8f5584c46b6e5" : !pir.val<"tg">
  pir.material_bind %y2 to "sha256:f9e684572cd9cab72656f35172689132378428b721c9da103116e814e9effb6a" : !pir.val<"tg">
  pir.residual %e : !pir.claim<"dleq_evaluation"> route "dleq-terminal-not-modeled"
}
