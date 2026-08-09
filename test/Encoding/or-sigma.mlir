// REQUIRES: uv
// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: zkc-translate --canonical %t.sealed -o %t.zkc
// RUN: %uv python -m oracle.parity encode or-sigma > %t.oracle
// RUN: diff %t.zkc %t.oracle
// RUN: zkc-translate --id %t.sealed -o %t.zkc-id
// RUN: %uv python -m oracle.parity id or-sigma > %t.oracle-id
// RUN: diff %t.zkc-id %t.oracle-id
// RUN: zkc-opt %pir-seal-full %pir-project-full %s -o %t.projected
// RUN: zkc-translate --oir-canonical %t.projected -o %t.oir.zkc
// RUN: %uv python -m oracle.parity oir-encode or-sigma > %t.oir.oracle
// RUN: diff %t.oir.zkc %t.oir.oracle
// RUN: zkc-translate --oir-id %t.projected -o %t.oir-id.zkc
// RUN: %uv python -m oracle.parity oir-id or-sigma > %t.oir-id.oracle
// RUN: diff %t.oir-id.zkc %t.oir-id.oracle
// RUN: rm -rf %t.artifacts
// RUN: zkc-seal %s %zkc-seal-full -o %t.artifacts

// Twin of reference/oracle/witnesses.py's OR_SIGMA witness: the CDS94
// OR-composition (proofs of partial knowledge; Damgaard Sec. 4 Thm 2)
// on the two-commitment shape. The boundary this fixture stress-tests:
// ONE kernel challenge c is squeezed; the shares c1, c2 and the
// per-branch responses are PROVER-DERIVED PROOF VALUES — modeled as
// proof-stream slots, never kernel challenges, so BIND demands
// nothing of them. Their entire binding to c is the transparent
// split check c1 + c2 = c (CDS94's 2-out-of-2 sharing, spelled
// additively mod q): without it the prover simulates both branches
// and never uses c at all — the exec twin's ignored_challenge vector
// is exactly that forgery, caught by the split check alone.
//
// The soundness arithmetic these protocols carry had a reporting
// consumer that no longer ships, so the assertions that named its
// output are gone rather than left looking like evidence. What this
// file still proves is byte parity of the encoding and identity
// against the reference twin, which is what its RUN lines do.
//
pir.protocol "or_sigma" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %c = pir.instantiate "ordlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:d75c7df03827613507aa3c5c4d52e05892b7b27a49fc7b1855bb9dbdc398df59"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y1 = pir.bind %t0 "y1" : "tg" stage instance
  %t2, %y2 = pir.bind %t1 "y2" : "tg" stage instance
  %t3, %a1 = pir.slot %t2 "commit_A1" : "tg" in "or" as "a"
  %t4, %a2 = pir.slot %t3 "commit_A2" : "tg" in "or" as "a" idx 1
  %t5, %ch = pir.chal %t4 deps(%y1, %y2, %a1, %a2 : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "or.c" space "2305843009213693952"
  // Prover-derived challenge shares and per-branch responses: proof
  // material, not challenges.
  %t6, %c1 = pir.slot %t5 "share_c1" : "scalar"
  %t7, %c2 = pir.slot %t6 "share_c2" : "scalar"
  %t8, %z1 = pir.slot %t7 "resp_z1" : "scalar"
  %t9, %z2 = pir.slot %t8 "resp_z2" : "scalar"
  // g^z1 = A1 * y1^c1.
  pir.check "verify1" contract "zkc.check.sigma-equation-scalar-challenge" (%y1, %a1, %c1, %z1 : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  // g^z2 = A2 * y2^c2.
  pir.check "verify2" contract "zkc.check.sigma-equation-scalar-challenge" (%y2, %a2, %c2, %z2 : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  // The CDS94 split: c1 + c2 = c binds the shares to the challenge.
  pir.check "split" contract "zkc.check.scalar-split" (%c1, %c2, %ch : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["in", 0], ["in", 1]], ["in", 2]]
  pir.end %t9
  %e = pir.reduce "or" contract "sigma_or" (%c : !pir.claim<"opaque_relation">) deps(%ch, %c1, %c2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) checks {challenge_split = "split", left_equation = "verify1", right_equation = "verify2"} params {left_statement = "sha256:c819b8b37daea1fa96171a0bc9189e2e95b70be9d37f8ae4a30650baff1fd280", right_statement = "sha256:4d2368520d64ee7a23a1bd2f9e0958063b223eda6ec5bb2619f134bec184bd16"} anchors [{statement = "sha256:d75c7df03827613507aa3c5c4d52e05892b7b27a49fc7b1855bb9dbdc398df59"}] -> !pir.claim<"or_evaluation">
  pir.material_bind %y1 to "sha256:c819b8b37daea1fa96171a0bc9189e2e95b70be9d37f8ae4a30650baff1fd280" : !pir.val<"tg">
  pir.material_bind %y2 to "sha256:4d2368520d64ee7a23a1bd2f9e0958063b223eda6ec5bb2619f134bec184bd16" : !pir.val<"tg">
  pir.residual %e : !pir.claim<"or_evaluation"> route "or-terminal-not-modeled"
}
