// REQUIRES: uv
// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: zkc-translate --canonical %t.sealed -o %t.zkc
// RUN: %uv python -m oracle.parity encode sumcheck-fs > %t.oracle
// RUN: diff %t.zkc %t.oracle
// RUN: zkc-translate --id %t.sealed -o %t.zkc-id
// RUN: %uv python -m oracle.parity id sumcheck-fs > %t.oracle-id
// RUN: diff %t.zkc-id %t.oracle-id
// RUN: zkc-opt %pir-seal-full %pir-project-full %s -o %t.projected
// RUN: zkc-translate --oir-canonical %t.projected -o %t.oir.zkc
// RUN: %uv python -m oracle.parity oir-encode sumcheck-fs > %t.oir.oracle
// RUN: diff %t.oir.zkc %t.oir.oracle
// RUN: zkc-translate --oir-id %t.projected -o %t.oir-id.zkc
// RUN: %uv python -m oracle.parity oir-id sumcheck-fs > %t.oir-id.oracle
// RUN: diff %t.oir-id.zkc %t.oir-id.oracle
// RUN: rm -rf %t.artifacts
// RUN: zkc-seal %s %zkc-seal-full -o %t.artifacts

// The knowledge-track FS twin: the sumcheck body with the artifact-level hop
// citation. The parity lines pin the hop encoding
// (the vocabulary's hop_rows and profiles sections) byte-for-byte
// against the oracle; the dispatch lines exercise the straightline
// knowledge chain — ArkLib's RBR knowledge (kappa_i = d_i/|C_i|,
// straightline) through COS20's transcript-only SR extractor to
// Chiesa-Orru Thm 6.2's straightline FS clause. The challenge space
// is exactly 2^61, which the 8-byte toy squeeze covers with ZERO
// bias (2^64 mod 2^61 = 0), so the FS conclusion is the two clean
// monomials: kappa_rbr * t + 25/2^256 * t^2.
//
// The soundness arithmetic these protocols carry had a reporting
// consumer that no longer ships, so the assertions that named its
// output are gone rather than left looking like evidence. What this
// file still proves is byte parity of the encoding and identity
// against the reference twin, which is what its RUN lines do.
//
pir.protocol "sumcheck" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %c = pir.instantiate "sum" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:aea20ace0f8efd6c86b7088db29b833b872fe0a1403d84a9046e2b1d4ed1412b"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %s = pir.bind %t0 "s" : "scalar" stage instance
  %t2, %g10 = pir.slot %t1 "g1_0" : "scalar" in "sc" as "g1"
  %t3, %g11 = pir.slot %t2 "g1_1" : "scalar" in "sc" as "g1" idx 1
  %t4, %g12 = pir.slot %t3 "g1_2" : "scalar" in "sc" as "g1" idx 2
  // Round-1 consistency: g1(0) + g1(1) = s.
  pir.check "round1" contract "zkc.check.sumcheck-round1" (%s, %g10, %g11, %g12 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["f_add", ["f_add", ["in", 1], ["in", 1]], ["in", 2]], ["in", 3]], ["in", 0]]
  %t5, %c1 = pir.chal %t4 "c1" : "scalar" domain "sumcheck.c1" space "2305843009213693952"
  %t6, %g20 = pir.slot %t5 "g2_0" : "scalar" in "sc" as "g2"
  %t7, %g21 = pir.slot %t6 "g2_1" : "scalar" in "sc" as "g2" idx 1
  %t8, %g22 = pir.slot %t7 "g2_2" : "scalar" in "sc" as "g2" idx 2
  // Round-2 consistency: g2(0) + g2(1) = g1(c1).
  pir.check "round2" contract "zkc.check.sumcheck-round2" (%g10, %g11, %g12, %c1, %g20, %g21, %g22 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["f_add", ["f_add", ["in", 4], ["in", 4]], ["in", 5]], ["in", 6]], ["f_add", ["in", 0], ["f_add", ["f_mul", ["in", 1], ["in", 3]], ["f_mul", ["in", 2], ["f_mul", ["in", 3], ["in", 3]]]]]]
  %t9, %c2 = pir.chal %t8 "c2" : "scalar" domain "sumcheck.c2" space "2305843009213693952"
  // Final evaluation: g2(c2) = f(c1, c2).
  pir.check "final" contract "zkc.check.sumcheck-final" (%g20, %g21, %g22, %c1, %c2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["in", 0], ["f_add", ["f_mul", ["in", 1], ["in", 4]], ["f_mul", ["in", 2], ["f_mul", ["in", 4], ["in", 4]]]]], ["f_add", ["f_mul", ["in", 3], ["in", 4]], ["in", 3]]]
  pir.end %t9
  %e = pir.reduce "sc" contract "sumcheck" (%c : !pir.claim<"opaque_relation">) deps(%c1, %c2 : !pir.val<"scalar">, !pir.val<"scalar">) checks {final = "final", round1 = "round1", round2 = "round2"} anchors [{statement = "sha256:aea20ace0f8efd6c86b7088db29b833b872fe0a1403d84a9046e2b1d4ed1412b"}] -> !pir.claim<"sumcheck_evaluation">
  pir.material_bind %s to "sha256:aea20ace0f8efd6c86b7088db29b833b872fe0a1403d84a9046e2b1d4ed1412b" : !pir.val<"scalar">
  pir.residual %e : !pir.claim<"sumcheck_evaluation"> route "sumcheck-terminal-not-modeled"
}
