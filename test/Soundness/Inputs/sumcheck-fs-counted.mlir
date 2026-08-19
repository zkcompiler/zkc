// A Fiat-Shamir artifact whose bias terms are nonzero, and whose one biased
// challenge is a counted vector.
//
// The adapter multiplies a challenge's per-draw statistical distance by its
// vector count, and until this fixture no configuration in the tree could
// observe that factor: every counted challenge the families emit samples a
// power-of-two space out of a power-of-two squeeze domain, where the distance
// is zero, and every biased challenge elsewhere is scalar. A wrong factor
// there priced every future counted squeeze and no test would have moved.
//
// The added challenge samples 7 values three times through an eight-symbol
// squeeze framing 2^64. It belongs to no reduction, which is deliberate on
// both counts: the codec-bias facts are artifact-global, so the sum sees it
// without any rule owning it, and the artifact judgment then says so -- the
// two accountings disagree about scope on purpose, and the disagreement is
// visible here rather than left to a reader.

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
  %t10, %spread = pir.chal %t9 "spread" : "scalar" domain "aux.spread" space "7" mode ["vector", "3", "uniform_independent"]
  pir.end %t10
  %e = pir.reduce "sc" contract "sumcheck" (%c : !pir.claim<"opaque_relation">) deps(%c1, %c2 : !pir.val<"scalar">, !pir.val<"scalar">) checks {final = "final", round1 = "round1", round2 = "round2"} anchors [{statement = "sha256:aea20ace0f8efd6c86b7088db29b833b872fe0a1403d84a9046e2b1d4ed1412b"}] -> !pir.claim<"sumcheck_evaluation">
  pir.material_bind %s to "sha256:aea20ace0f8efd6c86b7088db29b833b872fe0a1403d84a9046e2b1d4ed1412b" : !pir.val<"scalar">
  pir.residual %e : !pir.claim<"sumcheck_evaluation"> route "sumcheck-terminal-not-modeled"
}
