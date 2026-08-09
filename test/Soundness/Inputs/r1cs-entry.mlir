// The first end-to-end story from a compiled circuit to a bound.  The
// application relation enters as digests -- the constraint matrices and the
// public input -- and zkc never reads inside them: the entry claim's anchors
// are its author's declaration, which is the membrane, and the batching step
// that consumes it is one ordinary reduction contract whose bound reads a
// declared constraint count.  The batched statement is a tagged construction
// over the entry anchors, so the downstream sumcheck is checked against
// exactly the relation instance the entry named.
pir.protocol "r1cs_entry" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "r1cs" anchors {a = "sha256:6f7a1f3cbca32bf858d859646653a2d98e391f519150223e3222da84dec07e8b", b = "sha256:abb35bd25c2c9ce6fd7fcc4fe346743fbdbf56b5c35bdd3284f385fd99a04107", c = "sha256:e8497146da914e320456166bd1f69a74ec8b59fd91e2d63e3a8d480fd004bc14", public = "sha256:8dc577d7ba6e39046ec3bf3b897bf13756b564cfa26d59637f9ede7e456a8b62"} : !pir.claim<"r1cs">
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "scalar" stage instance
  %t2, %cs = pir.bind %t1 "cs" : "scalar" stage instance
  %t3, %alpha = pir.chal %t2 deps(%x : !pir.val<"scalar">) "alpha" : "scalar" domain "r1cs.alpha" space "2305843009213693952"
  %t4, %g0 = pir.slot %t3 "g1_0" : "scalar" in "sc" as "g1"
  %t5, %g1 = pir.slot %t4 "g1_1" : "scalar" in "sc" as "g1" idx 1
  %t6, %g2 = pir.slot %t5 "g1_2" : "scalar" in "sc" as "g1" idx 2
  %t7, %c1 = pir.chal %t6 "c1" : "scalar" domain "r1cs.c1" space "2305843009213693952"
  %t8, %h0 = pir.slot %t7 "g2_0" : "scalar" in "sc" as "g2"
  %t9, %h1 = pir.slot %t8 "g2_1" : "scalar" in "sc" as "g2" idx 1
  %t10, %h2 = pir.slot %t9 "g2_2" : "scalar" in "sc" as "g2" idx 2
  %t11, %c2 = pir.chal %t10 "c2" : "scalar" domain "r1cs.c2" space "2305843009213693952"
  pir.check "sc_round1" contract "zkc.check.sumcheck-round1" (%cs, %g0, %g1, %g2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["f_add", ["f_add", ["in", 1], ["in", 1]], ["in", 2]], ["in", 3]], ["in", 0]]
  pir.check "sc_round2" contract "zkc.check.sumcheck-round2" (%g0, %g1, %g2, %c1, %h0, %h1, %h2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["f_add", ["f_add", ["in", 4], ["in", 4]], ["in", 5]], ["in", 6]], ["f_add", ["in", 0], ["f_add", ["f_mul", ["in", 1], ["in", 3]], ["f_mul", ["in", 2], ["f_mul", ["in", 3], ["in", 3]]]]]]
  pir.check "sc_final" contract "zkc.check.sumcheck-final" (%h0, %h1, %h2, %c1, %c2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["in", 0], ["f_add", ["f_mul", ["in", 1], ["in", 4]], ["f_mul", ["in", 2], ["f_mul", ["in", 4], ["in", 4]]]]], ["f_add", ["f_mul", ["in", 3], ["in", 4]], ["in", 3]]]
  pir.end %t11
  %batched = pir.reduce "batch" contract "r1cs_batch" (%relation : !pir.claim<"r1cs">) deps(%alpha : !pir.val<"scalar">) checks {} anchors [{statement = "sha256:22bd47561342f95835c1f1808f592f43ceb5b691458c89fbb3f3380c9d88205c"}] -> !pir.claim<"r1cs_batched_sum">
  %evaluation = pir.reduce "sc" contract "r1cs_sumcheck" (%batched : !pir.claim<"r1cs_batched_sum">) deps(%c1, %c2 : !pir.val<"scalar">, !pir.val<"scalar">) checks {final = "sc_final", round1 = "sc_round1", round2 = "sc_round2"} anchors [{statement = "sha256:22bd47561342f95835c1f1808f592f43ceb5b691458c89fbb3f3380c9d88205c"}] -> !pir.claim<"sumcheck_evaluation">
  pir.material_bind %cs to "sha256:22bd47561342f95835c1f1808f592f43ceb5b691458c89fbb3f3380c9d88205c" : !pir.val<"scalar">
  pir.residual %evaluation : !pir.claim<"sumcheck_evaluation"> route "r1cs-terminal-not-modeled"
}
