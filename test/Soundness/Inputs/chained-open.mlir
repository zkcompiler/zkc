// The mid-chain shape the claim-coverage judgment exists for: a sumcheck whose
// output evaluation claim is consumed by an opening reduction, beside an
// independent opening whose consumed claim is an artifact source.  One
// binding, two occurrences, opposite verdicts.  The body is protocol "a" of
// test/Encoding/chained.mlir unchanged, so the sealed identity here is that
// test's identity.
pir.protocol "a" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "sum" anchors {contract = "sha256:8b53639f152c8fc6ef30802fde462ba0be9cf085f7580dc69efd72e002abbb35", statement = "sha256:e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc"} : !pir.claim<"opaque_relation">
  %aux = pir.instantiate "aux" anchors {statement = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"} : !pir.claim<"sumcheck_evaluation">
  %t0 = pir.begin
  %ts, %s = pir.bind %t0 "s" : "scalar" stage instance
  %t1, %g0 = pir.slot %ts "g1_0" : "scalar" in "sc" as "g1"
  %t2, %g1 = pir.slot %t1 "g1_1" : "scalar" in "sc" as "g1" idx 1
  %t3, %g2 = pir.slot %t2 "g1_2" : "scalar" in "sc" as "g1" idx 2
  %t4, %c1 = pir.chal %t3 "c1" : "scalar" domain "p.c1" space "2305843009213693952"
  %t5, %h0 = pir.slot %t4 "g2_0" : "scalar" in "sc" as "g2"
  %t6, %h1 = pir.slot %t5 "g2_1" : "scalar" in "sc" as "g2" idx 1
  %t7, %h2 = pir.slot %t6 "g2_2" : "scalar" in "sc" as "g2" idx 2
  %t8, %c2 = pir.chal %t7 "c2" : "scalar" domain "p.c2" space "2305843009213693952"
  %t9, %m0 = pir.slot %t8 "m0" : "scalar" in "op" as "m"
  %t10, %m0b = pir.slot %t9 "m0b" : "scalar" in "op" as "m" idx 1
  %t11, %c3 = pir.chal %t10 "c3" : "scalar" domain "p.c3" space "2305843009213693952"
  %t12, %m1 = pir.slot %t11 "m1" : "scalar" in "ind" as "m"
  %t13, %m1b = pir.slot %t12 "m1b" : "scalar" in "ind" as "m" idx 1
  %t14, %c4 = pir.chal %t13 "c4" : "scalar" domain "p.c4" space "2305843009213693952"
  pir.check "sc_round1" contract "zkc.check.sumcheck-round1" (%s, %g0, %g1, %g2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["f_add", ["f_add", ["in", 1], ["in", 1]], ["in", 2]], ["in", 3]], ["in", 0]]
  pir.check "sc_round2" contract "zkc.check.sumcheck-round2" (%g0, %g1, %g2, %c1, %h0, %h1, %h2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["f_add", ["f_add", ["in", 4], ["in", 4]], ["in", 5]], ["in", 6]], ["f_add", ["in", 0], ["f_add", ["f_mul", ["in", 1], ["in", 3]], ["f_mul", ["in", 2], ["f_mul", ["in", 3], ["in", 3]]]]]]
  pir.check "sc_final" contract "zkc.check.sumcheck-final" (%h0, %h1, %h2, %c1, %c2 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["f_add", ["in", 0], ["f_add", ["f_mul", ["in", 1], ["in", 4]], ["f_mul", ["in", 2], ["f_mul", ["in", 4], ["in", 4]]]]], ["f_add", ["f_mul", ["in", 3], ["in", 4]], ["in", 3]]]
  pir.end %t14
  // Authored order: dependent chain first, independent reduction last.
  %evaluation = pir.reduce "sc" contract "sumcheck" (%relation : !pir.claim<"opaque_relation">) deps(%c1, %c2 : !pir.val<"scalar">, !pir.val<"scalar">) checks {final = "sc_final", round1 = "sc_round1", round2 = "sc_round2"} anchors [{statement = "sha256:e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc"}] -> !pir.claim<"sumcheck_evaluation">
  %opening = pir.reduce "op" contract "evalopen" (%evaluation : !pir.claim<"sumcheck_evaluation">) deps(%c3 : !pir.val<"scalar">) checks {} anchors [{commitment = "sha256:50feaa7e90906c60034b0db9b872015920f52bf543de7873fd102adbae1b9a7f", point = "sha256:7ebb83c8fe1e5617c803993577102fa4d4b76a851fd855a2a25282ca680923ac", value = "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379"}] -> !pir.claim<"single_opening">
  %independent = pir.reduce "ind" contract "evalopen" (%aux : !pir.claim<"sumcheck_evaluation">) deps(%c4 : !pir.val<"scalar">) checks {} anchors [{commitment = "sha256:65b60629324703b7d7f6fea1362d18f78b3c1c865a8e890003477de2a8480f43", point = "sha256:085712992bf36d0c86e3e8654f555f12fd6cb4b39c1692daddb5b7b82f14e11f", value = "sha256:308efab7d1ff27bcb8edb1d1ec89290f26621e6372fa7708f6fe5fda83ad45ba"}] -> !pir.claim<"single_opening">
  pir.material_bind %s to "sha256:e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc" : !pir.val<"scalar">
  pir.material_bind %m0 to "sha256:50feaa7e90906c60034b0db9b872015920f52bf543de7873fd102adbae1b9a7f" : !pir.val<"scalar">
  pir.material_bind %m0b to "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379" : !pir.val<"scalar">
  pir.material_bind %c3 to "sha256:7ebb83c8fe1e5617c803993577102fa4d4b76a851fd855a2a25282ca680923ac" : !pir.val<"scalar">
  pir.material_bind %m1 to "sha256:65b60629324703b7d7f6fea1362d18f78b3c1c865a8e890003477de2a8480f43" : !pir.val<"scalar">
  pir.material_bind %m1b to "sha256:308efab7d1ff27bcb8edb1d1ec89290f26621e6372fa7708f6fe5fda83ad45ba" : !pir.val<"scalar">
  pir.material_bind %c4 to "sha256:085712992bf36d0c86e3e8654f555f12fd6cb4b39c1692daddb5b7b82f14e11f" : !pir.val<"scalar">
  pir.residual %opening : !pir.claim<"single_opening"> route "evalopen-terminal-not-modeled"
  pir.residual %independent : !pir.claim<"single_opening"> route "evalopen-terminal-not-modeled"
}
