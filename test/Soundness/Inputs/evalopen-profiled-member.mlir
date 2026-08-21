// An evaluation-opening protocol whose round messages are commitments.
//
// Driven by logup-range-check.test. `zkc.side.field_class` establishes that a
// round's messages are elements of the field the bound is priced over. A
// commitment stands for many of them, so it answers no however its profile is
// named — and this is the family where that condition is the only guard: its
// contract declares no check a commitment would fail at instead, so without
// the condition a profile named after a payload class would buy a 1/|F| bound
// for a round of commitments.
pir.protocol "interleaved" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %eva = pir.instantiate "eva" anchors {statement = "sha256:6c3aebe70e2969b448bcd2b7d38a34b7eebb1cae4b73d18b8f9d1b0693e2e6c9"} : !pir.claim<"sumcheck_evaluation">
  %evb = pir.instantiate "evb" anchors {statement = "sha256:2fca346db656187102ce806ac732e06a62df0dbb2829e511a770556d398e1a6e"} : !pir.claim<"sumcheck_evaluation">
  %t0 = pir.begin
  %t1, %ma0 = pir.slot %t0 "ma0" : profile "opening_commitment" in "opa" as "m"
  %t2, %mb0 = pir.slot %t1 "mb0" : profile "opening_commitment" in "opb" as "m"
  %t3, %ma1 = pir.slot %t2 "ma1" : profile "opening_commitment" in "opa" as "m" idx 1
  %t4, %mb1 = pir.slot %t3 "mb1" : profile "opening_commitment" in "opb" as "m" idx 1
  %t5, %ca = pir.chal %t4 "ca" : "scalar" domain "il.ca" space "2305843009213693952"
  %t6, %cb = pir.chal %t5 "cb" : "scalar" domain "il.cb" space "2305843009213693952"
  pir.end %t6
  %opa = pir.reduce "opa" contract "evalopen" (%eva : !pir.claim<"sumcheck_evaluation">) deps(%ca : !pir.val<"scalar">) checks {} anchors [{commitment = "sha256:50feaa7e90906c60034b0db9b872015920f52bf543de7873fd102adbae1b9a7f", point = "sha256:7ebb83c8fe1e5617c803993577102fa4d4b76a851fd855a2a25282ca680923ac", value = "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379"}] -> !pir.claim<"single_opening">
  %opb = pir.reduce "opb" contract "evalopen" (%evb : !pir.claim<"sumcheck_evaluation">) deps(%cb : !pir.val<"scalar">) checks {} anchors [{commitment = "sha256:65b60629324703b7d7f6fea1362d18f78b3c1c865a8e890003477de2a8480f43", point = "sha256:085712992bf36d0c86e3e8654f555f12fd6cb4b39c1692daddb5b7b82f14e11f", value = "sha256:308efab7d1ff27bcb8edb1d1ec89290f26621e6372fa7708f6fe5fda83ad45ba"}] -> !pir.claim<"single_opening">
  pir.material_bind %ma0 to "sha256:50feaa7e90906c60034b0db9b872015920f52bf543de7873fd102adbae1b9a7f" : !pir.val<profile "opening_commitment">
  pir.material_bind %ma1 to "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379" : !pir.val<profile "opening_commitment">
  pir.material_bind %ca to "sha256:7ebb83c8fe1e5617c803993577102fa4d4b76a851fd855a2a25282ca680923ac" : !pir.val<"scalar">
  pir.material_bind %mb0 to "sha256:65b60629324703b7d7f6fea1362d18f78b3c1c865a8e890003477de2a8480f43" : !pir.val<profile "opening_commitment">
  pir.material_bind %mb1 to "sha256:308efab7d1ff27bcb8edb1d1ec89290f26621e6372fa7708f6fe5fda83ad45ba" : !pir.val<profile "opening_commitment">
  pir.material_bind %cb to "sha256:085712992bf36d0c86e3e8654f555f12fd6cb4b39c1692daddb5b7b82f14e11f" : !pir.val<"scalar">
  pir.residual %opa : !pir.claim<"single_opening"> route "evalopen-terminal-not-modeled"
  pir.residual %opb : !pir.claim<"single_opening"> route "evalopen-terminal-not-modeled"
}
