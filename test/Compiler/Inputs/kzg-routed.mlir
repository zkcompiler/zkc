// KZG batching source carrying an independent, partially routed construction
// graph.  The compiler transform must preserve and reseal this graph even
// though the current KZG proof slots are not supplied by it.
pir.protocol "kzg_before_routed"
    kappa {codecs = {fr = "fr_be32", g1 = "bls_g1_be48"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {aux.commit = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}}, witnesses = [["w", "sigma-witness"]]} {
  %o1 = pir.instantiate "open1" anchors {commitment = "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64", value = "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379"} : !pir.claim<"single_opening">
  %o2 = pir.instantiate "open2" anchors {commitment = "sha256:75136a554c8ccd7a0780bbe87fb34ae8ef8d34eefb2509bc719f7b3160a3244b", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64", value = "sha256:308efab7d1ff27bcb8edb1d1ec89290f26621e6372fa7708f6fe5fda83ad45ba"} : !pir.claim<"single_opening">
  %t0 = pir.begin
  %t1, %c1 = pir.bind %t0 "C1" : "g1" stage instance
  %t2, %c2 = pir.bind %t1 "C2" : "g1" stage instance
  %t3, %z = pir.bind %t2 "z" : "fr" stage instance
  %t4, %v1 = pir.bind %t3 "v1" : "fr" stage instance
  %t5, %v2 = pir.bind %t4 "v2" : "fr" stage instance
  %t6, %w1 = pir.slot %t5 "W1" : "g1"
  %t7, %w2 = pir.slot %t6 "W2" : "g1"
  pir.check "open1_ok" contract "zkc.check.kzg-opening" params {suite = "bls12-381"} (%c1, %z, %v1, %w1 : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)
  pir.check "open2_ok" contract "zkc.check.kzg-opening" params {suite = "bls12-381"} (%c2, %z, %v2, %w2 : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)
  pir.end %t7
  pir.material_bind %c1 to "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4" : !pir.val<"g1">
  pir.material_bind %c2 to "sha256:75136a554c8ccd7a0780bbe87fb34ae8ef8d34eefb2509bc719f7b3160a3244b" : !pir.val<"g1">
  pir.material_bind %z to "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64" : !pir.val<"fr">
  pir.material_bind %v1 to "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379" : !pir.val<"fr">
  pir.material_bind %v2 to "sha256:308efab7d1ff27bcb8edb1d1ec89290f26621e6372fa7708f6fe5fda83ad45ba" : !pir.val<"fr">
  pir.discharge %o1 : !pir.claim<"single_opening"> rule "zkc.terminal.kzg-opening" checks {opening = "open1_ok"}
  pir.discharge %o2 : !pir.claim<"single_opening"> rule "zkc.terminal.kzg-opening" checks {opening = "open2_ok"}
}
