pir.protocol "opening_material_mismatch" kappa {codecs = {fr = "fr_be32", g1 = "bls_g1_be48"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %opening = pir.instantiate "opening" anchors {commitment = "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64", value = "sha256:4fbaa40d86f7755e1661aef783bd9f936c7e482111f15c0ac7fa826f7f83e7d6"} : !pir.claim<"single_opening">
  %t0 = pir.begin
  %t1, %commitment = pir.bind %t0 "commitment" : "g1" stage instance
  %t2, %point = pir.bind %t1 "point" : "fr" stage instance
  %t3, %value = pir.bind %t2 "value" : "fr" stage instance
  %t4, %proof = pir.slot %t3 "proof" : "g1"
  pir.check "opening_check" contract "zkc.check.kzg-opening" params {suite = "bls12-381"} (%commitment, %point, %value, %proof : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)
  pir.end %t4
  pir.material_bind %commitment to "sha256:9999999999999999999999999999999999999999999999999999999999999999" : !pir.val<"g1">
  pir.material_bind %point to "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64" : !pir.val<"fr">
  pir.material_bind %value to "sha256:4fbaa40d86f7755e1661aef783bd9f936c7e482111f15c0ac7fa826f7f83e7d6" : !pir.val<"fr">
  pir.discharge %opening : !pir.claim<"single_opening"> rule "zkc.terminal.kzg-opening" checks {opening = "opening_check"}
}
