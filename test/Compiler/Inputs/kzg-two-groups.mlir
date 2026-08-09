// Four independently discharged KZG openings at two distinct points.  Each
// point has one maximal two-opening batch group.

pir.protocol "kzg_two_groups" kappa {codecs = {fr = "fr_be32", g1 = "bls_g1_be48"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %a1 = pir.instantiate "a1" anchors {commitment = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", point = "sha256:1111111111111111111111111111111111111111111111111111111111111111", value = "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"} : !pir.claim<"single_opening">
  %a2 = pir.instantiate "a2" anchors {commitment = "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb", point = "sha256:1111111111111111111111111111111111111111111111111111111111111111", value = "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"} : !pir.claim<"single_opening">
  %b1 = pir.instantiate "b1" anchors {commitment = "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc", point = "sha256:2222222222222222222222222222222222222222222222222222222222222222", value = "sha256:0000000000000000000000000000000000000000000000000000000000000000"} : !pir.claim<"single_opening">
  %b2 = pir.instantiate "b2" anchors {commitment = "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd", point = "sha256:2222222222222222222222222222222222222222222222222222222222222222", value = "sha256:9999999999999999999999999999999999999999999999999999999999999999"} : !pir.claim<"single_opening">
  %t0 = pir.begin
  %t1, %c1 = pir.bind %t0 "C1" : "g1" stage instance
  %t2, %c2 = pir.bind %t1 "C2" : "g1" stage instance
  %t3, %c3 = pir.bind %t2 "C3" : "g1" stage instance
  %t4, %c4 = pir.bind %t3 "C4" : "g1" stage instance
  %t5, %z1 = pir.bind %t4 "z1" : "fr" stage instance
  %t6, %z2 = pir.bind %t5 "z2" : "fr" stage instance
  %t7, %v1 = pir.bind %t6 "v1" : "fr" stage instance
  %t8, %v2 = pir.bind %t7 "v2" : "fr" stage instance
  %t9, %v3 = pir.bind %t8 "v3" : "fr" stage instance
  %t10, %v4 = pir.bind %t9 "v4" : "fr" stage instance
  %t11, %w1 = pir.slot %t10 "W1" : "g1"
  %t12, %w2 = pir.slot %t11 "W2" : "g1"
  %t13, %w3 = pir.slot %t12 "W3" : "g1"
  %t14, %w4 = pir.slot %t13 "W4" : "g1"
  pir.check "a1_ok" contract "zkc.check.kzg-opening" params {suite = "bls12-381"} (%c1, %z1, %v1, %w1 : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)
  pir.check "a2_ok" contract "zkc.check.kzg-opening" params {suite = "bls12-381"} (%c2, %z1, %v2, %w2 : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)
  pir.check "b1_ok" contract "zkc.check.kzg-opening" params {suite = "bls12-381"} (%c3, %z2, %v3, %w3 : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)
  pir.check "b2_ok" contract "zkc.check.kzg-opening" params {suite = "bls12-381"} (%c4, %z2, %v4, %w4 : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)
  pir.end %t14
  pir.material_bind %c1 to "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" : !pir.val<"g1">
  pir.material_bind %c2 to "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" : !pir.val<"g1">
  pir.material_bind %c3 to "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc" : !pir.val<"g1">
  pir.material_bind %c4 to "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd" : !pir.val<"g1">
  pir.material_bind %z1 to "sha256:1111111111111111111111111111111111111111111111111111111111111111" : !pir.val<"fr">
  pir.material_bind %z2 to "sha256:2222222222222222222222222222222222222222222222222222222222222222" : !pir.val<"fr">
  pir.material_bind %v1 to "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee" : !pir.val<"fr">
  pir.material_bind %v2 to "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" : !pir.val<"fr">
  pir.material_bind %v3 to "sha256:0000000000000000000000000000000000000000000000000000000000000000" : !pir.val<"fr">
  pir.material_bind %v4 to "sha256:9999999999999999999999999999999999999999999999999999999999999999" : !pir.val<"fr">
  pir.discharge %a1 : !pir.claim<"single_opening"> rule "zkc.terminal.kzg-opening" checks {opening = "a1_ok"}
  pir.discharge %a2 : !pir.claim<"single_opening"> rule "zkc.terminal.kzg-opening" checks {opening = "a2_ok"}
  pir.discharge %b1 : !pir.claim<"single_opening"> rule "zkc.terminal.kzg-opening" checks {opening = "b1_ok"}
  pir.discharge %b2 : !pir.claim<"single_opening"> rule "zkc.terminal.kzg-opening" checks {opening = "b2_ok"}
}
