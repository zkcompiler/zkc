// RUN: zkc-opt '-pir-link=producer=prod consumer=cons %pir-link-authorities' %pir-seal-full %s | FileCheck %s
//
// Link composes claim flow, not merely two transcript lists.  The exported
// opening and the consumer source have one exact descriptor and therefore
// fuse. Stable material references stay attached to the consumer values, and
// terminal closure remains the admitted KZG rule. The segment boundary keeps
// the per-face structural statement-binding check valid when consumer bindings
// follow a producer challenge; it makes no fs_segment_seam soundness claim.

// CHECK: pir.sealed "prod"
// CHECK: pir.sealed "cons"
// CHECK: pir.sealed "link(prod,cons)"
// CHECK-SAME: segments [2]
// CHECK: pir.instantiate "left.opening" anchors
// CHECK-NOT: pir.instantiate "right.opening"
// CHECK: domain "left.producer.challenge"
// CHECK: domain "right.consumer.challenge"
// CHECK: pir.check "right.opening_check" contract "zkc.check.kzg-opening"
// CHECK: pir.material_bind {{.*}} to "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4"
// CHECK: pir.material_bind {{.*}} to "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64"
// CHECK: pir.material_bind {{.*}} to "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379"
// CHECK: pir.discharge {{.*}} : <"single_opening"> rule "zkc.terminal.kzg-opening" checks {opening = "right.opening_check"}

pir.protocol "prod" kappa {codecs = {fr = "fr_be32", g1 = "bls_g1_be48"}, iv = "artifact-id", sponge = "toy_duplex"} policy "host_exporting_artifact" {
  %opening = pir.instantiate "opening" anchors {commitment = "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64", value = "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379"} : !pir.claim<"single_opening">
  %t0 = pir.begin
  %t1, %context = pir.bind %t0 "context" : "g1" stage instance
  %t2, %challenge = pir.chal %t1 deps(%context : !pir.val<"g1">) "challenge" : "fr" domain "producer.challenge" space "52435875175126190479447740508185965837690552500527637822603658699938581184513"
  pir.end %t2
  pir.export %opening : !pir.claim<"single_opening"> route "to.consumer"
}

pir.protocol "cons" kappa {codecs = {fr = "fr_be32", g1 = "bls_g1_be48"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %opening = pir.instantiate "opening" anchors {commitment = "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64", value = "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379"} : !pir.claim<"single_opening">
  %t0 = pir.begin
  %t1, %commitment = pir.bind %t0 "commitment" : "g1" stage instance
  %t2, %point = pir.bind %t1 "point" : "fr" stage instance
  %t3, %value = pir.bind %t2 "value" : "fr" stage instance
  %t4, %challenge = pir.chal %t3 deps(%commitment, %point, %value : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">) "challenge" : "fr" domain "consumer.challenge" space "52435875175126190479447740508185965837690552500527637822603658699938581184513"
  %t5, %proof = pir.slot %t4 "proof" : "g1"
  pir.check "opening_check" contract "zkc.check.kzg-opening" params {suite = "kzg-bls12-381"} (%commitment, %point, %value, %proof : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)
  pir.end %t5
  pir.material_bind %commitment to "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4" : !pir.val<"g1">
  pir.material_bind %point to "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64" : !pir.val<"fr">
  pir.material_bind %value to "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379" : !pir.val<"fr">
  pir.discharge %opening : !pir.claim<"single_opening"> rule "zkc.terminal.kzg-opening" checks {opening = "opening_check"}
}
