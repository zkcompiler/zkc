// RUN: zkc-opt '-pir-link=producer=prod consumer=cons %pir-link-authorities' %pir-seal-full %s | FileCheck %s
//
// A reduce-produced export fuses with the consumer's exact descriptor after
// the producer tail is cloned.  The consumer intentionally has no modeled
// terminal verifier for that claim, so analysis mode carries an explicit
// residual instead of a fabricated discharge.

// CHECK: pir.sealed "link(prod,cons)"
// CHECK-SAME: segments [8]
// CHECK: %[[BATCH:.+]] = pir.reduce "left.batch" contract "kzg_batch"
// CHECK-SAME: -> !pir.claim<"batch_opening">
// CHECK-NOT: pir.instantiate "right.batched"
// CHECK: pir.residual %[[BATCH]] : <"batch_opening"> route "batch-terminal-unmodeled"

pir.protocol "prod" kappa {codecs = {fr = "fr_be32", g1 = "bls_g1_be48"}, iv = "artifact-id", sponge = "toy_duplex"} policy "host_exporting_artifact" {
  %o1 = pir.instantiate "open1" anchors {commitment = "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64", value = "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379"} : !pir.claim<"single_opening">
  %o2 = pir.instantiate "open2" anchors {commitment = "sha256:75136a554c8ccd7a0780bbe87fb34ae8ef8d34eefb2509bc719f7b3160a3244b", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64", value = "sha256:308efab7d1ff27bcb8edb1d1ec89290f26621e6372fa7708f6fe5fda83ad45ba"} : !pir.claim<"single_opening">
  %t0 = pir.begin
  %t1, %c1 = pir.bind %t0 "C1" : "g1" stage instance
  %t2, %c2 = pir.bind %t1 "C2" : "g1" stage instance
  %t3, %z = pir.bind %t2 "z" : "fr" stage instance
  %t4, %v1 = pir.bind %t3 "v1" : "fr" stage instance
  %t5, %v2 = pir.bind %t4 "v2" : "fr" stage instance
  %t6, %gamma = pir.chal %t5 deps(%c1, %c2, %z, %v1, %v2 : !pir.val<"g1">, !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">) "gamma" : "fr" domain "batch_open.96642ac9a6b16028" space "52435875175126190479447740508185965837690552500527637822603658699938581184513"
  %t7, %w = pir.slot %t6 "W" : "g1"
  pir.check "batch_ok" contract "zkc.check.kzg-batch-opening" params {suite = "bls12-381"} (%c2, %c1, %z, %v2, %v1, %gamma, %w : !pir.val<"g1">, !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)
  pir.end %t7
  %batch = pir.reduce "batch" contract "kzg_batch" (%o2, %o1 : !pir.claim<"single_opening">, !pir.claim<"single_opening">) deps(%gamma : !pir.val<"fr">) checks {opening = "batch_ok"} anchors [{members = "sha256:96642ac9a6b160285952fc491ea0043a2cad98fe32f8de0dd6b3893f5932aa93", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64"}] -> !pir.claim<"batch_opening">
  pir.material_bind %c1 to "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4" : !pir.val<"g1">
  pir.material_bind %c2 to "sha256:75136a554c8ccd7a0780bbe87fb34ae8ef8d34eefb2509bc719f7b3160a3244b" : !pir.val<"g1">
  pir.material_bind %z to "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64" : !pir.val<"fr">
  pir.material_bind %v1 to "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379" : !pir.val<"fr">
  pir.material_bind %v2 to "sha256:308efab7d1ff27bcb8edb1d1ec89290f26621e6372fa7708f6fe5fda83ad45ba" : !pir.val<"fr">
  pir.export %batch : !pir.claim<"batch_opening"> route "to.consumer"
}

pir.protocol "cons" kappa {codecs = {fr = "fr_be32"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %batched = pir.instantiate "batched" anchors {members = "sha256:96642ac9a6b160285952fc491ea0043a2cad98fe32f8de0dd6b3893f5932aa93", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64"} : !pir.claim<"batch_opening">
  %t0 = pir.begin
  %t1, %context = pir.bind %t0 "context" : "fr" stage instance
  pir.end %t1
  pir.residual %batched : !pir.claim<"batch_opening"> route "batch-terminal-unmodeled"
}
