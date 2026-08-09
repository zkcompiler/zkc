// RUN: zkc-opt '-pir-batch-open=batch-space=52435875175126190479447740508185965837690552500527637822603658699938581184513' %s -o %t.once
// RUN: zkc-opt '-pir-batch-open=batch-space=52435875175126190479447740508185965837690552500527637822603658699938581184513' '-pir-batch-open=batch-space=52435875175126190479447740508185965837690552500527637822603658699938581184513' %s -o %t.twice
// RUN: diff %t.once %t.twice
// RUN: zkc-opt %pir-seal-full %t.once | FileCheck %s
// RUN: not zkc-opt -pir-batch-open %s 2>&1 | FileCheck --check-prefix=SPACE %s
//
// Two fully closed v4 KZG openings at one point become one generic reduction.
// The transform preserves the semantic-material edges, replaces both terminal
// rules by the admitted batch rule, and is byte-idempotent on a second run.

// CHECK: pir.sealed "kzg_before"
// CHECK-SAME: pir.pass_manifest = "{{.*}}sha256:96642ac9a6b160285952fc491ea0043a2cad98fe32f8de0dd6b3893f5932aa93
// CHECK: pir.chal {{.*}} "batch.96642ac9.gamma" : "fr" domain "batch_open.96642ac9a6b16028"
// CHECK: pir.check "batch.96642ac9.open" contract "zkc.check.kzg-batch-opening" params {suite = "bls12-381"}
// CHECK: pir.reduce "batch.96642ac9" contract "kzg_batch"
// CHECK-SAME: -> !pir.claim<"batch_opening">
// CHECK: pir.material_bind
// CHECK: pir.discharge {{.*}} : <"batch_opening"> rule "zkc.terminal.kzg-batch-opening" checks {opening = "batch.96642ac9.open"}
// CHECK-NOT: zkc.terminal.kzg-opening
// SPACE: pir-batch-open: the batch-challenge space is required

pir.protocol "kzg_before" kappa {codecs = {fr = "fr_be32", g1 = "bls_g1_be48"}, iv = "artifact-id", sponge = "toy_duplex"} {
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
