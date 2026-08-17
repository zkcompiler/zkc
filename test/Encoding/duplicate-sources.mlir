// Two sources with identical content refuse, so the canonical form is a
// complete invariant.
//
// Sources are ordered by content, and claim positions follow that order.
// Where two sources carry the same profile and the same anchors, content
// cannot separate them, and the tie fell to the order they were authored
// in — so the same protocol, written with the two lines swapped, took a
// different identity. Two identifiers for one object contradicts what an
// identity is for: a judgment about one would not transfer to the other,
// and a registry keyed by identity would hold two rows for one protocol.
//
// The container already refuses duplicate claim descriptors one level up,
// so refusing here is the same rule applied where the tie arises. An
// author who wants two claims about one relation separates them by
// anchor, which is what anchors are.

// RUN: not zkc-opt %pir-seal-full %s 2>&1 | FileCheck %s
// CHECK: [zkc-E172] two sources have identical profile and anchors

pir.protocol "duplicate_sources" kappa {codecs = {fr = "fr_be32", g1 = "bls_g1_be48"}, iv = "artifact-id", sponge = "toy_duplex"} policy "closed_proof" {
  %o1 = pir.instantiate "open1" anchors {commitment = "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64", value = "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379"} : !pir.claim<"single_opening">
  %o2 = pir.instantiate "open2" anchors {commitment = "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64", value = "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379"} : !pir.claim<"single_opening">
  %t0 = pir.begin
  %t1, %c1 = pir.bind %t0 "C1" : "g1" stage instance
  %t2, %z = pir.bind %t1 "z" : "fr" stage instance
  %t3, %v1 = pir.bind %t2 "v1" : "fr" stage instance
  %t4, %w1 = pir.slot %t3 "W1" : "g1"
  %t5, %w2 = pir.slot %t4 "W2" : "g1"
  pir.check "open1_ok" contract "zkc.check.kzg-opening" params {suite = "bls12-381"} (%c1, %z, %v1, %w1 : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)
  pir.check "open2_ok" contract "zkc.check.kzg-opening" params {suite = "bls12-381"} (%c1, %z, %v1, %w2 : !pir.val<"g1">, !pir.val<"fr">, !pir.val<"fr">, !pir.val<"g1">)
  pir.end %t5
  pir.material_bind %c1 to "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4" : !pir.val<"g1">
  pir.material_bind %z to "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64" : !pir.val<"fr">
  pir.material_bind %v1 to "sha256:54a6fdf8410a02a98b7ec0172870aa7cffcd9fc7cfa04d4ca35c89025b10c379" : !pir.val<"fr">
  pir.discharge %o1 : !pir.claim<"single_opening"> rule "zkc.terminal.kzg-opening" checks {opening = "open1_ok"}
  pir.discharge %o2 : !pir.claim<"single_opening"> rule "zkc.terminal.kzg-opening" checks {opening = "open2_ok"}
}
