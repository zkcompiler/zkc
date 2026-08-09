// RUN: zkc-opt %s | zkc-opt | FileCheck %s
// Round-trip of the endpoint carrier: the exact artifact shape
// pir-project must emit for the Schnorr twin — one program, embedded
// src provenance (canonical event positions), linear sponge and
// stream, decision last.

// CHECK-LABEL: oir.artifact "schnorr"
oir.artifact "schnorr"
    id "6af02b5de1e864c079df759e5d0861b34ec028764e61500cb1dc08d40b3e0c84"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "verifier" {
  oir.program attributes {statement_labels = ["x"]} {
  ^bb0(%x: !oir.val<"tg", "public">, %proof: !oir.stream):
    // CHECK: oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    // CHECK-NEXT: oir.absorb {{.*}} src [0]
    %sp1 = oir.absorb %sp0, %x : !oir.val<"tg", "public"> src [0]
    %st1, %a = oir.read %proof "commit_A" : "tg" src [1]
    %sp2 = oir.absorb %sp1, %a : !oir.val<"tg", "wire"> src [1]
    // CHECK: oir.squeeze {{.*}} "c" : "scalar" count "1" domain "schnorr.c" rule "uniform" space "2305843009213693952" src [2]
    %sp3, %c = oir.squeeze %sp2 "c" : "scalar" count "1" domain "schnorr.c" rule "uniform" space "2305843009213693952" src [2]
    %st2, %z = oir.read %st1 "resp_z" : "scalar" src [3]
    %sp4 = oir.absorb %sp3, %z : !oir.val<"scalar", "wire"> src [3]
    // CHECK: oir.check_call "verify" kind "assert_eq" digest "sha256:0000000000000000000000000000000000000000000000000000000000000000"
    oir.check_call "verify" kind "assert_eq" digest "sha256:0000000000000000000000000000000000000000000000000000000000000000" (%a, %c, %z : !oir.val<"tg", "wire">, !oir.val<"scalar", "sampled">, !oir.val<"scalar", "wire">) src [4]
    oir.expect_end %st2
    // CHECK: oir.decide %{{.+}}
    oir.decide %sp4
  }
}

// The dual projection of the same seal: the prover endpoint — write
// where the verifier reads, absorb and squeeze identically, holes for
// the compute, end_stream/finish as the terminal consumers
// (docs/spec/endpoints.md §6.1).

// CHECK-LABEL: oir.artifact "schnorr_prover"
oir.artifact "schnorr_prover"
    id "6af02b5de1e864c079df759e5d0861b34ec028764e61500cb1dc08d40b3e0c85"
    source "sha256:987db52abcc816efde63c64e94705cc6bc902003c031690b836b3766735bd69b"
    endpoint "prover_skeleton" {
  oir.program attributes {counterparty = [], statement_labels = ["x"],
                          witness_labels = [["w", "sigma-witness"]]} {
  ^bb0(%x: !oir.val<"tg", "public">, %w: !oir.handle<"sigma-witness">,
       %proof: !oir.stream):
    %sp0 = oir.transcript_init sponge "toy_duplex" iv "artifact-id"
    %sp1 = oir.absorb %sp0, %x : !oir.val<"tg", "public"> src [0]
    // CHECK: oir.hole_call "commit" kind "commit" digest "sha256:1111111111111111111111111111111111111111111111111111111111111111"
    %a, %w1 = oir.hole_call "commit" kind "commit" digest "sha256:1111111111111111111111111111111111111111111111111111111111111111" (%w : !oir.handle<"sigma-witness">) -> !oir.val<"tg", "hole">, !oir.handle<"sigma-witness">
    // CHECK: oir.write {{.*}} as "commit_A" class "tg" src [1]
    %st1 = oir.write %proof, %a : !oir.val<"tg", "hole"> as "commit_A" class "tg" src [1]
    %sp2 = oir.absorb %sp1, %a : !oir.val<"tg", "hole"> src [1]
    %sp3, %c = oir.squeeze %sp2 "c" : "scalar" count "1" domain "schnorr.c" rule "uniform" space "2305843009213693952" src [2]
    %z = oir.hole_call "resp" kind "evaluate" digest "sha256:2222222222222222222222222222222222222222222222222222222222222222" (%c, %w1 : !oir.val<"scalar", "sampled">, !oir.handle<"sigma-witness">) -> !oir.val<"scalar", "hole">
    %st2 = oir.write %st1, %z : !oir.val<"scalar", "hole"> as "resp_z" class "scalar" src [3]
    %sp4 = oir.absorb %sp3, %z : !oir.val<"scalar", "hole"> src [3]
    // CHECK: oir.end_stream
    oir.end_stream %st2
    // CHECK: oir.finish %{{.+}}
    oir.finish %sp4
  }
}
