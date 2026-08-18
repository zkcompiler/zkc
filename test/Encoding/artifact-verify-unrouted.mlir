// The route is the link endpoints.md §3.1 requires: a child's assumptions,
// exports, residuals, and carried obligations are either discharged by the
// child-verifier semantics or lifted into the parent-visible route surface.
// The carrier cannot read the child, so what it enforces is that the parent
// names a route its own sinks carry -- a verification routing nowhere has
// lifted nothing, and seal refuses rather than sealing a boundary that
// silently drops the child's obligations.

// RUN: not zkc-opt %pir-seal-full %s -o /dev/null 2>&1 | FileCheck %s
// CHECK: [zkc-E163] artifact verification 'child_proof' routes through 'nowhere'
// CHECK-SAME: which no sink of this artifact names

pir.protocol "unrouted_child" kappa {codecs = {rs = "ts_be8", scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "child_statement" anchors {contract = "sha256:fb0288872031fc4818c03a7253bd3a78de192d05e6bccd09ceabeda65b4d7c6f", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "rs" stage instance
  %t2, %pi = pir.slot %t1 "child_pi" : "rs"
  %t3 = pir.artifact_verify %t2 "child_proof" child "sha256:9f1c0f5a5e5f4d3c2b1a0918273645541e2d3c4b5a69788796a5b4c3d2e1f0aa" endpoint "verifier" semantics "zkc.child.verifier.v1" key "sha256:1b2c3d4e5f60718293a4b5c6d7e8f9001122334455667788990aabbccddeeff0" statement "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" protocol "sha256:c0ffee11223344556677889900aabbccddeeff00112233445566778899aabbcc" relation_contract "sha256:fb0288872031fc4818c03a7253bd3a78de192d05e6bccd09ceabeda65b4d7c6f" route "nowhere" proof_slots ["child_pi"]
  pir.check "parent_binding" contract "zkc.check.rs-equality" (%x, %pi : !pir.val<"rs">, !pir.val<"rs">) expr ["eq", ["in", 0], ["in", 1]]
  pir.end %t3
  pir.residual %relation : !pir.claim<"opaque_relation"> route "child-verification-not-modeled"
}
