// The proof slots a child verifier consumes are slots of this artifact.
//
// Left unchecked, the label has nothing to resolve to at encoding time, and
// a label naming nothing would have to either alias onto an event position
// — giving two different protocols one identity — or fail with no
// diagnostic an author can act on. It refuses at seal instead.

// RUN: not zkc-opt %pir-seal-full -split-input-file %s -o /dev/null 2>&1 | FileCheck %s
// CHECK: [zkc-E164] unresolved proof slot 'no_such_slot'
// CHECK-SAME: not a slot of this artifact
// CHECK: [zkc-E165] out-of-order proof slot 'child_pi'
// CHECK-SAME: follows the verification on the spine

pir.protocol "unresolved_proof_slot" kappa {codecs = {rs = "ts_be8", scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "child_statement" anchors {contract = "sha256:6ee6bd757d89f3a090c844c3dcee5b569518319be9bd41f18d9bc6e16acd4baa", statement = "sha256:7fa4a7ff3aa5b35f12e112174c075f3a9e83a3bb3fcc336e4d0a25f06e12b345"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "rs" stage instance
  %t2, %pi = pir.slot %t1 "child_pi" : "rs"
  %t3 = pir.artifact_verify %t2 "child_proof" child "sha256:9bb3a90b6b08eaeb04602ebd4327f186511d71f7d05b49e1f8a50554afa66f77" endpoint "verifier" semantics "zkc.child.verifier.v1" key "sha256:399a1df13589ca02cea9ce8feb91497ef225da694fdd56a3a88db0c0f106e281" statement "sha256:7fa4a7ff3aa5b35f12e112174c075f3a9e83a3bb3fcc336e4d0a25f06e12b345" protocol "sha256:e9192af5b28560ecf2e3e74c54334050c080715ac579d6fc3a12c7bdd4c61a5e" relation_contract "sha256:6ee6bd757d89f3a090c844c3dcee5b569518319be9bd41f18d9bc6e16acd4baa" route "child-verification-not-modeled" proof_slots ["no_such_slot"]
  pir.check "parent_binding" contract "zkc.check.rs-equality" (%x, %pi : !pir.val<"rs">, !pir.val<"rs">) expr ["eq", ["in", 0], ["in", 1]]
  pir.end %t3
  pir.residual %relation : !pir.claim<"opaque_relation"> route "child-verification-not-modeled"
}

// -----

// The spine is a total order and an event reads what precedes it. A
// verification naming material that arrives later would have the child
// consume a proof that is not in the stream yet — a shape no projection
// could realize, so it does not seal.

pir.protocol "proof_slot_after_the_verification" kappa {codecs = {rs = "ts_be8", scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "child_statement" anchors {contract = "sha256:6ee6bd757d89f3a090c844c3dcee5b569518319be9bd41f18d9bc6e16acd4baa", statement = "sha256:7fa4a7ff3aa5b35f12e112174c075f3a9e83a3bb3fcc336e4d0a25f06e12b345"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "rs" stage instance
  %tv = pir.artifact_verify %t1 "child_proof" child "sha256:9bb3a90b6b08eaeb04602ebd4327f186511d71f7d05b49e1f8a50554afa66f77" endpoint "verifier" semantics "zkc.child.verifier.v1" key "sha256:399a1df13589ca02cea9ce8feb91497ef225da694fdd56a3a88db0c0f106e281" statement "sha256:7fa4a7ff3aa5b35f12e112174c075f3a9e83a3bb3fcc336e4d0a25f06e12b345" protocol "sha256:e9192af5b28560ecf2e3e74c54334050c080715ac579d6fc3a12c7bdd4c61a5e" relation_contract "sha256:6ee6bd757d89f3a090c844c3dcee5b569518319be9bd41f18d9bc6e16acd4baa" route "child-verification-not-modeled" proof_slots ["child_pi"]
  %t2, %pi = pir.slot %tv "child_pi" : "rs"
  pir.check "parent_binding" contract "zkc.check.rs-equality" (%x, %pi : !pir.val<"rs">, !pir.val<"rs">) expr ["eq", ["in", 0], ["in", 1]]
  pir.end %t2
  pir.residual %relation : !pir.claim<"opaque_relation"> route "child-verification-not-modeled"
}
