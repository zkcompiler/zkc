// The bounded artifact-verification carrier form (docs/spec/endpoints.md
// §3.1). The facts a parent must bind to name which child proposition it
// verifies are sealed content: child identity, endpoint kind, verifier
// semantics, key, statement, child protocol, child relation contract, the
// parent route, and the proof slots the child verifier consumes.
//
// The contract is reserved. This fixture pins the two ends the carrier
// owns -- the form seals, and projection refuses -- so that the versioned
// projection, execution, and conformance surface arrive against a shape
// that is already fixed rather than inventing one.

// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: zkc-translate --canonical %t.sealed -o %t.zkc
// RUN: FileCheck %s --check-prefix=ROW < %t.zkc
//
// The parity legs are gated on uv per RUN line rather than for the whole
// file: the seal, the row, and the projection refusal must be exercised on
// a machine without the twin, or a green suite there would mean nothing.
// RUN: %if uv %{ %uv python -m oracle.parity encode artifact-verify > %t.oracle %}
// RUN: %if uv %{ diff %t.zkc %t.oracle %}
// RUN: %if uv %{ zkc-translate --id %t.sealed -o %t.zkc-id %}
// RUN: %if uv %{ %uv python -m oracle.parity id artifact-verify > %t.oracle-id %}
// RUN: %if uv %{ diff %t.zkc-id %t.oracle-id %}

// Every fact the reserved contract binds reaches the canonical encoding:
// two parents that verify different children, or the same child under a
// different key or statement, are different protocols.
// ROW: "artifact_verify"
// ROW-SAME: sha256:9bb3a90b6b08eaeb04602ebd4327f186511d71f7d05b49e1f8a50554afa66f77
// ROW-SAME: "verifier"
// ROW-SAME: "zkc.child.verifier.v1"

// Projection refuses rather than dropping a protected effect or lowering a
// contract that has no execution rule yet. The refusal names the reserved
// contract, so an author reads why the form seals but does not project
// instead of reading a generic missing-rule diagnostic.
//
// The verifier endpoint is the one pinned here. The prover endpoint refuses
// this fixture earlier, for a reason that has nothing to do with artifact
// verification -- a prover projection needs construction routes and this
// protocol declares none -- so pinning it would pin the wrong refusal.
// RUN: not zkc-opt %pir-project-full %t.sealed 2>&1 | FileCheck %s --check-prefix=VERIFIER
// VERIFIER: [zkc-E235] bounded artifact verification 'child_proof' is a reserved endpoint contract
// VERIFIER-SAME: awaits the versioned projection, execution, and conformance surface

pir.protocol "recursive_parent" kappa {codecs = {rs = "ts_be8", scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "child_statement" anchors {contract = "sha256:6ee6bd757d89f3a090c844c3dcee5b569518319be9bd41f18d9bc6e16acd4baa", statement = "sha256:7fa4a7ff3aa5b35f12e112174c075f3a9e83a3bb3fcc336e4d0a25f06e12b345"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "rs" stage instance
  // The child's proof enters the parent's stream as ordinary material; the
  // verification names which slots it consumes.
  %t2, %pi = pir.slot %t1 "child_pi" : "rs"
  %t3 = pir.artifact_verify %t2 "child_proof" child "sha256:9bb3a90b6b08eaeb04602ebd4327f186511d71f7d05b49e1f8a50554afa66f77" endpoint "verifier" semantics "zkc.child.verifier.v1" key "sha256:399a1df13589ca02cea9ce8feb91497ef225da694fdd56a3a88db0c0f106e281" statement "sha256:7fa4a7ff3aa5b35f12e112174c075f3a9e83a3bb3fcc336e4d0a25f06e12b345" protocol "sha256:e9192af5b28560ecf2e3e74c54334050c080715ac579d6fc3a12c7bdd4c61a5e" relation_contract "sha256:6ee6bd757d89f3a090c844c3dcee5b569518319be9bd41f18d9bc6e16acd4baa" route "child-verification-not-modeled" proof_slots ["child_pi"]
  // The parent has a verifier face of its own; the child verification is
  // an effect beside it, not a substitute for one.
  pir.check "parent_binding" contract "zkc.check.rs-equality" (%x, %pi : !pir.val<"rs">, !pir.val<"rs">) expr ["eq", ["in", 0], ["in", 1]]
  pir.end %t3
  // The child's obligation is lifted into the parent route surface, which
  // is the route the verification names. A verification whose route no sink
  // carries has lifted nothing, and seal refuses it.
  pir.residual %relation : !pir.claim<"opaque_relation"> route "child-verification-not-modeled"
}

