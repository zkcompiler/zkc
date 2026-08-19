// The ad-hoc lookup: a prover who supplies the table as well as the values
// looked up in it. Beside the range check, whose table the statement fixes,
// this is the other side of the origin rule — the same three roles filled by
// prover messages, and value profiles that say `prover_message` to match.
//
// Keeping both is what makes the seat rule testable in the direction that
// matters. A profile's origin and the event carrying it are one fact with two
// spellings; a family with only one of the two seats could not tell whether
// the seal checks the agreement or merely the spelling it happens to see.
//
// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: zkc-translate --canonical %t.sealed -o %t.zkc
// RUN: FileCheck %s --check-prefix=ROW < %t.zkc
//
// The parity legs are gated per RUN line rather than for the whole file, so
// the seal and the row are exercised on a machine without the twin.
// RUN: %if uv %{ %uv python -m oracle.parity encode logup-bus > %t.oracle %}
// RUN: %if uv %{ diff %t.zkc %t.oracle %}
// RUN: %if uv %{ zkc-translate --id %t.sealed -o %t.id %}
// RUN: %if uv %{ %uv python -m oracle.parity id logup-bus > %t.id.oracle %}
// RUN: %if uv %{ diff %t.id %t.id.oracle %}

// Every column is a profiled slot here, and the profile is cited in the
// sealed table, which is what makes the artifact's identity commit to the
// arity a bound is priced from.
// ROW: "events":{{\[\[}}"slot_profiled","logup_committed_column",1,[1,"table",0]],["slot_profiled","logup_committed_column",1,[1,"queries",0]],["slot_profiled","logup_committed_column",1,[1,"multiplicities",0]],["chal",
// ROW-SAME: "value_profiles":{"logup_committed_column":"sha256:

pir.protocol "logup_bus" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %inclusion = pir.instantiate "inclusion" anchors {multiplicities = "sha256:5b1a0eb6f9c0b5b2fc4a9c9f6a0e4b4d3f1c6a8e2d7b0c9a5e3f8d1b7c4a2e60", queries = "sha256:9c1e4a7f2b8d0356e9a4c1f7b3d5028e6a9c4f1b7d3e5082a6c9f4b1d7e30528", table = "sha256:3f2a1c8d5e7b9046a2c1e8f4d6b0937518a4c2e0f9d7b5638a1c4e2f0d9b7563"} : !pir.claim<"logup_inclusion">
  %t0 = pir.begin
  %t1, %table = pir.slot %t0 "table" : profile "logup_committed_column" in "bus" as "table"
  %t2, %queries = pir.slot %t1 "queries" : profile "logup_committed_column" in "bus" as "queries"
  %t3, %mult = pir.slot %t2 "mult" : profile "logup_committed_column" in "bus" as "multiplicities"
  // The bus challenge, at which the logarithmic-derivative identity is
  // instantiated (Haböck, ePrint 2022/1530, Lemma 5).
  %t4, %beta = pir.chal %t3 "beta" : "scalar" domain "logup.beta" space "2305843009213693951"
  pir.end %t4
  %identity = pir.reduce "bus" contract "logup_bus" (%inclusion : !pir.claim<"logup_inclusion">) deps(%beta : !pir.val<"scalar">) checks {} anchors [{multiplicities = "sha256:5b1a0eb6f9c0b5b2fc4a9c9f6a0e4b4d3f1c6a8e2d7b0c9a5e3f8d1b7c4a2e60", queries = "sha256:9c1e4a7f2b8d0356e9a4c1f7b3d5028e6a9c4f1b7d3e5082a6c9f4b1d7e30528", table = "sha256:3f2a1c8d5e7b9046a2c1e8f4d6b0937518a4c2e0f9d7b5638a1c4e2f0d9b7563"}] -> !pir.claim<"logup_identity">
  pir.material_bind %table to "sha256:3f2a1c8d5e7b9046a2c1e8f4d6b0937518a4c2e0f9d7b5638a1c4e2f0d9b7563" : !pir.val<profile "logup_committed_column">
  pir.material_bind %queries to "sha256:9c1e4a7f2b8d0356e9a4c1f7b3d5028e6a9c4f1b7d3e5082a6c9f4b1d7e30528" : !pir.val<profile "logup_committed_column">
  pir.material_bind %mult to "sha256:5b1a0eb6f9c0b5b2fc4a9c9f6a0e4b4d3f1c6a8e2d7b0c9a5e3f8d1b7c4a2e60" : !pir.val<profile "logup_committed_column">
  pir.residual %identity : !pir.claim<"logup_identity"> route "logup-identity-discharge-not-modeled"
}
