// A lookup bus over committed columns, and the first protocol whose values
// carry profiles rather than bare payload classes.
//
// `!pir.val<profile "logup_column_1024">` resolves a `value_profiles` entry
// in the sealed vocabulary. The profile states what stands behind the
// commitment — a thousand and twenty-four scalars, committed by the prover,
// under a named binding route — where a bare class would have said only
// "this is a scalar-shaped value". The claim type has resolved a descriptor
// profile from the beginning; this is the same treatment for the other type,
// and every mechanism that reconstructed what a commitment binds on the rule
// side was working around its absence (docs/spec/carrier.md §3).
//
// The transcript order is forced, not chosen. The helper column depends on
// the bus challenge and so commits after it, and a round's messages must
// precede that round's challenge (`zkc-E213`), so the helper belongs to a
// second round. That round's challenge indexes into the committed columns
// and its space is the profile's arity, which is what ties a fact the rule
// reads back to sealed structure rather than leaving it declared.

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

// A profiled slot is its own event family: it carries the profile name where
// the scalar family carries a payload class, so no row outside this protocol
// moves and the two cannot be confused by a reader of the encoding.
// ROW: "slot_profiled"
// ROW-SAME: "logup_column_1024"
// ROW: "slot_profiled"
// ROW-SAME: "logup_column_1024"

pir.protocol "logup_bus" kappa {codecs = {query_index = "ts_be8", scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "air" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  // The three committed columns: the looked-up values, the table, and the
  // multiplicities. Each is one commitment, and each says what it commits to.
  %t1, %values = pir.slot %t0 "values" : profile "logup_column_1024" in "bus" as "cols"
  %t2, %table = pir.slot %t1 "table" : profile "logup_column_1024" in "bus" as "cols" idx 1
  %t3, %mult = pir.slot %t2 "mult" : profile "logup_column_1024" in "bus" as "cols" idx 2
  // The bus challenge, at which the logarithmic-derivative identity is
  // checked (Haböck, ePrint 2022/1530, Lemma 5).
  %t4, %beta = pir.chal %t3 deps(%values, %table, %mult : !pir.val<profile "logup_column_1024">, !pir.val<profile "logup_column_1024">, !pir.val<profile "logup_column_1024">) "beta" : "scalar" domain "logup.beta" space "2305843009213693952"
  // The helper column is a function of the bus challenge, so it commits
  // after it and belongs to the second round.
  %t5, %helper = pir.slot %t4 "helper" : profile "logup_column_1024" in "bus" as "helper"
  // The opening index. Its space is the committed arity, which is the tie
  // between the profile's declared content and the sealed spine.
  %t6, %idx = pir.chal %t5 deps(%helper : !pir.val<profile "logup_column_1024">) "idx" : "query_index" domain "logup.idx" space "1024"
  pir.end %t6
  %inclusion = pir.reduce "bus" contract "logup_bus" (%relation : !pir.claim<"opaque_relation">) deps(%beta, %idx : !pir.val<"scalar">, !pir.val<"query_index">) checks {} anchors [{multiplicities = "sha256:5b1a0eb6f9c0b5b2fc4a9c9f6a0e4b4d3f1c6a8e2d7b0c9a5e3f8d1b7c4a2e60", table = "sha256:3f2a1c8d5e7b9046a2c1e8f4d6b0937518a4c2e0f9d7b5638a1c4e2f0d9b7563", values = "sha256:9c1e4a7f2b8d0356e9a4c1f7b3d5028e6a9c4f1b7d3e5082a6c9f4b1d7e30528"}] -> !pir.claim<"logup_inclusion">
  // Each committed column's anchor is tied to the transcript value that
  // carries it, so the claim's identity rests on material the verifier saw
  // rather than on the reduction's word.
  pir.material_bind %values to "sha256:9c1e4a7f2b8d0356e9a4c1f7b3d5028e6a9c4f1b7d3e5082a6c9f4b1d7e30528" : !pir.val<profile "logup_column_1024">
  pir.material_bind %table to "sha256:3f2a1c8d5e7b9046a2c1e8f4d6b0937518a4c2e0f9d7b5638a1c4e2f0d9b7563" : !pir.val<profile "logup_column_1024">
  pir.material_bind %mult to "sha256:5b1a0eb6f9c0b5b2fc4a9c9f6a0e4b4d3f1c6a8e2d7b0c9a5e3f8d1b7c4a2e60" : !pir.val<profile "logup_column_1024">
  pir.residual %inclusion : !pir.claim<"logup_inclusion"> route "logup-constraints-not-modeled"
}
