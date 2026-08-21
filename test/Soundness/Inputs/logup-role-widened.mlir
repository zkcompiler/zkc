// A message role filled by two commitments that declare different sizes.
//
// Driven by logup-bus.test. Nothing in the shipped contracts reaches this —
// every role there takes exactly one member — but a role taking several is a
// shape the vocabulary permits, and then two members declaring different
// sizes leave a rule reading that role no single number to price with. The
// test that drives this file widens the contract to match.
pir.protocol "logup_bus" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %inclusion = pir.instantiate "inclusion" anchors {multiplicities = "sha256:5b1a0eb6f9c0b5b2fc4a9c9f6a0e4b4d3f1c6a8e2d7b0c9a5e3f8d1b7c4a2e60", queries = "sha256:9c1e4a7f2b8d0356e9a4c1f7b3d5028e6a9c4f1b7d3e5082a6c9f4b1d7e30528", table = "sha256:3f2a1c8d5e7b9046a2c1e8f4d6b0937518a4c2e0f9d7b5638a1c4e2f0d9b7563"} : !pir.claim<"logup_inclusion">
  %t0 = pir.begin
  %t1, %table = pir.slot %t0 "table" : profile "logup_committed_column" in "bus" as "table"
  %t2, %queries = pir.slot %t1 "queries" : profile "logup_committed_column" in "bus" as "queries"
  // The second occupant of the same role, at a different declared size.
  %t2b, %queries2 = pir.slot %t2 "queries2" : profile "logup_queries" in "bus" as "queries" idx 1
  %t3, %mult = pir.slot %t2b "mult" : profile "logup_committed_column" in "bus" as "multiplicities"
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
