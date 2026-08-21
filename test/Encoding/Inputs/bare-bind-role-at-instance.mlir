// A role-filling binding whose value arrives per statement.
//
// Driven by value-profile-resolution.mlir. The value is how a binding names
// the material its role claims; an instance-stage binding has none at seal,
// so the role's material would rest on a declaration the transcript never
// sees.
pir.protocol "logup_range_check" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %inclusion = pir.instantiate "inclusion" anchors {multiplicities = "sha256:5b1a0eb6f9c0b5b2fc4a9c9f6a0e4b4d3f1c6a8e2d7b0c9a5e3f8d1b7c4a2e60", queries = "sha256:9c1e4a7f2b8d0356e9a4c1f7b3d5028e6a9c4f1b7d3e5082a6c9f4b1d7e30528", table = "sha256:3f2a1c8d5e7b9046a2c1e8f4d6b0937518a4c2e0f9d7b5638a1c4e2f0d9b7563"} : !pir.claim<"logup_inclusion">
  %t0 = pir.begin
  // The table the statement fixes. A public binding absorbs, so the challenge
  // below is bound to the table's content — a table sampled after the
  // challenge would be the weak Fiat-Shamir shape (docs/spec/kernel.md §5.2).
  %t1, %table = pir.bind %t0 "table" : "scalar" stage instance in "bus" as "table"
  // The looked-up column and the multiplicities the prover commits. The
  // multiplicity sequence is indexed by the table, so its declared arity is
  // the table's and a machine condition of the rule requires exactly that.
  %t2, %queries = pir.slot %t1 "queries" : profile "logup_queries" in "bus" as "queries"
  %t3, %mult = pir.slot %t2 "mult" : profile "logup_multiplicities" in "bus" as "multiplicities"
  // The bus challenge, at which the logarithmic-derivative identity is
  // instantiated (Haböck, ePrint 2022/1530, Lemma 5).
  %t4, %beta = pir.chal %t3 "beta" : "scalar" domain "logup.beta" space "2305843009213693951"
  pir.end %t4
  %identity = pir.reduce "bus" contract "logup_range_check" (%inclusion : !pir.claim<"logup_inclusion">) deps(%beta : !pir.val<"scalar">) checks {} anchors [{multiplicities = "sha256:5b1a0eb6f9c0b5b2fc4a9c9f6a0e4b4d3f1c6a8e2d7b0c9a5e3f8d1b7c4a2e60", queries = "sha256:9c1e4a7f2b8d0356e9a4c1f7b3d5028e6a9c4f1b7d3e5082a6c9f4b1d7e30528", table = "sha256:3f2a1c8d5e7b9046a2c1e8f4d6b0937518a4c2e0f9d7b5638a1c4e2f0d9b7563"}] -> !pir.claim<"logup_identity">
  // Each committed column's anchor is tied to the transcript value that
  // carries it, so the claim's identity rests on material the verifier saw
  // rather than on the reduction's word. The table needs no such line: a
  // profiled seal-stage binding absorbs the digest itself, so the value
  // already carries its own reference and a material binding on it would be
  // that fact spelled twice (docs/spec/carrier.md §4).
  pir.material_bind %queries to "sha256:9c1e4a7f2b8d0356e9a4c1f7b3d5028e6a9c4f1b7d3e5082a6c9f4b1d7e30528" : !pir.val<profile "logup_queries">
  pir.material_bind %mult to "sha256:5b1a0eb6f9c0b5b2fc4a9c9f6a0e4b4d3f1c6a8e2d7b0c9a5e3f8d1b7c4a2e60" : !pir.val<profile "logup_multiplicities">
  // The identity at the sampled point is what leaves. Discharging it is the
  // constraint system's business — helper columns, a running sum, and the
  // quotient machinery that checks them — which no rule here states.
  pir.residual %identity : !pir.claim<"logup_identity"> route "logup-identity-discharge-not-modeled"
}
