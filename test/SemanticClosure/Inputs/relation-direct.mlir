// The direct relation witness shared with oracle. Its digest-shaped
// contract and statement anchors are opaque Semantic Closure material; source
// relation validity and ABI coverage are deliberately outside this judgment.
pir.protocol "relation_direct" kappa {codecs = {}, iv = "artifact-id", sponge = "toy_duplex"} {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:1a255a52c5db410cb7e99e6edf609e9ac8f41ff52b4dd625e82fff54ff415cbe", statement = "sha256:912b1c40e2557a50e621f9da9f829b1e36449bdbe1b6e175e4b9dd0a704a47fd"} : !pir.claim<"opaque_relation">
  %thread = pir.begin
  pir.check "predicate" contract "zkc.check.relation-predicate" semantic_args {contract = "sha256:1a255a52c5db410cb7e99e6edf609e9ac8f41ff52b4dd625e82fff54ff415cbe", statement = "sha256:912b1c40e2557a50e621f9da9f829b1e36449bdbe1b6e175e4b9dd0a704a47fd"}
  pir.end %thread
  pir.discharge %relation : !pir.claim<"opaque_relation"> rule "zkc.terminal.relation-direct" checks {predicate = "predicate"}
}
