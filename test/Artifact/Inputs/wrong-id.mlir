pir.sealed "relation_direct" id "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" kappa {codecs = {}, iv = "artifact-id", sponge = "toy_duplex"} vocab {check_contracts = {"zkc.check.relation-predicate" = "sha256:4d3ae9fe823b734613a8dee7df29b1cede11638d54692a274baaac56138c93ff"}, claim_profiles = {opaque_relation = "sha256:db632a627bb1fb032a5e09257482a3c92e166288a92825629291f93a8f681042"}, construction_profiles = {"sponge:toy_duplex" = "sha256:35aefee5b893ded95c3a1397e67477204f5f53711c9e7dc60d17efb6b2e26407"}, reduction_contracts = {}, terminal_rules = {"zkc.terminal.relation-direct" = "sha256:afd5ec4965e497b68aa4e5c73a18c6310701dc74ea916d6619cb1810d916aabf"}} {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:05998a94e196c41414f37e1982f06133e26f13525642c9c102b1c222b4037e25", statement = "sha256:4fbaa40d86f7755e1661aef783bd9f936c7e482111f15c0ac7fa826f7f83e7d6"} : !pir.claim<"opaque_relation">
  %thread = pir.begin
  pir.check "predicate" contract "zkc.check.relation-predicate" semantic_args {contract = "sha256:05998a94e196c41414f37e1982f06133e26f13525642c9c102b1c222b4037e25", statement = "sha256:4fbaa40d86f7755e1661aef783bd9f936c7e482111f15c0ac7fa826f7f83e7d6"}
  pir.end %thread
  pir.discharge %relation : !pir.claim<"opaque_relation"> rule "zkc.terminal.relation-direct" checks {predicate = "predicate"}
}
