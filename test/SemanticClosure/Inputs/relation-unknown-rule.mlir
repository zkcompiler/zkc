pir.protocol "relation_unknown_rule" kappa {codecs = {}, iv = "artifact-id", sponge = "toy_duplex"} {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:05998a94e196c41414f37e1982f06133e26f13525642c9c102b1c222b4037e25", statement = "sha256:4fbaa40d86f7755e1661aef783bd9f936c7e482111f15c0ac7fa826f7f83e7d6"} : !pir.claim<"opaque_relation">
  %thread = pir.begin
  pir.check "predicate" contract "zkc.check.relation-predicate" semantic_args {contract = "sha256:05998a94e196c41414f37e1982f06133e26f13525642c9c102b1c222b4037e25", statement = "sha256:4fbaa40d86f7755e1661aef783bd9f936c7e482111f15c0ac7fa826f7f83e7d6"}
  pir.end %thread
  pir.discharge %relation : !pir.claim<"opaque_relation"> rule "zkc.terminal.unknown" checks {predicate = "predicate"}
}
