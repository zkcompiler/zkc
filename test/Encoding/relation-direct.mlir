// REQUIRES: uv
// The direct relation witness is the one committed protocol whose verifier
// face is a single opaque check, so its differential is what pins the
// seven-element check_call row: both the human-readable contract id and the
// sealed content digest enter OIR identity (docs/spec/carrier.md section 6).
// The transparent witnesses never reach that row shape.
// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: zkc-translate --canonical %t.sealed -o %t.zkc
// RUN: %uv python -m oracle.parity encode relation-direct > %t.oracle
// RUN: diff %t.zkc %t.oracle
// RUN: zkc-translate --id %t.sealed -o %t.zkc-id
// RUN: %uv python -m oracle.parity id relation-direct > %t.oracle-id
// RUN: diff %t.zkc-id %t.oracle-id
// RUN: zkc-opt %pir-project-full %t.sealed > %t.projected
// RUN: zkc-translate --oir-canonical %t.projected -o %t.oir.zkc
// RUN: %uv python -m oracle.parity oir-encode relation-direct > %t.oir.oracle
// RUN: diff %t.oir.zkc %t.oir.oracle
// RUN: zkc-translate --oir-id %t.projected -o %t.oir-id.zkc
// RUN: %uv python -m oracle.parity oir-id relation-direct > %t.oir-id.oracle
// RUN: diff %t.oir-id.zkc %t.oir-id.oracle

pir.protocol "relation_direct" kappa {codecs = {}, iv = "artifact-id", sponge = "toy_duplex"} {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:1a255a52c5db410cb7e99e6edf609e9ac8f41ff52b4dd625e82fff54ff415cbe", statement = "sha256:912b1c40e2557a50e621f9da9f829b1e36449bdbe1b6e175e4b9dd0a704a47fd"} : !pir.claim<"opaque_relation">
  %thread = pir.begin
  pir.check "predicate" contract "zkc.check.relation-predicate" semantic_args {contract = "sha256:1a255a52c5db410cb7e99e6edf609e9ac8f41ff52b4dd625e82fff54ff415cbe", statement = "sha256:912b1c40e2557a50e621f9da9f829b1e36449bdbe1b6e175e4b9dd0a704a47fd"}
  pir.end %thread
  pir.discharge %relation : !pir.claim<"opaque_relation"> rule "zkc.terminal.relation-direct" checks {predicate = "predicate"}
}
