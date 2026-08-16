// The value-faithful spine (evaluation/upstream/plonky3-replay/README.md): the
// challenger-facing artifact whose iv, absorb material, and
// event set equal the pinned upstream FRI verifier's own — zero-state
// start, per-round caps, final-polynomial coefficient in the clear,
// arity binds in their own segment, a one-word nonce — and whose
// construction routes derive the prover endpoint with the FRI holes
// threading one codeword handle from witness to final coefficient,
// the pow-search hole peeking the transcript exactly at the grind.
// RUN: rm -rf %t && mkdir -p %t
// RUN: zkc-family %S/Inputs/plonky3-fri-vf.json --emit-vocabulary=%t/vocab.json --emit-spine=%t/spine.mlir
// RUN: zkc-opt '-pir-seal=protocol-vocabulary=%t/vocab.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' %t/spine.mlir -o %t/sealed.mlir
// RUN: FileCheck %s --check-prefix=SEALED < %t/sealed.mlir
// RUN: zkc-opt '-pir-project=protocol-vocabulary=%t/vocab.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' %t/sealed.mlir -o %t/verifier.mlir
// RUN: FileCheck %s --check-prefix=VERIFIER < %t/verifier.mlir
// RUN: zkc-opt '-pir-project=endpoint-kind=prover_skeleton protocol-vocabulary=%t/vocab.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' %t/sealed.mlir -o %t/prover.mlir
// RUN: FileCheck %s --check-prefix=PROVER < %t/prover.mlir

// SEALED: pir.sealed "plonky3-fri-value-faithful"
// SEALED-SAME: hole_contracts = {"zkc.hole.fri-answer" = "sha256:
// SEALED-SAME: "zkc.hole.fri-commit" = "sha256:
// SEALED-SAME: "zkc.hole.fri-reduce" = "sha256:
// SEALED-SAME: segments [12]
// SEALED: pir.bind {{.*}} "log_size" : "pow_value" stage seal = "3"
// SEALED: pir.chal {{.*}} "zeta" : "ext_field" domain "fri.zeta"
// SEALED: pir.slot {{.*}} "opened_value" : "ext_field" in "frij" as "opened" binding "openval.0"
// SEALED: pir.chal {{.*}} "alpha" : "ext_field" domain "fri.alpha"
// SEALED: pir.slot {{.*}} "g1_root" : "rs" in "frij" as "g1" binding "commit1.0"
// SEALED: pir.slot {{.*}} "final_poly" : "ext_field" in "frij" as "final" binding "final.0"
// SEALED: pir.bind {{.*}} "arity1" : "pow_value" stage seal = "1"
// SEALED: pir.slot {{.*}} "nonce" : "pow_value" in "grind" as "nonce" binding "grind.0"
// SEALED: pir.slot {{.*}} "query_leaves" : "word" count "4" unabsorbed binding "answer.0"
// SEALED: pir.slot {{.*}} "input_paths" : "rs" count "16" unabsorbed binding "answer.1"
// SEALED: pir.slot {{.*}} "sib1" : "ext_field" count "4" unabsorbed binding "answer.2"
// SEALED: pir.slot {{.*}} "path1" : "rs" count "12" unabsorbed binding "answer.3"
// SEALED: pir.slot {{.*}} "path3" : "rs" count "4" unabsorbed binding "answer.7"
// SEALED: pir.check "merkle_open" contract "zkc.check.merkle-multi-opening"
// SEALED: pir.check "query_consistency" contract "zkc.check.fri-query-consistency"

// VERIFIER: endpoint "verifier"
// VERIFIER: oir.transcript_init sponge "plonky3_bb31_poseidon2_w16_r8_lenpad" iv "zero"
// VERIFIER: oir.squeeze {{.*}} "zeta" : "ext_field"
// VERIFIER: oir.read {{.*}} "opened_value" : "ext_field"
// VERIFIER: oir.squeeze {{.*}} "alpha" : "ext_field"
// VERIFIER: oir.read {{.*}} "g1_root" : "rs"
// VERIFIER: oir.read {{.*}} "final_poly" : "ext_field"
// VERIFIER: oir.read {{.*}} "nonce" : "pow_value"
// VERIFIER: oir.squeeze {{.*}} "pow" : "pow_value" count "1" domain "grind.pow" rule "uniform" space "256"
// VERIFIER: oir.assert_eq {{.*}} as "pow_pin"
// VERIFIER: oir.squeeze {{.*}} "query" : "query_index" count "4"
// VERIFIER: oir.read {{.*}} "query_leaves" : "word" count "4"
// VERIFIER: oir.read {{.*}} "input_paths" : "rs" count "16"
// VERIFIER: oir.read {{.*}} "sib1" : "ext_field" count "4"
// VERIFIER: oir.read {{.*}} "path1" : "rs" count "12"
// VERIFIER: oir.read {{.*}} "path3" : "rs" count "4"
// VERIFIER: oir.check_call "merkle_open" kind "zkc.check.merkle-multi-opening" digest "sha256:
// VERIFIER: oir.check_call "query_consistency" kind "zkc.check.fri-query-consistency" digest "sha256:
// VERIFIER-SAME: params ["1", "0"]

// PROVER: endpoint "prover_skeleton"
// PROVER: witness_labels = {{\[\[}}"codeword", "fri-trace"]]
// PROVER: oir.squeeze {{.*}} "zeta" : "ext_field"
// PROVER: oir.hole_call "openval" kind "evaluate"
// PROVER: oir.write {{.*}} as "opened_value" class "ext_field"
// PROVER: oir.squeeze {{.*}} "alpha" : "ext_field"
// PROVER: oir.hole_call "reduce" kind "extend"
// PROVER: oir.hole_call "commit1" kind "commit"
// PROVER: oir.write {{.*}} as "g1_root" class "rs"
// PROVER: oir.hole_call "fold1" kind "fold"
// PROVER: oir.hole_call "final" kind "evaluate"
// PROVER: oir.write {{.*}} as "final_poly" class "ext_field"
// PROVER: oir.hole_call "grind" kind "pow_search"
// PROVER-SAME: !oir.sponge
// PROVER: oir.write {{.*}} as "nonce" class "pow_value"
// PROVER: oir.squeeze {{.*}} "query" : "query_index" count "4"
// PROVER: oir.hole_call "answer" kind "open"
// PROVER-SAME: result_counts ["4", "16", "4", "12", "4", "8", "4", "4"]
// PROVER: oir.write {{.*}} as "query_leaves" class "word" count "4"
// PROVER: oir.write {{.*}} as "input_paths" class "rs" count "16"
// PROVER: oir.write {{.*}} as "path3" class "rs" count "4"
// PROVER: oir.end_stream
// PROVER: oir.finish
