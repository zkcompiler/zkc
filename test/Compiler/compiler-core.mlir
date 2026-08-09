// RUN: zkc-test-opt %pir-seal-full \
// RUN:   -test-compiler-core='protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json signature=%zkc-registry-dir/soundness-signature.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' \
// RUN:   %S/../Encoding/sumcheck-fs.mlir 2>&1 | FileCheck %s

// CHECK: compiler domain: 2 canonical alternatives
// CHECK-NEXT: compiler derive: shared DERIVE accepted
// CHECK-NEXT: compiler select: ordinal tie-break exact
// CHECK-NEXT: compiler check decision: full selection recomputed
// CHECK-NEXT: compiler operational failure: late error propagated
// CHECK-NEXT: compiler submitted frontier: exact
// CHECK-NEXT: compiler constraints: exact substitutions and recursion closed
// CHECK-NEXT: compiler valid: exact total loss and hypothesis constraints
// CHECK-NEXT: compiler missing width: no eligible candidate
// CHECK-NEXT: compiler rounds: exact round/max and bound algebra accepted
// CHECK-NEXT: compiler transform: sequential lineage and assume leaves exact
// CHECK-NEXT: compiler introduced: related source envelope exact
// CHECK-NEXT: compiler empty folds: add zero and max refusal exact
// CHECK-NEXT: compiler transform refusals: authority checker and lineage closed
// CHECK-NEXT: compiler refusals: nonidentity/cycle closed
// CHECK-NEXT: compiler core: PASS
