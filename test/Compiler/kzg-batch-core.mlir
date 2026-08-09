// RUN: zkc-test-opt \
// RUN:   -test-kzg-batch-core='protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' \
// RUN:   %S/../Encoding/kzg-before.mlir 2>&1 | FileCheck %s

// CHECK: applications: 1
// CHECK: canonical-claims: 0,1
// CHECK: reordered: refused
// CHECK: wrong-suite: declined
// CHECK: replay: accepted
// CHECK: mutated-replay: refused
// CHECK: source-reads: 2 bls_g1_be48
// CHECK: final-reads: 1 bls_g1_be48
// CHECK: final-seal: accepted
// CHECK: source-projection:
// CHECK-COUNT-2: oir.read
// CHECK: final-projection:
// CHECK-COUNT-1: oir.read
