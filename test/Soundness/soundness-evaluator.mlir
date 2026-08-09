// RUN: zkc-test-opt %pir-seal-full \
// RUN:   -test-soundness-evaluator='protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json signature=%zkc-registry-dir/soundness-signature.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' \
// RUN:   %S/../Encoding/sumcheck-fs.mlir 2>&1 | FileCheck %s

// CHECK: apply: native sumcheck exact
// CHECK-NEXT: derive: sumcheck -> sr -> fs exact
// CHECK-NEXT: path binding mismatch: refused
// CHECK-NEXT: missing premise: refused
// CHECK-NEXT: condition false: refused
// CHECK-NEXT: dynamic exponent range: refused
// CHECK-NEXT: root assume: refused
// CHECK-NEXT: soundness evaluator: PASS
