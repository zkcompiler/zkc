// RUN: zkc-test-opt \
// RUN:   -test-soundness-semantic-regressions='protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json signature=%zkc-registry-dir/soundness-signature.json' \
// RUN:   %s 2>&1 | FileCheck %s

// CHECK: grinding ordinal 0 scales vector position 0: accepted
// A composed premise is longer than the premise reduction's own rounds, so the
// authenticated ordinal no longer names the round it was authenticated
// against.  The range check alone passes, which is why this is its own case.
// CHECK-NEXT: grinding ordinal over a composed premise: refused
// CHECK-NEXT: grinding adjacency exact premise claim: refused
// CHECK-NEXT: derive pre-marked assumption: refused
// CHECK-NEXT: soundness semantic regressions: PASS

module {}
