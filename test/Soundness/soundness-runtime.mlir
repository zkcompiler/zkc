// RUN: zkc-test-opt -test-soundness-runtime %s 2>&1 | FileCheck %s

module {}

// CHECK: closed-bound algebra edges: exact
// CHECK-NEXT: soundness runtime safety: PASS
