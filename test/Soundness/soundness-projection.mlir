// RUN: zkc-test-opt -test-soundness-projection %s 2>&1 | FileCheck %s

module {}

// CHECK: projection: exact parameter and IID-only challenge count
// CHECK-NEXT: projection: scalar ChallengeCount refused
// CHECK-NEXT: path: selected binding is the sole exact authority
// CHECK-NEXT: FRI arithmetic: positive and negative cases exact
// CHECK-NEXT: decider arithmetic: excessive exponents refused
// CHECK-NEXT: SamePoint: missing facts fail closed
// CHECK-NEXT: soundness projection: PASS
