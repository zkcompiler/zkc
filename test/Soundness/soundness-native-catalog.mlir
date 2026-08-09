// RUN: zkc-test-opt -test-soundness-native-catalog %s 2>&1 | FileCheck %s

// CHECK: native catalog: computational entry exact
// CHECK-NEXT: native catalog: special-soundness preservation exact
// CHECK-NEXT: native soundness catalog: PASS

module {}
