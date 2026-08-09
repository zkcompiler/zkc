// RUN: zkc-test-opt -test-soundness-runtime %s 2>&1 | FileCheck %s

module {}

// CHECK: soundness runtime safety: PASS
