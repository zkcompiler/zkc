// RUN: not zkc-opt -pir-seal='construction-profile-registry=%zkc-registry-dir/construction-profiles.json' %S/../Encoding/sumcheck.mlir 2>&1 | FileCheck %s
//
// The protocol vocabulary is the sole shape-semantics authority. The shared
// environment boundary refuses before judging any protocol when it is absent.

// CHECK: [zkc-E248] pir-seal requires a protocol-vocabulary authority
