// RUN: zkc-test-opt %pir-seal-full \
// RUN:   -test-soundness-site='protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' \
// RUN:   %S/../Encoding/schnorr.mlir 2>&1 | FileCheck %s

// CHECK: soundness sealed view: PASS
// CHECK-NEXT: view: 2 claims, 1 reduction
// CHECK-NEXT: reduction site: output, subject, and ordered input exact
// CHECK-NEXT: artifact mismatch: refused
// CHECK-NEXT: owner mismatch: refused
// CHECK-NEXT: path site: exact claim subject
// CHECK-NEXT: path claim mismatch: refused
