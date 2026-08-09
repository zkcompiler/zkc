// RUN: zkc-test-opt %pir-seal-full \
// RUN:   -test-soundness-rule-bodies='protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json signature=%zkc-registry-dir/soundness-signature.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' \
// RUN:   %S/../Encoding/schnorr.mlir 2>&1 | FileCheck %s

// CHECK: body: special soundness entry exact
// CHECK-NEXT: body: special soundness to round-by-round exact
// CHECK-NEXT: soundness rule bodies: PASS
