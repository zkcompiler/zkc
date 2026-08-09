// RUN: zkc-test-opt %pir-seal-full \
// RUN:   -test-soundness-kzg-preservation='protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json signature=%zkc-registry-dir/soundness-signature.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' \
// RUN:   %S/../Encoding/kzg-after.mlir 2>&1 | FileCheck %s

// CHECK: KZG preservation: EB + DB exact
// CHECK-NEXT: KZG preservation: 2 * ARSDH exact
// CHECK-NEXT: KZG preservation: wrong point/order refused
// CHECK-NEXT: soundness KZG preservation: PASS
