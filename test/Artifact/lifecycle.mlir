// The transport decoder authenticates bytes but does not mint semantic
// authority. Admission binds a decoded artifact to the exact cited registry
// entries, and mutable consumers receive independent raw clones.
// RUN: rm -rf %t.artifacts
// RUN: zkc-seal %S/../Encoding/routed-schnorr.mlir %zkc-seal-full -o %t.artifacts > /dev/null
// RUN: cp %t.artifacts/*.mlirbc %t.mlirbc
// RUN: %python %S/Inputs/rewrite-construction-profiles.py cited-change %zkc-registry-dir/construction-profiles.json %t.cited.json
// RUN: %python %S/Inputs/rewrite-construction-profiles.py uncited-addition %zkc-registry-dir/construction-profiles.json %t.additive.json
// RUN: zkc-test-opt %s -test-artifact-lifecycle='artifact=%t.mlirbc protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json base-construction-profiles=%zkc-registry-dir/construction-profiles.json cited-change-construction-profiles=%t.cited.json additive-construction-profiles=%t.additive.json' -o /dev/null 2>&1 | FileCheck %s

// CHECK: decode: accepted
// CHECK-NEXT: base admission: accepted
// CHECK-NEXT: cited authority mismatch: refused
// CHECK-NEXT: uncited additive authority: accepted
// CHECK-NEXT: verifier projection: accepted
// CHECK-NEXT: prover projection: accepted
// CHECK-NEXT: admitted projection isolation: accepted
// CHECK-NEXT: serialized snapshot isolation: accepted
// CHECK-NEXT: mutable clone isolation: accepted

module {}
