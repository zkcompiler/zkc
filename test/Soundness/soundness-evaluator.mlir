// RUN: zkc-test-opt %pir-seal-full \
// RUN:   -test-soundness-evaluator='protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json signature=%zkc-registry-dir/soundness-signature.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' \
// RUN:   %S/../Encoding/sumcheck-fs.mlir 2>&1 | FileCheck %s

// CHECK: apply: native sumcheck exact
// CHECK-NEXT: derive: sumcheck -> sr -> fs exact
// CHECK-NEXT: adaptive premise: refused fail-closed
// CHECK-NEXT: path binding mismatch: refused
// CHECK-NEXT: missing premise: refused
// CHECK-NEXT: condition false: refused
// CHECK-NEXT: dynamic exponent range: refused
// CHECK-NEXT: root assume: refused
// CHECK-NEXT: soundness evaluator: PASS

// The same evaluator against a signature whose schema also admits the
// adaptive_instance forms (schema-only widening; every rule and binding
// digest is unchanged). The carrying rules must preserve the premise's
// quantification through both hops instead of refusing it — this is the
// only place in the tree a non-static value actually flows, so it is
// what keeps the coordinate from being decorative.
// RUN: %python %S/Inputs/widen_quantification.py \
// RUN:   %zkc-registry-dir/soundness-signature.json %t.widened.json
// RUN: zkc-test-opt %pir-seal-full \
// RUN:   -test-soundness-evaluator='protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json signature=%t.widened.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' \
// RUN:   %S/../Encoding/sumcheck-fs.mlir 2>&1 | FileCheck %s --check-prefix=WIDE

// WIDE: derive: sumcheck -> sr -> fs exact
// WIDE-NEXT: adaptive quantification: carried to fs
// WIDE: soundness evaluator: PASS

// The twin's leg of the same stress, from the same premise index. The
// carry runs either way — it is schema-independent — and the schema
// decides only whether the index it produces is admitted, which is the
// gate the C++ evaluator applies to an incoming judgment.
// RUN: %if uv %{ %uv python -m oracle.parity adaptive-carry %zkc-registry-dir/soundness-signature.json | FileCheck %s --check-prefix=TWIN-SHIPPED %}
// TWIN-SHIPPED: adaptive index: carried, and unadmitted by the vocabulary
// RUN: %if uv %{ %uv python -m oracle.parity adaptive-carry %t.widened.json | FileCheck %s --check-prefix=TWIN-WIDE %}
// TWIN-WIDE: adaptive quantification: carried

module {}
