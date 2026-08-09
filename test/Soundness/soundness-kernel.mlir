// RUN: zkc-test-opt \
// RUN:   -test-soundness-kernel='signature=%zkc-registry-dir/soundness-signature.json' \
// RUN:   %s 2>&1 | FileCheck %s

// CHECK: soundness kernel declaration slice: PASS
// CHECK-NEXT: rules: 25 declared, 21 admitted
// CHECK-NEXT: reduction bindings: 18
// CHECK-NEXT: path bindings: 5
// CHECK-NEXT: zero-binding rules: 5
// CHECK-NEXT: heterogeneous FRI cases: fold, query
// CHECK-NEXT: refuted theorem remains declared: yes
// CHECK-NEXT: executable KZG preservation rules: 2
// CHECK-NEXT: body/index mutation refused: invalid_body_signature
// CHECK-NEXT: loss trees: exact
// CHECK-NEXT: invalid typed constant refused: yes
// CHECK-NEXT: unimplemented machine decider refused: yes
// CHECK-NEXT: unknown declaration field refused: yes
// CHECK-NEXT: binding to a declared rule refused: yes
// CHECK-NEXT: subject-relation mutation refused: invalid_subject_relation
// CHECK-NEXT: declarations carry their own content digests
// CHECK-NEXT: receipt overclaim refused: yes
// CHECK-NEXT: stray unmatched obligation refused: yes
// The analysis is named by this digest: it covers the schemas, the rules and
// the bindings, and nothing else. Correcting a citation must not make an
// artifact's analysis a different analysis.
// CHECK-NEXT: signature digest: sha256:4c00592e02b268365320906a76d36339a6346e0f8f51a1978aee5e815e6635f4

module {}
