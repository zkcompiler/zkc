// RUN: zkc-test-opt \
// RUN:   -test-soundness-kernel='signature=%zkc-registry-dir/soundness-signature.json' \
// RUN:   %s 2>&1 | FileCheck %s

// CHECK: soundness kernel declaration slice: PASS
// CHECK-NEXT: rules: 30 declared, 26 admitted
// CHECK-NEXT: reduction bindings: 30
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
// CHECK-NEXT: index variable binds once and instantiates: yes
// CHECK-NEXT: unbound conclusion variable refused: yes
// The analysis is named by this digest: it covers the schemas, the rules and
// the bindings, and nothing else. Correcting a citation must not make an
// artifact's analysis a different analysis.
// CHECK-NEXT: signature digest: sha256:8c607be76a689b4eefe5d0a919d16de0fe70d1c1648f883f3ef51f8f4fe85ca3

module {}
