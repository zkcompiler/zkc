// RUN: zkc-opt %pir-seal-full %S/../Encoding/schnorr.mlir -o %t.sealed
// RUN: zkc-opt %pir-recheck-full %t.sealed -o /dev/null
// RUN: %python %S/../Oir/Inputs/rewrite-artifact-id.py pir.sealed %t.sealed %t.forged 0000000000000000000000000000000000000000000000000000000000000000
// RUN: not zkc-opt %pir-recheck-full %t.forged 2>&1 | FileCheck --check-prefix=IDENTITY %s
// RUN: sed 's/opaque_relation = "sha256:[0-9a-f]*"/opaque_relation = "sha256:0000000000000000000000000000000000000000000000000000000000000000"/' %t.sealed > %t.profile-tampered
// RUN: not zkc-opt %pir-recheck-full %t.profile-tampered 2>&1 | FileCheck --check-prefix=PROFILE %s
//
// A consumer re-runs the seal battery over the loaded artifact and holds
// every section of the single resolved-vocabulary stamp to its authority.
// Self-consistent text is insufficient when descriptor semantics have drifted.

// PROFILE: [zkc-E248] 'opaque_relation' content digest does not match the loaded registry
// IDENTITY: [zkc-E171] stored PIR artifact id does not match its canonical identity
