// RUN: %python %S/../SemanticClosure/lib/artifact_handoff.py reset %t.one.artifacts
// RUN: zkc-seal %S/../Encoding/kzg-before.mlir %zkc-seal-full -o %t.one.artifacts > /dev/null
// RUN: %python %S/../SemanticClosure/lib/artifact_handoff.py stage %t.one.artifacts %t.one.mlirbc
// RUN: zkc-test-opt \
// RUN:   -test-pir-compiler-provider='protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json signature=%zkc-registry-dir/soundness-signature.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json source-artifact=%t.one.mlirbc expected-groups=1' \
// RUN:   %s -o /dev/null 2>&1 | FileCheck %s --check-prefix=ONE
// RUN: %python %S/../SemanticClosure/lib/artifact_handoff.py reset %t.two.artifacts
// RUN: zkc-seal %S/Inputs/kzg-two-groups.mlir %zkc-seal-full -o %t.two.artifacts > /dev/null
// RUN: %python %S/../SemanticClosure/lib/artifact_handoff.py stage %t.two.artifacts %t.two.mlirbc
// RUN: zkc-test-opt \
// RUN:   -test-pir-compiler-provider='protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json signature=%zkc-registry-dir/soundness-signature.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json source-artifact=%t.two.mlirbc expected-groups=2' \
// RUN:   %s -o /dev/null 2>&1 | FileCheck %s --check-prefix=TWO
// RUN: %python %S/../SemanticClosure/lib/artifact_handoff.py reset %t.routed.artifacts
// RUN: zkc-seal %S/Inputs/kzg-routed.mlir %zkc-seal-full -o %t.routed.artifacts > /dev/null
// RUN: %python %S/../SemanticClosure/lib/artifact_handoff.py stage %t.routed.artifacts %t.routed.mlirbc
// RUN: zkc-test-opt \
// RUN:   -test-pir-compiler-provider='protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json signature=%zkc-registry-dir/soundness-signature.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json source-artifact=%t.routed.mlirbc expected-groups=1 expect-routes=1' \
// RUN:   %s -o /dev/null 2>&1 | FileCheck %s --check-prefix=ROUTED

// ONE: PIR compiler semantics: HoleContracts identity exact
//
// Golden configured refs: the compiler-configuration preimage
// (registry/protocol-vocabulary.json and registry/construction-profiles.json
// through ProtocolEnvironment::compilerConfiguration) is identity-bearing.
// These values change exactly when a registry entry or the preimage
// construction changes; update them consciously in the same change.
// ONE-NEXT: configured semantics ref: sha256:707b116dcb55a13f1b6da41812d58cf8f887f01b5d78752b4ede14fbcf6dcf7b
// ONE-NEXT: configured family ref: sha256:2c7705f23ebf4e0375cd1a1adef78c94f64b74a398781c60a762b950b35f1fb0
// ONE-NEXT: configured domain ref: sha256:f661443a391df9ee5b192fd1cec8690d9847bc559e9fabf03442a2e21c39577e
// ONE-NEXT: PIR compiler admission: full environment exact
// ONE: PIR compiler one-group: identity + EB/DB + ARSDH
// ONE-NEXT: PIR compiler soundness: shared DERIVE, typed ceiling exact
// ONE-NEXT: PIR compiler objective: 96 -> 48 bytes
// ONE-NEXT: PIR compiler selection: EB/DB ordinal 1

// TWO: PIR compiler semantics: HoleContracts identity exact
// TWO-NEXT: configured semantics ref: sha256:
// TWO-NEXT: configured family ref: sha256:
// TWO-NEXT: configured domain ref: sha256:
// TWO-NEXT: PIR compiler admission: full environment exact
// TWO: PIR compiler two-group: 4 canonical combinations
// TWO-NEXT: PIR compiler namespace: second application uses checked survivors
// TWO-NEXT: PIR compiler multi-step: 192 -> 96 bytes
// TWO-NEXT: PIR compiler bounds: application and plan limits exact

// ROUTED: PIR compiler semantics: HoleContracts identity exact
// ROUTED-NEXT: configured semantics ref: sha256:
// ROUTED-NEXT: configured family ref: sha256:
// ROUTED-NEXT: configured domain ref: sha256:
// ROUTED-NEXT: PIR compiler admission: full environment exact
// ROUTED: PIR compiler one-group: identity + EB/DB + ARSDH
// ROUTED-NEXT: PIR compiler soundness: shared DERIVE, typed ceiling exact
// ROUTED-NEXT: PIR compiler objective: 96 -> 48 bytes
// ROUTED-NEXT: PIR compiler selection: EB/DB ordinal 1
// ROUTED-NEXT: PIR compiler routed successor: routes and HoleContract citation re-admitted
