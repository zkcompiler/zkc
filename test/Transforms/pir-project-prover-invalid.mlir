// Prover projection only accepts an admitted route graph that realizes every
// proof slot. Both refusals start from freshly sealed open protocols.
// RUN: zkc-opt %pir-seal-full %S/../Encoding/schnorr.mlir -o %t.unrouted.mlir
// RUN: not zkc-opt %pir-project-prover-full %t.unrouted.mlir 2>&1 | FileCheck --check-prefix=UNROUTED %s
// UNROUTED: [zkc-E239] prover projection requires construction routes

// RUN: sed 's/ binding "resp.0"//' %S/../Encoding/routed-schnorr.mlir > %t.partial.open.mlir
// RUN: zkc-opt %pir-seal-full %t.partial.open.mlir -o %t.partial.sealed.mlir
// RUN: not zkc-opt %pir-project-prover-full %t.partial.sealed.mlir 2>&1 | FileCheck --check-prefix=PARTIAL %s
// PARTIAL: [zkc-E239] prover projection requires a construction route for every slot; unbound: 'resp_z'
