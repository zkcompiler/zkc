// RUN: zkc-opt %s | FileCheck %s

// The carrier names one ReductionContract and binds its semantic check roles
// to authored check labels. Labels remain readable in MLIR; the canonical encoding replaces them
// with event positions.

// CHECK-LABEL: pir.protocol "reduction-contract-carrier"
// CHECK: pir.check "proof" contract "zkc.check.example"
// CHECK: %[[OUT:.+]] = pir.reduce "step" contract "zkc.reduction.example"
// CHECK-SAME: checks {equation = "proof"} params {rounds = 1 : i64} anchors [{}]
// CHECK-SAME: -> !pir.claim<"schnorr_evaluation">
// CHECK: pir.residual %[[OUT]] : <"schnorr_evaluation"> route "test.unpriced"
pir.protocol "reduction-contract-carrier" policy "residual_artifact" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:fb0288872031fc4818c03a7253bd3a78de192d05e6bccd09ceabeda65b4d7c6f", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %value = pir.bind %t0 "value" : "scalar" stage instance
  pir.check "proof" contract "zkc.check.example" (%value : !pir.val<"scalar">)
  pir.end %t1
  %out = pir.reduce "step" contract "zkc.reduction.example" (%relation : !pir.claim<"opaque_relation">) checks {equation = "proof"} params {rounds = 1 : i64} anchors [{}] -> !pir.claim<"schnorr_evaluation">
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "test.unpriced"
}
