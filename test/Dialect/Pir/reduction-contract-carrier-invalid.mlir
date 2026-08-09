// RUN: zkc-opt %s -split-input-file -verify-diagnostics

// Reduction selectors resolve in the container's check-event namespace.
pir.protocol "unknown-reduction-check" policy "residual_artifact" {
  %claim = pir.instantiate "claim" anchors {contract = "sha256:fb0288872031fc4818c03a7253bd3a78de192d05e6bccd09ceabeda65b4d7c6f", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.end %t0
  // expected-error @below {{[zkc-E136] reduction role 'equation' selects unknown check 'missing'}}
  %out = pir.reduce "step" contract "zkc.reduction.example" (%claim : !pir.claim<"opaque_relation">) checks {equation = "missing"} anchors [{}] -> !pir.claim<"schnorr_evaluation">
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "test.unpriced"
}

// Cross-owner reuse is checked by registry-backed semantic closure, where the
// exact producer-output terminal exception can be distinguished.
