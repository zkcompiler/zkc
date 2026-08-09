// RUN: zkc-opt %pir-seal-full %pir-project-full %s -split-input-file -verify-diagnostics
// Projection rejects endpoint shapes that are valid sealed protocols but
// cannot become verifier programs.

// expected-error @below {{[zkc-E232] kappa must name the 'sponge' axis for projection}}
pir.protocol "missing-sponge" kappa {codecs = {}, iv = "artifact-id"} {
  %t0 = pir.begin
  pir.end %t0
}

// -----

// A verifier endpoint with no check would accept every proof.
// expected-error @below {{[zkc-E234] empty verifier face: the projected program would carry no check and accept every proof}}
pir.protocol "empty-verifier" kappa {codecs = {}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  pir.end %t0
}
