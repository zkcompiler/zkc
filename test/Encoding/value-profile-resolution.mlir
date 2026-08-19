// A value profile resolves in the sealed vocabulary or the seal refuses.
//
// The marker on the type is what makes this possible. A single namespace,
// where a string is a profile when the registry happens to resolve it and a
// payload class otherwise, would read a mistyped profile name as a class
// nobody declared and seal it — the one failure a closed registry exists to
// prevent. So the resolution is explicit, and it fails closed.

// RUN: not zkc-opt %pir-seal-full %s 2>&1 | FileCheck %s
// CHECK: [zkc-E166] slot 'cols' names value profile 'no_such_profile'
// CHECK-SAME: which the sealed vocabulary does not declare

pir.protocol "unresolved_value_profile" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "air" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %cols = pir.slot %t0 "cols" : profile "no_such_profile"
  pir.end %t1
  pir.residual %relation : !pir.claim<"opaque_relation"> route "unmodeled"
}
