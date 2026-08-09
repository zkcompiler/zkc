// RUN: not zkc-translate --id %s 2>&1 | FileCheck %s
// A routed sink reaches the encoder in open IR without passing through the seal
// battery. The encoder independently refuses route bytes outside the canonical
// domain instead of constructing JSON first.
// CHECK: string leaves the canonical encoding domain

pir.protocol "p" policy "residual_artifact" {
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.end %t0
  pir.residual %claim : !pir.claim<"opaque_relation"> route "caf\C3\A9"
}
