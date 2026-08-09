// RUN: not zkc-opt -pir-project='endpoint-kind=prover' %s 2>&1 | FileCheck %s
// Projection fails closed on an unknown endpoint before loading authorities or
// inspecting an input artifact.

// An endpoint kind projection does not know (zkc-E231); 'prover' is a
// never-allocated name — prover_skeleton itself is a known kind now.
// CHECK: [zkc-E231] unknown endpoint kind 'prover'
pir.sealed "p" id "005b623ffa380f83bc0004bd13b6366d13f297bb91101e078b8673b625416f22"
    kappa {codecs = {}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  pir.end %t0
}
