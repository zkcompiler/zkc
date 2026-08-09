// The hand-written canonical-encoding composite fixture for pir-link has one fused
// evaluation claim, two namespaced transcript segments, and an explicit
// unmodeled consumer obligation. Segmentation permits the second face's
// instance binding after the first face's challenge; no obsolete assert_eq
// discharge or executable OIR claim is retained.
// REQUIRES: uv

// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: FileCheck %s < %t.sealed
// The `segments` section is identity-bearing, and this is the only fixture
// that carries one — so it is the only place the section can be held to the
// reference twin. The canonical bytes used to be written here and never read
// again, which left that contribution to identity unguarded.
// RUN: zkc-translate --canonical %t.sealed -o %t.canonical
// RUN: %uv python -m oracle.parity encode linked > %t.canonical.oracle
// RUN: diff %t.canonical %t.canonical.oracle
// RUN: zkc-translate --id %t.sealed -o %t.id
// RUN: %uv python -m oracle.parity id linked > %t.id.oracle
// RUN: diff %t.id %t.id.oracle
// RUN: FileCheck %s --check-prefix=HASH < %t.id

// CHECK: pir.sealed "linked" id "[[ID:[0-9a-f]+]]"
// CHECK-SAME: segments [2]
// CHECK-SAME: policy "analysis_only_artifact"
// CHECK: domain "left.p.c"
// CHECK: domain "right.q.c"
// CHECK: pir.residual {{.*}} route "evaluation-terminal-not-modeled"
// HASH: {{^[0-9a-f]{64}$}}

pir.protocol "linked" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} segments [2] policy "analysis_only_artifact" {
  %evaluation = pir.instantiate "ev" anchors {statement = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"} : !pir.claim<"schnorr_evaluation">
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "X" : "tg" stage instance
  %t2, %c1 = pir.chal %t1 deps(%x : !pir.val<"tg">) "c1" : "scalar" domain "left.p.c" space "2305843009213693952"
  %t3, %y = pir.bind %t2 "Y" : "tg" stage instance
  %t4, %c2 = pir.chal %t3 deps(%y : !pir.val<"tg">) "c2" : "scalar" domain "right.q.c" space "2305843009213693952"
  pir.end %t4
  pir.residual %evaluation : !pir.claim<"schnorr_evaluation"> route "evaluation-terminal-not-modeled"
}
