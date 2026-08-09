// RUN: zkc-opt %pir-seal-full %s | FileCheck %s
//
// The segment-scoped statement-binding default (kernel.md 5.3):
// a two-segment spine may bind a later segment's statement after an
// earlier segment's challenges — each segment's bindings precede its
// OWN first challenge. The same body without the segment
// decomposition is the weak-FS shape (zkc-E214 negative in
// pir-seal-invalid.mlir); the decomposition is judgment-bearing and
// identity-bearing, so it rides the sealed artifact and its canonical encoding.
// Even an empty semantic-citation set resolves through the unified
// protocol-vocabulary authority.
//
// CHECK: pir.sealed "segmented"
// CHECK-SAME: segments [2]
pir.protocol "segmented" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} segments [2] {
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "tg" stage instance
  %t2, %c1 = pir.chal %t1 deps(%x : !pir.val<"tg">) "c1" : "scalar" domain "left.p.c" space "2305843009213693952"
  %t3, %y = pir.bind %t2 "y" : "tg" stage instance
  %t4, %c2 = pir.chal %t3 deps(%y : !pir.val<"tg">) "c2" : "scalar" domain "right.q.c" space "2305843009213693952"
  pir.end %t4
}
