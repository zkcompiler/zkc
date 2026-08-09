// RUN: not zkc-translate --id %s 2>&1 | FileCheck %s
// Validate-before-build covers op-level fields, not only attribute
// trees: an invalid UTF-8 byte in a bind value is a clean refusal, never a
// trap inside canonical JSON construction. The identity tool deliberately
// accepts open protocols, so no seal judgment precedes this backstop.
// CHECK: string leaves the canonical encoding domain
pir.protocol "p" kappa {codecs = {tg = "tg_be8"}} {
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage seal = "\FF"
  pir.end %t1
}
