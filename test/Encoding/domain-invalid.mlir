// RUN: not zkc-translate --id %s 2>&1 | FileCheck %s
// The encoder is fail-closed on the encoding domain independently of
// the seal battery (defense in depth, kernel.md §3, item 4): identity is
// never computed over bytes the reference encoder could disagree on.
// Author labels are not identity-bearing, so this exercises an encoded
// semantic string: the payload class in a spine event.
// CHECK: string leaves the canonical encoding domain

pir.protocol "p" kappa {codecs = {tg = "tg_be8"}} {
  %t0 = pir.begin
  %t1, %m = pir.slot %t0 "m" : "caf\C3\A9"
  pir.end %t1
}
