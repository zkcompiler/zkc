// RUN: zkc-test-opt -test-sealed-guard %s 2>&1 | FileCheck %s
// RUN: zkc-test-opt -test-sealed-guard %s --remarks-filter-failed=zkc-guard 2>&1 | FileCheck %s --check-prefix=ENGINE
// Sealing enforcement, layer two (docs/spec/carrier.md §3): the guard
// refuses pattern application rooted under a sealed artifact — audited,
// never silent. Without a remark engine the audit is a plain
// diagnostic; with one (the upstream --remarks-* flags) it is a
// structured failure remark under the zkc-guard category
// (carrier.md §5).

// ENGINE: Failure
// ENGINE-SAME: zkc-guard
// ENGINE-SAME: pattern application refused under sealed protocol 'shut'

// CHECK: sealed-protocol guard refused a pattern application
pir.protocol "open" {
  %t0 = pir.begin
  // CHECK: pir.slot %{{.+}} "rewritten"
  %t1, %v = pir.slot %t0 "marker" : "tg"
  pir.end %t1
}

pir.sealed "shut" id "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" {
  %t0 = pir.begin
  // CHECK: pir.slot %{{.+}} "marker"
  %t1, %v = pir.slot %t0 "marker" : "tg"
  pir.end %t1
}
