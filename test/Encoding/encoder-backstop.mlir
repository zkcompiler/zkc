// RUN: not zkc-translate --id %s 2>&1 | FileCheck %s
// The encoder is total on out-of-domain content (kernel.md §3, item 4,
// validate-before-build): a non-ASCII string reached through a path
// the seal battery has not judged (the tool also accepts open protocols) is a
// clean error, never a trap inside canonical JSON construction.
// CHECK: string leaves the canonical encoding domain
pir.protocol "p" kappa {iv = "caf\C3\A9"} {
  %t0 = pir.begin
  pir.end %t0
}
