// RUN: zkc-opt %s | zkc-opt | FileCheck %s
// Parse/print coverage for the v4 carrier: descriptor profiles, contract-backed
// checks, one material edge, a rule/check discharge, generic reductions, and
// honest routed residuals.

// A Schnorr-shaped terminal closure uses the admitted profile and contract
// identities. Registry interpretation remains a seal-time concern.
// CHECK-LABEL: pir.protocol "schnorr"
pir.protocol "schnorr" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}} {
  // CHECK: %[[REL:.+]] = pir.instantiate "dlog" anchors {{.*}} : <"opaque_relation">
  %relation = pir.instantiate "dlog" anchors {contract = "sha256:fb0288872031fc4818c03a7253bd3a78de192d05e6bccd09ceabeda65b4d7c6f", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  // CHECK-NEXT: %[[T0:.+]] = pir.begin
  %t0 = pir.begin
  // CHECK-NEXT: %[[T1:.+]], %[[X:.+]] = pir.bind %[[T0]] "x" : "tg" stage instance
  %t1, %x = pir.bind %t0 "x" : "tg" stage instance
  // CHECK-NEXT: %[[T2:.+]], %[[A:.+]] = pir.slot %[[T1]] "commit_A" : "tg" in "sigma" as "a"
  %t2, %a = pir.slot %t1 "commit_A" : "tg" in "sigma" as "a"
  // CHECK-NEXT: %[[T3:.+]], %[[CH:.+]] = pir.chal %[[T2]] deps(%[[X]], %[[A]] : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "schnorr.c" space "2305843009213693952"
  %t3, %ch = pir.chal %t2 deps(%x, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "schnorr.c" space "2305843009213693952"
  // CHECK-NEXT: %[[T4:.+]], %[[Z:.+]] = pir.slot %[[T3]] "resp_z" : "scalar"
  %t4, %z = pir.slot %t3 "resp_z" : "scalar"
  // CHECK-NEXT: pir.check "verify" contract "zkc.check.schnorr-equation"(%[[X]], %[[A]], %[[CH]], %[[Z]] : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr
  pir.check "verify" contract "zkc.check.schnorr-equation" (%x, %a, %ch, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  // CHECK-NEXT: pir.end %[[T4]]
  pir.end %t4
  // CHECK-NEXT: %[[EVAL:.+]] = pir.reduce "sigma" contract "sigma"(%[[REL]] : !pir.claim<"opaque_relation">) deps(%[[CH]] : !pir.val<"scalar">) checks {equation = "verify"} anchors [{}] -> !pir.claim<"schnorr_evaluation">
  %evaluation = pir.reduce "sigma" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%ch : !pir.val<"scalar">) checks {equation = "verify"} anchors [{}] -> !pir.claim<"schnorr_evaluation">
  // CHECK-NEXT: pir.material_bind %[[X]] to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : <"tg">
  pir.material_bind %x to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  // CHECK-NEXT: pir.discharge %[[EVAL]] : <"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "verify"}
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "verify"}
}

// The claim graph is a typed DAG. This structural example does not claim a
// terminal theorem: its last node is an explicit residual.
// CHECK-LABEL: pir.protocol "dag"
pir.protocol "dag" kappa {codecs = {scalar = "ts_be8"}} policy "residual_artifact" {
  // CHECK: %[[ROOT:.+]] = pir.instantiate "sum" anchors {{.*}} : <"opaque_relation">
  %root = pir.instantiate "sum" anchors {contract = "sha256:fb0288872031fc4818c03a7253bd3a78de192d05e6bccd09ceabeda65b4d7c6f", statement = "sha256:aea20ace0f8efd6c86b7088db29b833b872fe0a1403d84a9046e2b1d4ed1412b"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  // CHECK: pir.slot %{{.+}} "g1_0" : "scalar" in "sc" as "g1"
  %t1, %g10 = pir.slot %t0 "g1_0" : "scalar" in "sc" as "g1"
  // CHECK-NEXT: pir.slot %{{.+}} "g1_1" : "scalar" in "sc" as "g1" idx 1
  %t2, %g11 = pir.slot %t1 "g1_1" : "scalar" in "sc" as "g1" idx 1
  %t3, %g12 = pir.slot %t2 "g1_2" : "scalar" in "sc" as "g1" idx 2
  %t4, %c1 = pir.chal %t3 deps(%g10, %g11, %g12 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) "c1" : "scalar" domain "sum.c1" space "2305843009213693952"
  %t5, %g20 = pir.slot %t4 "g2_0" : "scalar" in "sc" as "g2"
  %t6, %g21 = pir.slot %t5 "g2_1" : "scalar" in "sc" as "g2" idx 1
  %t7, %g22 = pir.slot %t6 "g2_2" : "scalar" in "sc" as "g2" idx 2
  %t8, %c2 = pir.chal %t7 deps(%g20, %g21, %g22 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) "c2" : "scalar" domain "sum.c2" space "2305843009213693952"
  %t9, %open_c = pir.chal %t8 "open_c" : "scalar" domain "open.c" space "2305843009213693952"
  pir.end %t9
  // CHECK: %[[EVAL:.+]] = pir.reduce "sc" contract "sumcheck"(%[[ROOT]] : !pir.claim<"opaque_relation">) deps({{.*}}) checks {} anchors [{}] -> !pir.claim<"sumcheck_evaluation">
  %evaluation = pir.reduce "sc" contract "sumcheck" (%root : !pir.claim<"opaque_relation">) deps(%c1, %c2 : !pir.val<"scalar">, !pir.val<"scalar">) checks {} anchors [{}] -> !pir.claim<"sumcheck_evaluation">
  // CHECK-NEXT: %[[OPEN:.+]] = pir.reduce "open" contract "evalopen"(%[[EVAL]] : !pir.claim<"sumcheck_evaluation">) deps({{.*}}) checks {} anchors [{{.*}}] -> !pir.claim<"single_opening">
  %opening = pir.reduce "open" contract "evalopen" (%evaluation : !pir.claim<"sumcheck_evaluation">) deps(%open_c : !pir.val<"scalar">) checks {} anchors [{commitment = "sha256:c9256a263eaf9251bb2b10ec702ab192f7661351c8be76e0341503de862776a4", point = "sha256:a6c948c314f9ee69ae3accd8e7f801ad25975616cbde1fdab2a05d042728cf64", value = "sha256:4fbaa40d86f7755e1661aef783bd9f936c7e482111f15c0ac7fa826f7f83e7d6"}] -> !pir.claim<"single_opening">
  // CHECK-NEXT: pir.residual %[[OPEN]] : <"single_opening"> route "unproved.opening"
  pir.residual %opening : !pir.claim<"single_opening"> route "unproved.opening"
}

// The non-discharge sink vocabulary remains typed by descriptor profile.
// CHECK-LABEL: pir.protocol "routes"
pir.protocol "routes" policy "residual_artifact" {
  %left = pir.instantiate "left" anchors {contract = "sha256:fb0288872031fc4818c03a7253bd3a78de192d05e6bccd09ceabeda65b4d7c6f", statement = "sha256:e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc"} : !pir.claim<"opaque_relation">
  %mid = pir.instantiate "mid" anchors {contract = "sha256:fb0288872031fc4818c03a7253bd3a78de192d05e6bccd09ceabeda65b4d7c6f", statement = "sha256:ad328846aa18b32a335816374511cac1063c704b8c57999e51da9f908290a7a4"} : !pir.claim<"opaque_relation">
  %right = pir.instantiate "right" anchors {contract = "sha256:fb0288872031fc4818c03a7253bd3a78de192d05e6bccd09ceabeda65b4d7c6f", statement = "sha256:41242b9fae56fad4e6e77dfe33cb18d1c3fc583f988cf25ef9f2d9be0d440bbb"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %v = pir.slot %t0 "m" : "tg"
  pir.end %t1
  // CHECK: pir.export %{{.+}} : <"opaque_relation"> route "host.consensus"
  pir.export %left : !pir.claim<"opaque_relation"> route "host.consensus"
  // CHECK-NEXT: pir.assume %{{.+}} : <"opaque_relation"> route "trusted.setup"
  pir.assume %mid : !pir.claim<"opaque_relation"> route "trusted.setup"
  // CHECK-NEXT: pir.residual %{{.+}} : <"opaque_relation"> route "open.obligation"
  pir.residual %right : !pir.claim<"opaque_relation"> route "open.obligation"
}
