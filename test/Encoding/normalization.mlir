// REQUIRES: uv

// RUN: zkc-opt %pir-seal-full %s | FileCheck %s

// The tie-break the encoder applies when two reduces are ready at once has no
// other cross-implementation witness: every other corpus entry has at most one
// reduce ready at a time, so the ready-set order and its key were fixed by the
// two implementations agreeing and by nothing else. Protocol "a" is that case,
// so it is held to the twin here.
// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: %python %S/../SemanticClosure/lib/first_sealed.py %t.sealed > %t.a.mlir
// RUN: zkc-translate --canonical %t.a.mlir -o %t.a.zkc
// RUN: %uv python -m oracle.parity encode two-ready-reduces > %t.a.oracle
// RUN: diff %t.a.zkc %t.a.oracle

// Transformer tails represent a dependency graph, not authored block order.
// Two independent sigma reductions therefore normalize by content before
// encoding. This property test uses explicit analysis residuals so only the
// reduction graph, rather than terminal-rule selection, is under comparison.
// CHECK: pir.sealed "a" id "[[TAIL:[0-9a-f]+]]"
// CHECK: pir.sealed "b" id "[[TAIL]]"

pir.protocol "a" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %left = pir.instantiate "left" anchors {contract = "sha256:f55ff16f66f43360266b95db6f8fec01d76031054306ae4a4b380598f6cfd114", statement = "sha256:e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc"} : !pir.claim<"opaque_relation">
  %right = pir.instantiate "right" anchors {contract = "sha256:7dc96f776c8423e57a2785489a3f9c43fb6e756876d6ad9a9cac4aa4e72ec193", statement = "sha256:ad328846aa18b32a335816374511cac1063c704b8c57999e51da9f908290a7a4"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %ya = pir.bind %t0 "ya" : "tg" stage instance
  %t2, %yb = pir.bind %t1 "yb" : "tg" stage instance
  %t3, %ma = pir.slot %t2 "ma" : "tg" in "ra" as "a"
  %t4, %ca = pir.chal %t3 deps(%ya, %ma : !pir.val<"tg">, !pir.val<"tg">) "ca" : "scalar" domain "a.c" space "2305843009213693952"
  %t5, %za = pir.slot %t4 "za" : "scalar"
  %t6, %mb = pir.slot %t5 "mb" : "tg" in "rb" as "a"
  %t7, %cb = pir.chal %t6 deps(%yb, %mb : !pir.val<"tg">, !pir.val<"tg">) "cb" : "scalar" domain "b.c" space "2305843009213693952"
  %t8, %zb = pir.slot %t7 "zb" : "scalar"
  pir.check "verify_a" contract "zkc.check.schnorr-equation" (%ya, %ma, %ca, %za : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.check "verify_b" contract "zkc.check.schnorr-equation" (%yb, %mb, %cb, %zb : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t8
  %ea = pir.reduce "ra" contract "sigma" (%left : !pir.claim<"opaque_relation">) deps(%ca : !pir.val<"scalar">) checks {equation = "verify_a"} anchors [{statement = "sha256:e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc"}] -> !pir.claim<"schnorr_evaluation">
  %eb = pir.reduce "rb" contract "sigma" (%right : !pir.claim<"opaque_relation">) deps(%cb : !pir.val<"scalar">) checks {equation = "verify_b"} anchors [{statement = "sha256:ad328846aa18b32a335816374511cac1063c704b8c57999e51da9f908290a7a4"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %ya to "sha256:e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc" : !pir.val<"tg">
  pir.material_bind %yb to "sha256:ad328846aa18b32a335816374511cac1063c704b8c57999e51da9f908290a7a4" : !pir.val<"tg">
  pir.residual %ea : !pir.claim<"schnorr_evaluation"> route "normalization.probe"
  pir.residual %eb : !pir.claim<"schnorr_evaluation"> route "normalization.probe"
}

pir.protocol "b" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %left = pir.instantiate "left" anchors {contract = "sha256:f55ff16f66f43360266b95db6f8fec01d76031054306ae4a4b380598f6cfd114", statement = "sha256:e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc"} : !pir.claim<"opaque_relation">
  %right = pir.instantiate "right" anchors {contract = "sha256:7dc96f776c8423e57a2785489a3f9c43fb6e756876d6ad9a9cac4aa4e72ec193", statement = "sha256:ad328846aa18b32a335816374511cac1063c704b8c57999e51da9f908290a7a4"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %ya = pir.bind %t0 "ya" : "tg" stage instance
  %t2, %yb = pir.bind %t1 "yb" : "tg" stage instance
  %t3, %ma = pir.slot %t2 "ma" : "tg" in "ra" as "a"
  %t4, %ca = pir.chal %t3 deps(%ya, %ma : !pir.val<"tg">, !pir.val<"tg">) "ca" : "scalar" domain "a.c" space "2305843009213693952"
  %t5, %za = pir.slot %t4 "za" : "scalar"
  %t6, %mb = pir.slot %t5 "mb" : "tg" in "rb" as "a"
  %t7, %cb = pir.chal %t6 deps(%yb, %mb : !pir.val<"tg">, !pir.val<"tg">) "cb" : "scalar" domain "b.c" space "2305843009213693952"
  %t8, %zb = pir.slot %t7 "zb" : "scalar"
  pir.check "verify_a" contract "zkc.check.schnorr-equation" (%ya, %ma, %ca, %za : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.check "verify_b" contract "zkc.check.schnorr-equation" (%yb, %mb, %cb, %zb : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t8
  %eb = pir.reduce "rb" contract "sigma" (%right : !pir.claim<"opaque_relation">) deps(%cb : !pir.val<"scalar">) checks {equation = "verify_b"} anchors [{statement = "sha256:ad328846aa18b32a335816374511cac1063c704b8c57999e51da9f908290a7a4"}] -> !pir.claim<"schnorr_evaluation">
  %ea = pir.reduce "ra" contract "sigma" (%left : !pir.claim<"opaque_relation">) deps(%ca : !pir.val<"scalar">) checks {equation = "verify_a"} anchors [{statement = "sha256:e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %ya to "sha256:e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc" : !pir.val<"tg">
  pir.material_bind %yb to "sha256:ad328846aa18b32a335816374511cac1063c704b8c57999e51da9f908290a7a4" : !pir.val<"tg">
  pir.residual %eb : !pir.claim<"schnorr_evaluation"> route "normalization.probe"
  pir.residual %ea : !pir.claim<"schnorr_evaluation"> route "normalization.probe"
}

// Challenge prerequisites are a set. Reordering the authored operand list
// must not move the canonical v4 identity. Terminal rules select checks by
// named roles rather than by an authored citation order.
// CHECK: pir.sealed "c" id "[[DEPS:[0-9a-f]+]]"
// CHECK: pir.sealed "d" id "[[DEPS]]"

pir.protocol "c" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:8b53639f152c8fc6ef30802fde462ba0be9cf085f7580dc69efd72e002abbb35", statement = "sha256:e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "a" : "tg"
  %t3, %challenge = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "normalization.c" space "2305843009213693952"
  pir.end %t3
  pir.residual %relation : !pir.claim<"opaque_relation"> route "normalization.probe"
}

pir.protocol "d" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:8b53639f152c8fc6ef30802fde462ba0be9cf085f7580dc69efd72e002abbb35", statement = "sha256:e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "a" : "tg"
  %t3, %challenge = pir.chal %t2 deps(%a, %y : !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "normalization.c" space "2305843009213693952"
  pir.end %t3
  pir.residual %relation : !pir.claim<"opaque_relation"> route "normalization.probe"
}
