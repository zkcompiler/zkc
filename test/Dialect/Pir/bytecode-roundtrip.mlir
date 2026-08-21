// RUN: zkc-opt --emit-bytecode %s -o %t.bc
// RUN: zkc-opt --verify-roundtrip %s
// RUN: not zkc-opt %t.bc 2>&1 | FileCheck %s --check-prefix=TEXT-ONLY
// TEXT-ONLY: zkc-opt accepts textual compiler IR only
// `--verify-roundtrip` exercises MLIR's in-memory text and bytecode paths.
// Public bytecode input is deliberately absent: persisted PIR must cross the
// artifact loader, which owns producer, dialect-version, shape, and id
// validation.
// The current bytecode major must preserve every identity-bearing carrier
// field: profile types, contract checks, rule bindings, and material
// attachments.

pir.protocol "bytecode_v4" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}} {
  %relation = pir.instantiate "root" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "tg" stage instance
  %t2, %a = pir.slot %t1 "a" : "tg" in "sigma" as "a"
  %t3, %ch = pir.chal %t2 deps(%x, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "sigma.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "z" : "scalar"
  // A value profile is identity-bearing: it selects a different encoded row
  // family, so a bytecode path that dropped the marker would turn a
  // commitment into an element of a class and move the artifact's id.
  %t4p, %committed = pir.slot %t4 "committed" : profile "logup_committed_column"
  %t4q, %bound = pir.bind %t4p "bound" : profile "logup_table" stage seal = "sha256:3f2a1c8d5e7b9046a2c1e8f4d6b0937518a4c2e0f9d7b5638a1c4e2f0d9b7563"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%x, %a, %ch, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4q
  %evaluation = pir.reduce "sigma" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%ch : !pir.val<"scalar">) checks {equation = "equation"} anchors [{}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %x to "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "equation"}
}
