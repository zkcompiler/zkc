// REQUIRES: uv
// RUN: zkc-opt %pir-seal-full %s -o %t.sealed
// RUN: zkc-translate --canonical %t.sealed -o %t.zkc
// RUN: %uv python -m oracle.parity encode vecchal > %t.oracle
// RUN: diff %t.zkc %t.oracle
// RUN: zkc-translate --id %t.sealed -o %t.zkc-id
// RUN: %uv python -m oracle.parity id vecchal > %t.oracle-id
// RUN: diff %t.zkc-id %t.oracle-id
// RUN: zkc-opt %pir-project-full %t.sealed > %t.projected
// RUN: zkc-translate --oir-canonical %t.projected -o %t.oir.zkc
// RUN: %uv python -m oracle.parity oir-encode vecchal > %t.oir.oracle
// RUN: diff %t.oir.zkc %t.oir.oracle
// RUN: zkc-translate --oir-id %t.projected -o %t.oir-id.zkc
// RUN: %uv python -m oracle.parity oir-id vecchal > %t.oir-id.oracle
// RUN: diff %t.oir-id.zkc %t.oir-id.oracle

// Twin of reference/oracle/witnesses.py's VECCHAL witness: SCHNORR with
// its scalar challenge replaced by the vector shape FRI's query round
// draws (the vector capability in docs/spec/kernel.md §1.5). The mode is a
// trailing encoding section, present only for a vector challenge. This test
// pins that the vector mode crosses the PIR v5 cross-implementation parity
// gate (carrier.md §6); OIR projection is tested separately as one counted
// squeeze. A count-16 value fills sixteen units of a check operand
// segment, never a scalar one, so the schnorr equation consumes its
// own scalar challenge and the vector rides checked-free. The
// counted unabsorbed slot after it is the read_vec/slot_vec families'
// own parity gate (docs/spec/carrier.md §7): response material read
// after the last challenge, no absorption, no length framing.
pir.protocol "vecchal" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %c = pir.instantiate "dlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "commit_A" : "tg"
  %t3, %q = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "q" : "scalar" domain "vec.q" space "1099511627776" mode ["vector", "16", "uniform_independent"]
  %t4, %ch = pir.chal %t3 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "vec.c" space "1099511627776"
  %t5, %z = pir.slot %t4 "resp_z" : "scalar"
  pir.check "verify" contract "zkc.check.schnorr-equation" (%y, %a, %ch, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  %t6, %vec = pir.slot %t5 "resp_vec" : "scalar" count "16" unabsorbed
  pir.end %t6
  pir.residual %c : !pir.claim<"opaque_relation"> route "vector-challenge-analysis"
}
