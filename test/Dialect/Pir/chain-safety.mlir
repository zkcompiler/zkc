// RUN: zkc-opt %s > %t.before
// RUN: zkc-opt -canonicalize -cse -sccp %s > %t.after
// RUN: diff %t.before %t.after
// Generic pipelines must preserve the v4 carrier byte-for-byte. Token
// threading protects order; ProtocolResource effects keep identical checks,
// reductions, material edges, and terminal routes alive and unmerged.

pir.protocol "chain_v4" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}} policy "residual_artifact" {
  %root = pir.instantiate "root" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %a = pir.slot %t0 "a" : "tg" in "sigma" as "a"
  // Identical propositions with distinct labels remain distinct events.
  pir.check "k1" contract "zkc.check.relation-predicate" semantic_args {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"}
  pir.check "k2" contract "zkc.check.relation-predicate" semantic_args {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"}
  %t2, %ch = pir.chal %t1 deps(%a : !pir.val<"tg">) "c" : "scalar" domain "sigma.c" space "2305843009213693952"
  pir.end %t2
  %evaluation = pir.reduce "sigma" contract "sigma" (%root : !pir.claim<"opaque_relation">) deps(%ch : !pir.val<"scalar">) checks {} anchors [{}] -> !pir.claim<"schnorr_evaluation">
  pir.residual %evaluation : !pir.claim<"schnorr_evaluation"> route "unproved.evaluation"
}
