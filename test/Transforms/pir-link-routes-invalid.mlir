// A handle has one consuming reader in the construction DAG. The link engine
// judges each input before composing it, so a duplicated witness reader is
// refused rather than copied into a larger graph.
// RUN: not zkc-opt '-pir-link=producer=bad-handles consumer=plain %pir-link-authorities' %s 2>&1 | FileCheck %s --check-prefix=HANDLE
// HANDLE: [zkc-E223] route instance 'second' input #1 gives handle 'witness:w' more than one reader

// Handle-valued instance results obey the same linear reader rule.
// RUN: not zkc-opt '-pir-link=producer=bad-result consumer=plain %pir-link-authorities' %s 2>&1 | FileCheck %s --check-prefix=RESULT-HANDLE
// RESULT-HANDLE: [zkc-E223] route instance 'b.response' input #1 gives handle 'commit.1' more than one reader

// Linking requires the same authorities as sealing because it judges both
// inputs and the complete open result.
// RUN: not zkc-opt '-pir-link=producer=plain consumer=other' %s 2>&1 | FileCheck %s --check-prefix=AUTHORITY
// AUTHORITY: [zkc-E248] pir-link requires a protocol-vocabulary authority

// The producer is valid under analysis policy, but its residual is not valid
// under the consumer's closed policy. This failure occurs after the composite
// has been built. The IR dump after failure contains only the original roots:
// the transactional engine erased the rejected composite.
// RUN: not zkc-opt '-pir-link=producer=residual-prod consumer=closed-cons %pir-link-authorities' -mlir-print-ir-after-failure %s 2>&1 | FileCheck %s --check-prefix=TRANSACTION
// TRANSACTION: [zkc-E201]
// TRANSACTION-LABEL: IR Dump After PirLink
// TRANSACTION-NOT: pir.protocol "link(residual-prod,closed-cons)"

pir.protocol "bad-handles"
    kappa {codecs = {tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {first = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}, second = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}}, witnesses = [["w", "sigma-witness"]]} {
  %t0 = pir.begin
  pir.end %t0
}

pir.protocol "plain" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "tg" stage instance
  pir.end %t1
}

pir.protocol "bad-result"
    kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {a.response = {contract = "zkc.hole.sigma-response", inputs = ["chal:c", "commit.1"]}, b.response = {contract = "zkc.hole.sigma-response", inputs = ["chal:c", "commit.1"]}, commit = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}}, witnesses = [["w", "sigma-witness"]]} {
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "tg" stage instance
  %t2, %c = pir.chal %t1 deps(%x : !pir.val<"tg">) "c" : "scalar" domain "bad.result" space "2305843009213693952"
  pir.end %t2
}

pir.protocol "other" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "tg" stage instance
  pir.end %t1
}

pir.protocol "residual-prod"
    kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"}
    policy "analysis_only_artifact" {
  %claim = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "tg" stage instance
  pir.end %t1
  pir.residual %claim : !pir.claim<"opaque_relation"> route "analysis"
}

pir.protocol "closed-cons" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %x = pir.bind %t0 "x" : "tg" stage instance
  pir.end %t1
}
