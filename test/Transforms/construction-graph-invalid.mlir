// RUN: %python %S/Inputs/construction_graph_vocabulary.py %zkc-registry-dir/protocol-vocabulary.json %t.vocabulary.json
// RUN: not zkc-opt -pir-seal='protocol-vocabulary=%t.vocabulary.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' %s -split-input-file 2>&1 | FileCheck %s

// The typed construction graph owns the exact HoleContract ABI checks that are
// independent of any current concrete supplier implementation.

// CHECK: [zkc-E223] route instance 'vector' must supply exactly 2 declared static and semantic parameter(s)
pir.protocol "missing-parameters"
    kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {vector = {contract = "zkc.hole.test-vector", inputs = ["bind:items", "witness:state"]}}, witnesses = [["state", "test-state"]]} {
  %t0 = pir.begin
  pir.end %t0
}

// -----

// CHECK: [zkc-E223] route instance 'vector' supplies 1 inputs, its contract 'zkc.hole.test-vector' declares 2 routed operand(s)
pir.protocol "wrong-arity"
    kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {vector = {contract = "zkc.hole.test-vector", inputs = ["witness:state"], params = {mode = "test", relation = "sha256:0000000000000000000000000000000000000000000000000000000000000000"}}}, witnesses = [["state", "test-state"]]} {
  %t0 = pir.begin
  pir.end %t0
}

// -----

// CHECK: [zkc-E223] route instance 'vector' input #0 count '1' disagrees with the contract operand count '2'
pir.protocol "wrong-count"
    kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {vector = {contract = "zkc.hole.test-vector", inputs = ["bind:items", "witness:state"], params = {mode = "test", relation = "sha256:0000000000000000000000000000000000000000000000000000000000000000"}}}, witnesses = [["state", "test-state"]]} {
  %t0 = pir.begin
  %t1, %items0 = pir.bind %t0 "items" : "tg" stage instance
  pir.end %t1
}

// -----

// Route declarations have their own ordered witness namespace. A duplicate is
// rejected before any reference can choose one declaration as its meaning.
// CHECK: [zkc-E223] routes witness label 'w' is duplicated
pir.protocol "ambiguous-witness"
    kappa {codecs = {tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {commit = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}}, witnesses = [["w", "sigma-witness"], ["w", "sigma-witness"]]} {
  %t0 = pir.begin
  pir.end %t0
}

// -----

// CHECK: [zkc-E223] slot 'out' binding output index is out of range for 'commit'
pir.protocol "result-out-of-range"
    kappa {codecs = {tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {commit = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}}, witnesses = [["w", "sigma-witness"]]} {
  %t0 = pir.begin
  %t1, %out = pir.slot %t0 "out" : "tg" binding "commit.2"
  pir.end %t1
}

// -----

// CHECK: [zkc-E223] route instance 'second' input #1 gives handle 'witness:w' more than one reader
pir.protocol "duplicate-handle-reader"
    kappa {codecs = {tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {first = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}, second = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}}, witnesses = [["w", "sigma-witness"]]} {
  %t0 = pir.begin
  pir.end %t0
}

// -----

// The root is materialized at the first slot. Its dependency reaches a
// challenge that is sampled only afterwards, so the indirect route refuses.
// CHECK: [zkc-E223] route instance 'late' input #0 references event 'chal:c' that is not earlier than its first materialization point
pir.protocol "transitive-future-event"
    kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {late = {contract = "zkc.hole.test-late", inputs = ["chal:c"]}, root = {contract = "zkc.hole.test-root", inputs = ["late.0"]}}} {
  %t0 = pir.begin
  %t1, %early = pir.slot %t0 "early" : "tg" binding "root.0"
  %t2, %c = pir.chal %t1 deps(%early : !pir.val<"tg">) "c" : "scalar" domain "transitive.c" space "2305843009213693952"
  pir.end %t2
}

// -----

// The witness seam: handle classes are admitted only through a cited
// contract's declared segments. A class no contract admits refuses here —
// new witness families enter by teaching a contract, never by loosening
// the route judgment.
// CHECK: [zkc-E223] route instance 'root' input #0 class 'off-family-state' disagrees with the contract operand class 'test-state'
pir.protocol "off-family-witness"
    kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"}
    routes {instances = {root = {contract = "zkc.hole.test-root", inputs = ["witness:state"]}}, witnesses = [["state", "off-family-state"]]} {
  %t0 = pir.begin
  pir.end %t0
}
