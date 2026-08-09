// RUN: not zkc-opt %pir-seal-full %s -split-input-file 2>&1 | FileCheck %s
//
// General seal-negative matrix for the current carrier. Reduction-contract
// closure has its own adversarial matrix in reduction-closure-invalid.mlir;
// keeping it separate prevents unrelated schema diagnostics from becoming a
// de facto compatibility surface.

// CHECK: [zkc-E202] pir-seal accepts open pir.protocol roots only; pre-existing pir.sealed is never seal input
pir.sealed "authored" id "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" {
  %t0 = pir.begin
  pir.end %t0
}

// -----

// CHECK: [zkc-E202] pir-seal found no open pir.protocol to judge
module {
}

// -----

// CHECK: [zkc-E201] terminal route 'residual' is not permitted under policy 'closed_proof'
pir.protocol "closed-residual" {
  %claim = pir.instantiate "relation" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.end %t0
  pir.residual %claim : !pir.claim<"opaque_relation"> route "unmodeled"
}

// -----

// CHECK-DAG: [zkc-E211] dependency 'message' is unabsorbed
// CHECK-DAG: [zkc-E212] unabsorbed slot precedes challenge 'challenge'
pir.protocol "unbound-prefix" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %message = pir.slot %t0 "message" : "tg" unabsorbed
  %t2, %challenge = pir.chal %t1 deps(%message : !pir.val<"tg">) "challenge" : "scalar" domain "unbound.challenge" space "2305843009213693952"
  pir.end %t2
}

// -----

// CHECK: [zkc-E221] payload class 'scalar' has no codec in kappa.codecs
pir.protocol "missing-codec" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %message = pir.slot %t0 "message" : "scalar"
  pir.end %t1
}

// -----

// CHECK: [zkc-E222] unknown check contract 'zkc.check.unknown'
pir.protocol "unknown-contract" {
  %t0 = pir.begin
  pir.check "predicate" contract "zkc.check.unknown"
  pir.end %t0
}

// -----

// CHECK: [zkc-E224] unknown seal policy 'almost_closed'
pir.protocol "unknown-policy" policy "almost_closed" {
  %t0 = pir.begin
  pir.end %t0
}

// -----

// CHECK: [zkc-E225] unknown kappa axis 'flavor'
pir.protocol "unknown-axis" kappa {codecs = {}, flavor = "mild"} {
  %t0 = pir.begin
  pir.end %t0
}

// -----

// CHECK: [zkc-E227] seal-stage binding must carry an explicit value
pir.protocol "missing-seal-value" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %constant = pir.bind %t0 "constant" : "tg" stage seal
  pir.end %t1
}

// -----

// CHECK: [zkc-E226] expr input reference out of range
pir.protocol "bad-expression" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %statement = pir.bind %t0 "statement" : "tg" stage instance
  %t2, %commitment = pir.slot %t1 "commitment" : "tg"
  %t3, %challenge = pir.chal %t2 deps(%statement, %commitment : !pir.val<"tg">, !pir.val<"tg">) "challenge" : "scalar" domain "bad-expression.challenge" space "2305843009213693952"
  %t4, %response = pir.slot %t3 "response" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%statement, %commitment, %challenge, %response : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["in", 9], ["in", 0]]
  pir.end %t4
}

// -----

// CHECK: [zkc-E228] label leaves the canonical encoding domain (printable ASCII)
pir.protocol "non-ascii" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %message = pir.slot %t0 "caf\C3\A9" : "tg"
  pir.end %t1
}

// -----

// CHECK: [zkc-E228] protocol_name leaves the canonical encoding domain (printable ASCII)
pir.protocol "caf\C3\A9" {
  %t0 = pir.begin
  pir.end %t0
}

// -----

// CHECK: [zkc-E214] statement binding 'late' follows challenge 'challenge'
pir.protocol "late-binding" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %early = pir.bind %t0 "early" : "tg" stage instance
  %t2, %challenge = pir.chal %t1 deps(%early : !pir.val<"tg">) "challenge" : "scalar" domain "late-binding.challenge" space "2305843009213693952"
  %t3, %late = pir.bind %t2 "late" : "tg" stage instance
  pir.end %t3
}

// -----

// CHECK: [zkc-E215] segment starts must be strictly increasing event positions inside the spine
pir.protocol "bad-segments" kappa {codecs = {tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} segments [2] {
  %t0 = pir.begin
  %t1, %left = pir.bind %t0 "left" : "tg" stage instance
  %t2, %right = pir.bind %t1 "right" : "tg" stage instance
  pir.end %t2
}

// -----

// CHECK: [zkc-E216] challenge domain 'duplicate.domain' is already used by another challenge
pir.protocol "duplicate-domains" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %c1 = pir.chal %t0 "c1" : "scalar" domain "duplicate.domain" space "2305843009213693952"
  %t2, %c2 = pir.chal %t1 "c2" : "scalar" domain "duplicate.domain" space "2305843009213693952"
  pir.end %t2
}

// -----

// CHECK: [zkc-E229] kappa codec 'unknown_codec' is not in the construction-profile registry
pir.protocol "unknown-profile" kappa {codecs = {tg = "unknown_codec"}, iv = "artifact-id", sponge = "toy_duplex"} {
  %t0 = pir.begin
  %t1, %message = pir.slot %t0 "message" : "tg"
  pir.end %t1
}

// -----

// CHECK: [zkc-E247] claim profile 'opaque_relation' requires exactly its admitted anchor set
pir.protocol "missing-anchor" policy "analysis_only_artifact" {
  %claim = pir.instantiate "relation" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.end %t0
  pir.residual %claim : !pir.claim<"opaque_relation"> route "invalid-descriptor"
}

// -----

// A route instance citing an unresolved hole contract refuses (E223).
// CHECK: [zkc-E223] route instance 'commit' cites hole contract 'zkc.hole.unminted' that does not resolve
pir.protocol "routed" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} routes {instances = {commit = {contract = "zkc.hole.unminted", inputs = ["witness:w"]}}, witnesses = [["w", "sigma-witness"]]} {
  %relation = pir.instantiate "dlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "commit_A" : "tg" in "sig" as "a" binding "commit.0"
  %t3, %c = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "schnorr.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "resp_z" : "scalar"
  pir.check "verify" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "verify"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %y to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "verify"}
}

// -----

// A route reference to an unknown challenge refuses (E223).
// CHECK: [zkc-E223] route instance 'resp' input #0 references unknown challenge 'nope'
pir.protocol "routed" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} routes {instances = {commit = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}, resp = {contract = "zkc.hole.sigma-response", inputs = ["chal:nope", "commit.1"]}}, witnesses = [["w", "sigma-witness"]]} {
  %relation = pir.instantiate "dlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "commit_A" : "tg" in "sig" as "a" binding "commit.0"
  %t3, %c = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "schnorr.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "resp_z" : "scalar" binding "resp.0"
  pir.check "verify" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "verify"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %y to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "verify"}
}

// -----

// A binding whose value class disagrees with the slot refuses (E223).
// CHECK: [zkc-E223] slot 'commit_A' binding must name a value result of the slot's payload class
pir.protocol "routed" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} routes {instances = {commit = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "witness:w"]}, resp = {contract = "zkc.hole.sigma-response", inputs = ["chal:c", "commit.1"]}}, witnesses = [["w", "sigma-witness"]]} {
  %relation = pir.instantiate "dlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "commit_A" : "tg" in "sig" as "a" binding "resp.0"
  %t3, %c = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "schnorr.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "resp_z" : "scalar" binding "resp.0"
  pir.check "verify" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "verify"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %y to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "verify"}
}

// -----

// Route instances forming a dataflow cycle refuse (E223). The two
// instances feed each other's handle operands.
// CHECK: [zkc-E223] route instances form a dataflow cycle
pir.protocol "routed" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} routes {instances = {commit = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "other.1"]}, other = {contract = "zkc.hole.sigma-commit", inputs = ["const:g", "commit.1"]}}, witnesses = [["w", "sigma-witness"]]} {
  %relation = pir.instantiate "dlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "commit_A" : "tg" in "sig" as "a" binding "commit.0"
  %t3, %c = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "schnorr.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "resp_z" : "scalar"
  pir.check "verify" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "verify"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %y to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "verify"}
}

// -----

// A slot binding without a routes section has nothing to resolve
// against (E223).
// CHECK: [zkc-E223] slot 'commit_A' declares a binding but the protocol declares no routes
pir.protocol "routed" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} {
  %relation = pir.instantiate "dlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "commit_A" : "tg" in "sig" as "a" binding "commit.0"
  %t3, %c = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "schnorr.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "resp_z" : "scalar"
  pir.check "verify" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "verify"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %y to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "verify"}
}

// -----

// A hole cannot consume the slot whose value it must produce. The route DAG
// alone is acyclic, but the event is unavailable at the lazy materialization
// point (E223).
// CHECK: [zkc-E223] route instance 'commit' input #0 references event 'slot:commit_A' that is not earlier than its first materialization point
pir.protocol "routed-temporal-cycle" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} routes {instances = {commit = {contract = "zkc.hole.sigma-commit", inputs = ["slot:commit_A", "witness:w"]}}, witnesses = [["w", "sigma-witness"]]} {
  %relation = pir.instantiate "dlog" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "commit_A" : "tg" in "sig" as "a" binding "commit.0"
  %t3, %c = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "schnorr.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "resp_z" : "scalar"
  pir.check "verify" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %evaluation = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "verify"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %y to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.discharge %evaluation : !pir.claim<"schnorr_evaluation"> rule "zkc.terminal.schnorr-evaluation" checks {equation = "verify"}
}
