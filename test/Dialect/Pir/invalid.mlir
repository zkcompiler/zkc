// RUN: zkc-opt %s -split-input-file -verify-diagnostics --allow-unregistered-dialect
// Current container diagnostics. Every example uses profile claim types,
// contract checks, rule/check discharges, and the material-attachment phase.

// Foreign operations are not protocol members (E131).
pir.protocol "foreign" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E131] is not a protocol member}}
  "test.foreign"() : () -> ()
  pir.end %t0
}

// -----

// Sources cannot appear after the spine head (E132).
pir.protocol "late_source" policy "residual_artifact" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E132] claim source after the spine head}}
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  pir.end %t0
  pir.residual %claim : !pir.claim<"opaque_relation"> route "late.source"
}

// -----

// Every body has one completed spine (E132).
// expected-error @below {{[zkc-E132] body must run [sources]* begin [events]* end [reduces]* [attachments]* [sinks]*; the spine never ends}}
pir.protocol "unterminated" {
  %t0 = pir.begin
}

// -----

// Spine events stay between begin and end (E132).
pir.protocol "late_check" {
  %t0 = pir.begin
  pir.end %t0
  // expected-error @below {{[zkc-E132] spine event outside begin/end}}
  pir.check "predicate" contract "zkc.check.relation-predicate" semantic_args {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"}
}

// -----

// Transformers occur only after end (E132).
pir.protocol "early_reduce" policy "residual_artifact" {
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  // expected-error @below {{[zkc-E132] transformer before the spine ends}}
  %out = pir.reduce "sigma" contract "sigma" (%claim : !pir.claim<"opaque_relation">) checks {} anchors [{}] -> !pir.claim<"schnorr_evaluation">
  pir.end %t0
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "early.reduce"
}

// -----

// Material attachments occur only after end (E132).
pir.protocol "early_material" {
  %t0 = pir.begin
  %t1, %value = pir.slot %t0 "value" : "fr"
  // expected-error @below {{[zkc-E132] material attachment before the spine ends}}
  pir.material_bind %value to "sha256:1111111111111111111111111111111111111111111111111111111111111111" : !pir.val<"fr">
  pir.end %t1
}

// -----

// The tail phase is reductions, then material attachments, then sinks (E132).
pir.protocol "reduce_after_material" policy "residual_artifact" {
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %value = pir.slot %t0 "value" : "fr"
  pir.end %t1
  pir.material_bind %value to "sha256:1111111111111111111111111111111111111111111111111111111111111111" : !pir.val<"fr">
  // expected-error @below {{[zkc-E132] transformer after a material attachment}}
  %out = pir.reduce "sigma" contract "sigma" (%claim : !pir.claim<"opaque_relation">) checks {} anchors [{}] -> !pir.claim<"schnorr_evaluation">
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "late.reduce"
}

// -----

// Material attachments cannot follow a sink (E132).
pir.protocol "material_after_sink" policy "residual_artifact" {
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %value = pir.slot %t0 "value" : "fr"
  pir.end %t1
  pir.residual %claim : !pir.claim<"opaque_relation"> route "done"
  // expected-error @below {{[zkc-E132] material attachment after a terminal sink}}
  pir.material_bind %value to "sha256:1111111111111111111111111111111111111111111111111111111111111111" : !pir.val<"fr">
}

// -----

// Threading must equal block order (E133).
pir.protocol "broken_thread" {
  %t0 = pir.begin
  %t1, %a = pir.slot %t0 "a" : "tg"
  // expected-error @below {{[zkc-E133] does not consume the live thread}}
  %t2, %b = pir.slot %t0 "b" : "tg"
  pir.end %t1
}

// -----

// Labels are unique and non-empty (E134).
pir.protocol "duplicate_label" {
  %t0 = pir.begin
  %t1, %a = pir.slot %t0 "m" : "tg"
  // expected-error @below {{[zkc-E134] duplicate label 'm'}}
  %t2, %b = pir.slot %t1 "m" : "tg"
  pir.end %t2
}

// -----

pir.protocol "empty_label" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E134] label must not be empty}}
  %t1, %a = pir.slot %t0 "" : "tg"
  pir.end %t1
}

// -----

// Claims neither disappear nor fan out (E135).
pir.protocol "dropped_claim" {
  // expected-error @below {{[zkc-E135] claim is never routed}}
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.end %t0
}

// -----

pir.protocol "fanned_claim" policy "residual_artifact" {
  // expected-error @below {{[zkc-E135] claim is consumed more than once}}
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.end %t0
  pir.residual %claim : !pir.claim<"opaque_relation"> route "left"
  pir.residual %claim : !pir.claim<"opaque_relation"> route "right"
}

// -----

// Discharge role values select declared check labels (E136).
pir.protocol "unknown_check" {
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.end %t0
  // expected-error @below {{[zkc-E136] terminal role 'predicate' selects unknown check 'nope'}}
  pir.discharge %claim : !pir.claim<"opaque_relation"> rule "zkc.terminal.relation-direct" checks {predicate = "nope"}
}

// -----

// Sealed ids have one spelling (E137).
// expected-error @below {{[zkc-E137] id must be a 64-lowercase-hex SHA-256 digest}}
pir.sealed "bad_id" id "deadbeef" {
  %t0 = pir.begin
  pir.end %t0
}

// -----

// The old origin-as-payload pseudo-class is retired on wire producers (E138).
pir.protocol "reserved_chal" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E138] payload class 'chal' is retired; name the semantic payload class}}
  %t1, %value = pir.slot %t0 "value" : "chal"
  pir.end %t1
}

// -----

// A challenge also names semantic payload, while the op carries origin (E145).
pir.protocol "challenge_pseudo_class" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E145] payload class 'chal' is retired: a challenge must name its semantic payload class}}
  %t1, %challenge = pir.chal %t0 "c" : "chal" domain "d" space "17"
  pir.end %t1
}

// -----

pir.protocol "empty_challenge_class" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E145] challenge payload class must be non-empty}}
  %t1, %challenge = pir.chal %t0 "c" : "" domain "d" space "17"
  pir.end %t1
}

// -----

// The interface identifies the exact SSA result and its reported semantic
// class; another result of the same producer is not challenge-origin.
pir.protocol "mismatched_challenge_result" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E145] challenge capability value must have type !pir.val<"scalar">}}
  %t1:2 = "pir.chal"(%t0) <{domain = "d", label = "c", mode = [], payload_class = "scalar", space = "17"}> : (token) -> (token, !pir.val<"fr">)
  pir.end %t1#0
}

// -----

// Challenge cardinalities and vector modes are canonical (E139/E140).
pir.protocol "bad_space" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E139] space is the exact sample-space cardinality as a minimal decimal string, got "061"}}
  %t1, %challenge = pir.chal %t0 "c" : "scalar" domain "d" space "061"
  pir.end %t1
}

// -----

pir.protocol "bad_vector" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E140] a vector challenge mode is}}
  %t1, %challenge = pir.chal %t0 "c" : "scalar" domain "d" space "17" mode ["vector", "1", "uniform_independent"]
  pir.end %t1
}

// -----

pir.protocol "oversized_vector" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E145] challenge capability count must be a canonical decimal from 1 through 2^20}}
  %t1, %challenge = pir.chal %t0 "c" : "query_index" domain "d" space "17" mode ["vector", "1048577", "uniform_independent"]
  pir.end %t1
}

// -----

// Membership names a real reduction and is complete (E151/E152).
pir.protocol "unknown_membership" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E151] membership references unknown reduce instance 'missing'}}
  %t1, %message = pir.slot %t0 "message" : "tg" in "missing" as "a"
  pir.end %t1
}

// -----

pir.protocol "partial_membership" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E152] membership needs an instance, a role, and a non-negative occurrence index}}
  %t1, %message = pir.slot %t0 "message" : "tg" in "sigma"
  pir.end %t1
}

// -----

// Dependency position is the sole role spelling (E152).
pir.protocol "double_role" policy "residual_artifact" {
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  // expected-error @below {{[zkc-E152] event is a dep operand of reduce 'sigma' and must not carry membership props}}
  %t1, %dependency = pir.slot %t0 "dependency" : "tg" in "sigma" as "a"
  pir.end %t1
  %out = pir.reduce "sigma" contract "sigma" (%claim : !pir.claim<"opaque_relation">) deps(%dependency : !pir.val<"tg">) checks {} anchors [{}] -> !pir.claim<"schnorr_evaluation">
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "double.role"
}

// -----

// A reduction is neither a source nor a sink (E153).
pir.protocol "empty_reduce" policy "residual_artifact" {
  %t0 = pir.begin
  pir.end %t0
  // expected-error @below {{[zkc-E153] a reduction consumes at least one claim and produces at least one}}
  %out = "pir.reduce"() <{label = "r", contract = "sigma", row = "zkc.ss.sigma", checks = {}, operandSegmentSizes = array<i32: 0, 0>}> : () -> !pir.claim<"schnorr_evaluation">
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "empty.reduce"
}

// -----

// Challenge dependencies are a set (E154).
pir.protocol "duplicate_dependency" {
  %t0 = pir.begin
  %t1, %message = pir.slot %t0 "message" : "tg"
  // expected-error @below {{[zkc-E154] duplicate challenge dependency: P_req is a set}}
  %t2, %challenge = pir.chal %t1 deps(%message, %message : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "d" space "17"
  pir.end %t2
}

// -----

// One check cannot impersonate two roles in one discharge (E155).
pir.protocol "duplicate_terminal_role" {
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.check "predicate" contract "zkc.check.relation-predicate" semantic_args {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"}
  pir.end %t0
  // expected-error @below {{[zkc-E155] check 'predicate' is selected for more than one terminal role}}
  pir.discharge %claim : !pir.claim<"opaque_relation"> rule "syntactic.rule" checks {left = "predicate", right = "predicate"}
}

// -----

// Anchors are digest-shaped semantic references (E156).
pir.protocol "bad_anchor" policy "residual_artifact" {
  // expected-error @below {{[zkc-E156] anchor 'contract' must be a sha256:-prefixed 64-lowercase-hex digest reference}}
  %claim = pir.instantiate "claim" anchors {contract = "c0ffee", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.end %t0
  pir.residual %claim : !pir.claim<"opaque_relation"> route "bad.anchor"
}

// -----

// Semantic maps are non-empty string maps (E157).
pir.protocol "bad_semantic_map" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E157] semantic_args must be a dictionary from non-empty role names to non-empty strings}}
  pir.check "predicate" contract "zkc.check.relation-predicate" semantic_args {statement = ""}
  pir.end %t0
}

// -----

// Semantic ids are non-empty (E158).
pir.protocol "empty_contract" {
  %t0 = pir.begin
  // expected-error @below {{[zkc-E158] check contract id must not be empty}}
  pir.check "predicate" contract ""
  pir.end %t0
}

// -----

pir.protocol "empty_rule" {
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.check "predicate" contract "zkc.check.relation-predicate"
  pir.end %t0
  // expected-error @below {{[zkc-E158] terminal rule id must not be empty}}
  pir.discharge %claim : !pir.claim<"opaque_relation"> rule "" checks {predicate = "predicate"}
}

// -----

// Material references have one digest spelling (E159).
pir.protocol "bad_material_ref" {
  %t0 = pir.begin
  %t1, %value = pir.slot %t0 "value" : "fr"
  pir.end %t1
  // expected-error @below {{[zkc-E159] semantic_ref must be a sha256:-prefixed 64-lowercase-hex digest reference}}
  pir.material_bind %value to "not-a-digest" : !pir.val<"fr">
}

// -----

// Material bindings are a partial function (E161).
pir.protocol "duplicate_value_binding" {
  %t0 = pir.begin
  %t1, %value = pir.slot %t0 "value" : "fr"
  pir.end %t1
  pir.material_bind %value to "sha256:1111111111111111111111111111111111111111111111111111111111111111" : !pir.val<"fr">
  // expected-error @below {{[zkc-E161] a verifier value may have at most one semantic material binding}}
  pir.material_bind %value to "sha256:2222222222222222222222222222222222222222222222222222222222222222" : !pir.val<"fr">
}

// -----

// Material references are reverse-injective (E162).
pir.protocol "duplicate_material_ref" {
  %t0 = pir.begin
  %t1, %left = pir.slot %t0 "left" : "fr"
  %t2, %right = pir.slot %t1 "right" : "fr"
  pir.end %t2
  pir.material_bind %left to "sha256:1111111111111111111111111111111111111111111111111111111111111111" : !pir.val<"fr">
  // expected-error @below {{[zkc-E162] semantic_ref 'sha256:1111111111111111111111111111111111111111111111111111111111111111' is already bound to another verifier value}}
  pir.material_bind %right to "sha256:1111111111111111111111111111111111111111111111111111111111111111" : !pir.val<"fr">
}

// -----

// Routed sinks carry an explicit, non-empty route reference (E158).
pir.protocol "empty_route" policy "residual_artifact" {
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.end %t0
  // expected-error @below {{[zkc-E158] terminal route reference must not be empty}}
  pir.residual %claim : !pir.claim<"opaque_relation"> route ""
}

// -----

pir.protocol "empty_export_route" policy "exportable_artifact" {
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.end %t0
  // expected-error @below {{[zkc-E158] terminal route reference must not be empty}}
  pir.export %claim : !pir.claim<"opaque_relation"> route ""
}

// -----

pir.protocol "empty_assume_route" policy "analysis_only_artifact" {
  %claim = pir.instantiate "claim" anchors {contract = "sha256:18ac3e7343f016890c510e93f935261169d9e3f565436429830faf0934f4f8e4", statement = "sha256:043a718774c572bd8a25adbeb1bfcd5c0256ae11cecf9f9c3f925d0e52beaf89"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.end %t0
  // expected-error @below {{[zkc-E158] terminal route reference must not be empty}}
  pir.assume %claim : !pir.claim<"opaque_relation"> route ""
}

// -----

// A reduction produces exactly one claim. The admitted vocabulary has always
// said so — its loader refuses a contract with a second output — but the
// carrier's variadic result list did not, so the positional pairing for a
// second result was reachable in principle and unreachable in fact. A seam
// gets a consumer or a typed refusal.
pir.protocol "two_produced" policy "residual_artifact" {
  %relation = pir.instantiate "r" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  pir.end %t0
  // expected-error @below {{[zkc-E157] a reduction produces exactly one claim, got 2}}
  %a, %b = "pir.reduce"(%relation) <{label = "pair", contract = "sigma", checks = {}, operandSegmentSizes = array<i32: 1, 0>}> : (!pir.claim<"opaque_relation">) -> (!pir.claim<"schnorr_evaluation">, !pir.claim<"schnorr_evaluation">)
  pir.residual %a : !pir.claim<"schnorr_evaluation"> route "one"
  pir.residual %b : !pir.claim<"schnorr_evaluation"> route "two"
}
