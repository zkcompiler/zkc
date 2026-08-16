// RUN: not zkc-opt %pir-seal-full %s -split-input-file 2>&1 | FileCheck %s
//
// Adversarial matrix for ReductionClosureOK (`docs/spec/kernel.md` §4.1).
// Every case uses the current contract/check/material vocabulary and mutates
// one instance-level fact.
// Contract/version/profile/output/parameter shape is E320; the pre-existing
// kernel partitions remain E243 (dependency), E244 (membership), E245
// (challenge ownership), and E213 (contract-derived transcript prefix).

// An unknown contract has no local implication for the seal to judge. One
// owner says so: the battery used to repeat this lookup under its own id,
// which is why this expectation was written twice.
// CHECK-DAG: [zkc-E320] unknown reduction contract 'not-admitted'
pir.protocol "closure-unknown-contract" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %a = pir.slot %t0 "a" : "tg" in "bad" as "a"
  %t2, %c = pir.chal %t1 deps(%a : !pir.val<"tg">) "c" : "scalar" domain "closure.unknown.c" space "2305843009213693952"
  pir.end %t2
  %out = pir.reduce "bad" contract "not-admitted" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "negative"
}

// -----

// The contract, not the result spelling, owns the exact consumed profile.
// CHECK: [zkc-E320] input claim 0 must have profile 'opaque_relation'
pir.protocol "closure-shape" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %wrong = pir.instantiate "wrong" anchors {statement = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"} : !pir.claim<"sumcheck_evaluation">
  %t0 = pir.begin
  %t1, %a = pir.slot %t0 "a" : "tg" in "sig" as "a"
  %t2, %c = pir.chal %t1 deps(%a : !pir.val<"tg">) "c" : "scalar" domain "closure.shape.c" space "2305843009213693952"
  pir.end %t2
  %out = pir.reduce "sig" contract "sigma" (%wrong : !pir.claim<"sumcheck_evaluation">) deps(%c : !pir.val<"scalar">) checks {} anchors [{statement = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"}] -> !pir.claim<"schnorr_evaluation">
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "negative"
}

// -----

// A contract round generates its own prefix: every declared message is
// absorbed before that round's challenge.
// CHECK: [zkc-E213] message role 'm' is committed after its challenge
pir.protocol "closure-round-prefix" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %input = pir.instantiate "input" anchors {statement = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"} : !pir.claim<"sumcheck_evaluation">
  %t0 = pir.begin
  %t1, %m0 = pir.slot %t0 "m0" : "scalar" in "open" as "m"
  %t2, %c = pir.chal %t1 deps(%m0 : !pir.val<"scalar">) "c" : "scalar" domain "closure.prefix.c" space "2305843009213693952"
  %t3, %m1 = pir.slot %t2 "m1" : "scalar" in "open" as "m" idx 1
  pir.end %t3
  %out = pir.reduce "open" contract "evalopen" (%input : !pir.claim<"sumcheck_evaluation">) deps(%c : !pir.val<"scalar">) checks {} anchors [{commitment = "sha256:1111111111111111111111111111111111111111111111111111111111111111", point = "sha256:2222222222222222222222222222222222222222222222222222222222222222", value = "sha256:3333333333333333333333333333333333333333333333333333333333333333"}] -> !pir.claim<"single_opening">
  pir.residual %out : !pir.claim<"single_opening"> route "negative"
}

// -----

// Dependency kind and class are exact contract facts. An ordinary scalar
// object cannot occupy evalopen's challenge slot.
// CHECK: [zkc-E243] dependency 0 does not match role 'c'
pir.protocol "closure-dependency" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %input = pir.instantiate "input" anchors {statement = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"} : !pir.claim<"sumcheck_evaluation">
  %t0 = pir.begin
  %t1, %m0 = pir.slot %t0 "m0" : "scalar" in "open" as "m"
  %t2, %m1 = pir.slot %t1 "m1" : "scalar" in "open" as "m" idx 1
  %t3, %aux = pir.slot %t2 "aux" : "scalar"
  %t4, %c = pir.chal %t3 deps(%m0, %m1 : !pir.val<"scalar">, !pir.val<"scalar">) "c" : "scalar" domain "closure.dependency.c" space "2305843009213693952"
  pir.end %t4
  %out = pir.reduce "open" contract "evalopen" (%input : !pir.claim<"sumcheck_evaluation">) deps(%aux : !pir.val<"scalar">) checks {} anchors [{commitment = "sha256:1111111111111111111111111111111111111111111111111111111111111111", point = "sha256:2222222222222222222222222222222222222222222222222222222222222222", value = "sha256:3333333333333333333333333333333333333333333333333333333333333333"}] -> !pir.claim<"single_opening">
  pir.residual %out : !pir.claim<"single_opening"> route "negative"
}

// -----

// Message-role membership is exact, including its occurrence set. The
// multiplicity counts units: a counted slot occurrence contributes its
// declared count, so a scalar occurrence covers exactly one.
// CHECK: [zkc-E244] message role 'm' needs 2 unit(s), got 1
pir.protocol "closure-membership" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %input = pir.instantiate "input" anchors {statement = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"} : !pir.claim<"sumcheck_evaluation">
  %t0 = pir.begin
  %t1, %m0 = pir.slot %t0 "m0" : "scalar" in "open" as "m"
  %t2, %c = pir.chal %t1 deps(%m0 : !pir.val<"scalar">) "c" : "scalar" domain "closure.membership.c" space "2305843009213693952"
  pir.end %t2
  %out = pir.reduce "open" contract "evalopen" (%input : !pir.claim<"sumcheck_evaluation">) deps(%c : !pir.val<"scalar">) checks {} anchors [{commitment = "sha256:1111111111111111111111111111111111111111111111111111111111111111", point = "sha256:2222222222222222222222222222222222222222222222222222222222222222", value = "sha256:3333333333333333333333333333333333333333333333333333333333333333"}] -> !pir.claim<"single_opening">
  pir.residual %out : !pir.claim<"single_opening"> route "negative"
}

// -----

// One sampled challenge has one reduction owner until declared sharing lands.
// The left reduction is otherwise fully closed, so this reaches ownership
// rather than failing on unrelated material reconstruction.
// CHECK: [zkc-E245] priced challenge capability is already consumed by reduce 'left'
pir.protocol "closure-challenge-owner" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %left_input = pir.instantiate "left-input" anchors {statement = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"} : !pir.claim<"sumcheck_evaluation">
  %right_input = pir.instantiate "right-input" anchors {statement = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"} : !pir.claim<"sumcheck_evaluation">
  %t0 = pir.begin
  %t1, %lm0 = pir.slot %t0 "lm0" : "scalar" in "left" as "m"
  %t2, %lm1 = pir.slot %t1 "lm1" : "scalar" in "left" as "m" idx 1
  %t3, %rm0 = pir.slot %t2 "rm0" : "scalar" in "right" as "m"
  %t4, %rm1 = pir.slot %t3 "rm1" : "scalar" in "right" as "m" idx 1
  %t5, %c = pir.chal %t4 deps(%lm0, %lm1, %rm0, %rm1 : !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">, !pir.val<"scalar">) "c" : "scalar" domain "closure.owner.c" space "2305843009213693952"
  pir.end %t5
  %left_out = pir.reduce "left" contract "evalopen" (%left_input : !pir.claim<"sumcheck_evaluation">) deps(%c : !pir.val<"scalar">) checks {} anchors [{commitment = "sha256:1111111111111111111111111111111111111111111111111111111111111111", point = "sha256:2222222222222222222222222222222222222222222222222222222222222222", value = "sha256:3333333333333333333333333333333333333333333333333333333333333333"}] -> !pir.claim<"single_opening">
  %right_out = pir.reduce "right" contract "evalopen" (%right_input : !pir.claim<"sumcheck_evaluation">) deps(%c : !pir.val<"scalar">) checks {} anchors [{commitment = "sha256:4444444444444444444444444444444444444444444444444444444444444444", point = "sha256:2222222222222222222222222222222222222222222222222222222222222222", value = "sha256:5555555555555555555555555555555555555555555555555555555555555555"}] -> !pir.claim<"single_opening">
  pir.material_bind %lm0 to "sha256:1111111111111111111111111111111111111111111111111111111111111111" : !pir.val<"scalar">
  pir.material_bind %lm1 to "sha256:3333333333333333333333333333333333333333333333333333333333333333" : !pir.val<"scalar">
  pir.material_bind %c to "sha256:2222222222222222222222222222222222222222222222222222222222222222" : !pir.val<"scalar">
  pir.residual %left_out : !pir.claim<"single_opening"> route "negative.left"
  pir.residual %right_out : !pir.claim<"single_opening"> route "negative.right"
}

// -----

// A contract parameter surface is exact; omitted MaterialRefs are not defaults.
// CHECK: [zkc-E320] reduction parameter names do not exactly match contract 'sigma_dleq'
pir.protocol "closure-parameters" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:bba3f50128ba9db12704c2e35ac7966e21b9105c3c0b8a0ba0bfa83bdc02e18e"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %a0 = pir.slot %t0 "a0" : "tg" in "dleq" as "a"
  %t2, %a1 = pir.slot %t1 "a1" : "tg" in "dleq" as "a" idx 1
  %t3, %c = pir.chal %t2 deps(%a0, %a1 : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "closure.parameters.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "z" : "scalar"
  pir.end %t4
  %out = pir.reduce "dleq" contract "sigma_dleq" (%relation : !pir.claim<"opaque_relation">) deps(%c, %z : !pir.val<"scalar">, !pir.val<"scalar">) checks {} params {left_statement = "sha256:9b6cefd1e5cc69489e2d7f3c535e4685ce72a3127a7204cf80b8f5584c46b6e5"} anchors [{statement = "sha256:bba3f50128ba9db12704c2e35ac7966e21b9105c3c0b8a0ba0bfa83bdc02e18e"}] -> !pir.claim<"dleq_evaluation">
  pir.residual %out : !pir.claim<"dleq_evaluation"> route "negative"
}

// -----

// Removing the equation is a missing contract role, not a smaller proof.
// CHECK: [zkc-E321] body-check roles do not exactly match reduction contract 'sigma'
pir.protocol "closure-check-surface" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %a = pir.slot %t0 "a" : "tg" in "sig" as "a"
  %t2, %c = pir.chal %t1 deps(%a : !pir.val<"tg">) "c" : "scalar" domain "closure.surface.c" space "2305843009213693952"
  pir.end %t2
  %out = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "negative"
}

// -----

// A transparent check must equal the contract-owned normalized predicate.
// CHECK: [zkc-E322] body role 'equation' has the wrong transparent predicate
pir.protocol "closure-predicate" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "a" : "tg" in "sig" as "a"
  %t3, %c = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "closure.predicate.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "z" : "scalar"
  pir.check "wrong" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["in", 0], ["in", 0]]
  pir.end %t4
  %out = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "wrong"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "negative"
}

// -----

// The selected equation uses an unrelated commitment SSA value.
// CHECK: [zkc-E323] local SSA attachment does not match role 'commitment'
pir.protocol "closure-local-attachment" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "a" : "tg" in "sig" as "a"
  %t3, %other = pir.slot %t2 "other" : "tg"
  %t4, %c = pir.chal %t3 deps(%y, %a, %other : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "closure.local.c" space "2305843009213693952"
  %t5, %z = pir.slot %t4 "z" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%y, %other, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t5
  %out = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %y to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "negative"
}

// -----

// A MaterialBinding may exist and still bind the wrong semantic object.
// CHECK: [zkc-E323] material-reference attachment does not match role 'statement'
pir.protocol "closure-material-attachment" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "a" : "tg" in "sig" as "a"
  %t3, %c = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "closure.material.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "z" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %out = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %y to "sha256:0000000000000000000000000000000000000000000000000000000000000000" : !pir.val<"tg">
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "negative"
}

// -----

// Material-valued attachments refuse unresolved carrier values.
// CHECK: [zkc-E324] material expression value has no MaterialBinding
pir.protocol "closure-unresolved-material" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "a" : "tg" in "sig" as "a"
  %t3, %c = pir.chal %t2 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "closure.unresolved.c" space "2305843009213693952"
  %t4, %z = pir.slot %t3 "z" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t4
  %out = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "negative"
}

// -----

// Exact checks can hold while the contract's input/parameter identity fails.
// CHECK: [zkc-E325] an admitted material-identity constraint does not hold
pir.protocol "closure-constraint" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}, h = {class = "tg", value = "2077728439817762110"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:0000000000000000000000000000000000000000000000000000000000000000"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y1 = pir.bind %t0 "y1" : "tg" stage instance
  %t2, %y2 = pir.bind %t1 "y2" : "tg" stage instance
  %t3, %a1 = pir.slot %t2 "a1" : "tg" in "dleq" as "a"
  %t4, %a2 = pir.slot %t3 "a2" : "tg" in "dleq" as "a" idx 1
  %t5, %c = pir.chal %t4 deps(%y1, %y2, %a1, %a2 : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "closure.constraint.c" space "2305843009213693952"
  %t6, %z = pir.slot %t5 "z" : "scalar"
  pir.check "left" contract "zkc.check.schnorr-equation" (%y1, %a1, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.check "right" contract "zkc.check.schnorr-equation" (%y2, %a2, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "h"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t6
  %out = pir.reduce "dleq" contract "sigma_dleq" (%relation : !pir.claim<"opaque_relation">) deps(%c, %z : !pir.val<"scalar">, !pir.val<"scalar">) checks {left_equation = "left", right_equation = "right"} params {left_statement = "sha256:9b6cefd1e5cc69489e2d7f3c535e4685ce72a3127a7204cf80b8f5584c46b6e5", right_statement = "sha256:f9e684572cd9cab72656f35172689132378428b721c9da103116e814e9effb6a"} anchors [{statement = "sha256:0000000000000000000000000000000000000000000000000000000000000000"}] -> !pir.claim<"dleq_evaluation">
  pir.material_bind %y1 to "sha256:9b6cefd1e5cc69489e2d7f3c535e4685ce72a3127a7204cf80b8f5584c46b6e5" : !pir.val<"tg">
  pir.material_bind %y2 to "sha256:f9e684572cd9cab72656f35172689132378428b721c9da103116e814e9effb6a" : !pir.val<"tg">
  pir.residual %out : !pir.claim<"dleq_evaluation"> route "negative"
}

// -----

// Authored output descriptors are assertions checked against the constructor.
// CHECK: [zkc-E326] output 0 descriptor does not equal the contract constructor
pir.protocol "closure-output" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %input = pir.instantiate "input" anchors {statement = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"} : !pir.claim<"sumcheck_evaluation">
  %t0 = pir.begin
  %t1, %m0 = pir.slot %t0 "m0" : "scalar" in "open" as "m"
  %t2, %m1 = pir.slot %t1 "m1" : "scalar" in "open" as "m" idx 1
  %t3, %c = pir.chal %t2 deps(%m0, %m1 : !pir.val<"scalar">, !pir.val<"scalar">) "c" : "scalar" domain "closure.output.c" space "2305843009213693952"
  pir.end %t3
  %out = pir.reduce "open" contract "evalopen" (%input : !pir.claim<"sumcheck_evaluation">) deps(%c : !pir.val<"scalar">) checks {} anchors [{commitment = "sha256:0000000000000000000000000000000000000000000000000000000000000000", point = "sha256:2222222222222222222222222222222222222222222222222222222222222222", value = "sha256:3333333333333333333333333333333333333333333333333333333333333333"}] -> !pir.claim<"single_opening">
  pir.material_bind %m0 to "sha256:1111111111111111111111111111111111111111111111111111111111111111" : !pir.val<"scalar">
  pir.material_bind %m1 to "sha256:3333333333333333333333333333333333333333333333333333333333333333" : !pir.val<"scalar">
  pir.material_bind %c to "sha256:2222222222222222222222222222222222222222222222222222222222222222" : !pir.val<"scalar">
  pir.residual %out : !pir.claim<"single_opening"> route "negative"
}

// -----

// A body check is evidence for one reduction instance, even when its contract
// and predicate could be replayed against another instance.
// CHECK: [zkc-E327] check 'shared' already justifies another reduction
pir.protocol "closure-check-reuse" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %left_relation = pir.instantiate "left" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %right_relation = pir.instantiate "right" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y1 = pir.bind %t0 "y1" : "tg" stage instance
  %t2, %y2 = pir.bind %t1 "y2" : "tg" stage instance
  %t3, %a1 = pir.slot %t2 "a1" : "tg" in "left_sig" as "a"
  %t4, %a2 = pir.slot %t3 "a2" : "tg" in "right_sig" as "a"
  %t5, %c1 = pir.chal %t4 deps(%y1, %a1 : !pir.val<"tg">, !pir.val<"tg">) "c1" : "scalar" domain "closure.reuse.c1" space "2305843009213693952"
  %t6, %z1 = pir.slot %t5 "z1" : "scalar"
  %t7, %c2 = pir.chal %t6 deps(%y2, %a2 : !pir.val<"tg">, !pir.val<"tg">) "c2" : "scalar" domain "closure.reuse.c2" space "2305843009213693952"
  %t8, %z2 = pir.slot %t7 "z2" : "scalar"
  pir.check "shared" contract "zkc.check.schnorr-equation" (%y1, %a1, %c1, %z1 : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t8
  %left_out = pir.reduce "left_sig" contract "sigma" (%left_relation : !pir.claim<"opaque_relation">) deps(%c1 : !pir.val<"scalar">) checks {equation = "shared"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  %right_out = pir.reduce "right_sig" contract "sigma" (%right_relation : !pir.claim<"opaque_relation">) deps(%c2 : !pir.val<"scalar">) checks {equation = "shared"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.material_bind %y1 to "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47" : !pir.val<"tg">
  pir.residual %left_out : !pir.claim<"schnorr_evaluation"> route "negative.left"
  pir.residual %right_out : !pir.claim<"schnorr_evaluation"> route "negative.right"
}

// -----

// Slot membership is an exact partial map: two slots claiming the same
// (instance, role, idx) triple would let a later decoy shadow the occurrence
// every closure matcher binds, so the duplicate refuses outright.
// CHECK: [zkc-E244] duplicate occurrence: instance 'sig' role 'a' idx 0 is already bound
pir.protocol "closure-duplicate-membership" kappa {codecs = {scalar = "ts_be8", tg = "tg_be8"}, constants = {g = {class = "tg", value = "4"}}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "relation" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %y = pir.bind %t0 "y" : "tg" stage instance
  %t2, %a = pir.slot %t1 "a" : "tg" in "sig" as "a"
  %t3, %a2 = pir.slot %t2 "a_decoy" : "tg" in "sig" as "a"
  %t4, %c = pir.chal %t3 deps(%y, %a : !pir.val<"tg">, !pir.val<"tg">) "c" : "scalar" domain "closure.dup.c" space "2305843009213693952"
  %t5, %z = pir.slot %t4 "z" : "scalar"
  pir.check "equation" contract "zkc.check.schnorr-equation" (%y, %a, %c, %z : !pir.val<"tg">, !pir.val<"tg">, !pir.val<"scalar">, !pir.val<"scalar">) expr ["eq", ["g_exp", ["const", "g"], ["in", 3]], ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]]]
  pir.end %t5
  %out = pir.reduce "sig" contract "sigma" (%relation : !pir.claim<"opaque_relation">) deps(%c : !pir.val<"scalar">) checks {equation = "equation"} anchors [{statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"}] -> !pir.claim<"schnorr_evaluation">
  pir.residual %out : !pir.claim<"schnorr_evaluation"> route "negative"
}
