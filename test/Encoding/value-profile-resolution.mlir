// A value profile resolves in the sealed vocabulary or the seal refuses,
// on either seat a profile can sit on.
//
// The marker on the type is what makes this possible. A single namespace,
// where a string is a profile when the registry happens to resolve it and a
// payload class otherwise, would read a mistyped profile name as a class
// nobody declared and seal it — the one failure a closed registry exists to
// prevent. So the resolution is explicit, and it fails closed.

// RUN: not zkc-opt %pir-seal-full %s 2>&1 | FileCheck %s
// CHECK: [zkc-E166] value profile 'no_such_profile', named by slot 'cols'
// CHECK-SAME: is not declared by the sealed vocabulary

pir.protocol "unresolved_value_profile" kappa {codecs = {scalar = "ts_be8"}, iv = "artifact-id", sponge = "toy_duplex"} policy "analysis_only_artifact" {
  %relation = pir.instantiate "air" anchors {contract = "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", statement = "sha256:a8e0d4fd1cf2805185daf6d0f9234b21b842fefde3503dfd74d6919a109cdb47"} : !pir.claim<"opaque_relation">
  %t0 = pir.begin
  %t1, %cols = pir.slot %t0 "cols" : profile "no_such_profile"
  pir.end %t1
  pir.residual %relation : !pir.claim<"opaque_relation"> route "unmodeled"
}

// A commitment is not an element of the class its content is drawn from, so
// it satisfies no operand slot. Without this a value profile spelled like a
// payload class would stand in for one element of it: the check compares a
// declared class against the value's, and a profile name is not a class.
// RUN: not zkc-opt %pir-seal-full %S/Inputs/value-profile-as-operand.mlir 2>&1 \
// RUN:   | FileCheck %s --check-prefix=OPERAND
// OPERAND: [zkc-E302] operand sequence has 0 valid layouts
// OPERAND-SAME: operand of value profile 'logup_committed_column' is a commitment
// OPERAND-SAME: an operand slot declares a payload class rather than one

// A codec refusal names where the class came from. The class a profiled
// slot's material travels under is the profile's element class, which the
// author never wrote down, so quoting it alone would leave them to guess the
// connection.
// RUN: %python -c "import json,sys; d=json.load(open(sys.argv[1])); d['value_profiles']['uncodeced']={'arity_log2':10,'binding_route':'zkc.commit.toy-vector','element_class':'no_such_class','origin':'prover_message'}; json.dump(d, open(sys.argv[2],'w'))" %zkc-registry-dir/protocol-vocabulary.json %t.vocab.json
// RUN: %python -c "import sys; sys.stdout.write(open(sys.argv[1]).read().replace('logup_committed_column','uncodeced'))" %S/logup-bus.mlir > %t.uncodeced.mlir
// RUN: not zkc-opt -pir-seal='protocol-vocabulary=%t.vocab.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' %t.uncodeced.mlir 2>&1 \
// RUN:   | FileCheck %s --check-prefix=NOCODEC
// NOCODEC: [zkc-E221] payload class 'no_such_class' has no codec in kappa.codecs
// NOCODEC-SAME: it is the element class of value profile 'uncodeced'

// A profile's `origin` says who chose the content; the event carrying it
// says the same thing in the carrier's own terms — a slot is prover
// material, a public binding is material the statement fixes. They are one
// fact with two spellings, so an artifact whose profile claims one
// provenance while its transcript shows another is refused rather than
// sealed with the disagreement inside it. Both directions are exercised,
// because a family with only one seat could not tell whether the seal checks
// the agreement or merely the spelling it happens to see.
// RUN: %python -c "import json,sys; d=json.load(open(sys.argv[1])); d['value_profiles']['logup_committed_column']['origin']='preprocessed'; json.dump(d, open(sys.argv[2],'w'))" %zkc-registry-dir/protocol-vocabulary.json %t.slot.json
// RUN: not zkc-opt -pir-seal='protocol-vocabulary=%t.slot.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' %S/logup-bus.mlir 2>&1 \
// RUN:   | FileCheck %s --check-prefix=SLOTSEAT
// SLOTSEAT: [zkc-E169] value profile 'logup_committed_column' declares origin 'preprocessed'
// SLOTSEAT-SAME: does not belong on slot 'table'
// SLOTSEAT-SAME: that seat carries content of origin 'prover_message'

// RUN: %python -c "import json,sys; d=json.load(open(sys.argv[1])); d['value_profiles']['logup_table']['origin']='prover_message'; json.dump(d, open(sys.argv[2],'w'))" %zkc-registry-dir/protocol-vocabulary.json %t.bind.json
// RUN: not zkc-opt -pir-seal='protocol-vocabulary=%t.bind.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' %S/logup-range-check.mlir 2>&1 \
// RUN:   | FileCheck %s --check-prefix=BINDSEAT
// BINDSEAT: [zkc-E169] value profile 'logup_table' declares origin 'prover_message'
// BINDSEAT-SAME: does not belong on binding 'table'
// BINDSEAT-SAME: that seat carries content of origin 'preprocessed'

// And the contract states the same fact from its own side: a role whose
// source is a public binding admits no prover message, and the converse.
// A protocol where the two disagree has two answers to who chose the content.
// RUN: %python -c "import json,sys; d=json.load(open(sys.argv[1])); [m.pop('source',None) for r in d['reduction_contracts']['logup_range_check']['rounds'] for m in r['messages']]; json.dump(d, open(sys.argv[2],'w'))" %zkc-registry-dir/protocol-vocabulary.json %t.source.json
// RUN: not zkc-opt -pir-seal='protocol-vocabulary=%t.source.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' %S/logup-range-check.mlir 2>&1 \
// RUN:   | FileCheck %s --check-prefix=SOURCE
// SOURCE: [zkc-E244] message role 'table' is filled by a public binding
// SOURCE-SAME: contract declares it filled by a prover message

// A profiled seal-stage binding absorbs the digest of the content its profile
// describes, so the value carries its own material reference. Spelling it
// again as a material binding would be one fact in two places, and two places
// can disagree — the transcript would absorb one digest while the claim's
// anchor named another. The second spelling is not checked for agreement; it
// is refused, because nothing consumes it.
// RUN: not zkc-opt %pir-seal-full %S/Inputs/profiled-bind-bound-twice.mlir 2>&1 \
// RUN:   | FileCheck %s --check-prefix=TWICE
// TWICE: [zkc-E161] a verifier value may have at most one semantic material binding

// The value a profiled seal-stage binding absorbs is a material reference, so
// it answers to the rules every other one does. An empty value is not one:
// the transcript would absorb nothing in the table's place while a material
// binding grounded the anchor elsewhere, which is the drift the reference
// living in the value exists to prevent.
// RUN: not zkc-opt %pir-seal-full %S/Inputs/profiled-bind-empty-value.mlir 2>&1 \
// RUN:   | FileCheck %s --check-prefix=EMPTY
// EMPTY: [zkc-E159] a profiled seal-stage binding absorbs the digest

// And no two verifier values may name one material. Pointing the query
// column's binding at the table's digest would have a thousand-scalar prover
// column and a preprocessed table claim the same content — the refusal that
// guards material bindings, now guarding the reference a binding carries in
// itself.
// RUN: not zkc-opt %pir-seal-full %S/Inputs/profiled-bind-aliases-material.mlir 2>&1 \
// RUN:   | FileCheck %s --check-prefix=ALIAS
// ALIAS: [zkc-E162] semantic_ref
// ALIAS-SAME: reverse-injective

// A binding fills a contract role only when it is profiled. The scalar
// binding row carries no membership, so two artifacts that fill roles
// differently would encode alike and share one identity; the role is refused
// where the encoding cannot carry it rather than dropped where it cannot.
// RUN: not zkc-opt %pir-seal-full %S/Inputs/bare-bind-with-membership.mlir 2>&1 \
// RUN:   | FileCheck %s --check-prefix=BAREROLE
// BAREROLE: [zkc-E152] a binding carries reduction membership only when it is profiled

// The seat is only half the carrier's statement of who chose the content;
// the stage is the other half. Preprocessed content is fixed before any
// statement, so it does not ride a binding whose value arrives per statement
// — and the seat the arity hypothesis names for discharging it, the anchor's
// preimage, is not in an instance-stage transcript at all.
// RUN: not zkc-opt %pir-seal-full %S/Inputs/preprocessed-at-instance-stage.mlir 2>&1 \
// RUN:   | FileCheck %s --check-prefix=STAGE
// STAGE: [zkc-E169] value profile 'logup_table' declares origin 'preprocessed'
// STAGE-SAME: does not belong on an instance-stage binding

// And the fourth direction of the contract's own statement: a role the
// contract says a public binding fills, filled by a prover message.
// RUN: not zkc-opt %pir-seal-full %S/Inputs/bind-role-filled-by-slot.mlir 2>&1 \
// RUN:   | FileCheck %s --check-prefix=SLOTROLE
// SLOTROLE: [zkc-E244] message role 'table' is filled by a prover message
// SLOTROLE-SAME: contract declares it filled by a public binding

