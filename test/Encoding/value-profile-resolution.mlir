// A value profile resolves in the sealed vocabulary or the seal refuses.
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
// OPERAND-SAME: operand of value profile 'logup_column_1024' is a commitment
// OPERAND-SAME: an operand slot declares a payload class rather than one

// A codec refusal names where the class came from. The class a profiled
// slot's material travels under is the profile's element class, which the
// author never wrote down, so quoting it alone would leave them to guess the
// connection.
// RUN: %python -c "import json,sys; d=json.load(open(sys.argv[1])); d['value_profiles']['uncodeced']={'arity_log2':10,'binding_route':'zkc.commit.toy-vector','element_class':'no_such_class','origin':'prover_message'}; json.dump(d, open(sys.argv[2],'w'))" %zkc-registry-dir/protocol-vocabulary.json %t.vocab.json
// RUN: %python -c "import sys; sys.stdout.write(open(sys.argv[1]).read().replace('logup_column_1024','uncodeced'))" %S/logup-bus.mlir > %t.uncodeced.mlir
// RUN: not zkc-opt -pir-seal='protocol-vocabulary=%t.vocab.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' %t.uncodeced.mlir 2>&1 \
// RUN:   | FileCheck %s --check-prefix=NOCODEC
// NOCODEC: [zkc-E221] payload class 'no_such_class' has no codec in kappa.codecs
// NOCODEC-SAME: it is the element class of value profile 'uncodeced'

// A profile's `origin` says who chose the content; the event carrying it
// says the same thing in the carrier's own terms — a slot is prover
// material, a public binding is material the statement fixes. They are one
// fact with two spellings, so an artifact whose profile claims one
// provenance while its transcript shows another is refused rather than
// sealed with the disagreement inside it.
// RUN: %python -c "import json,sys; d=json.load(open(sys.argv[1])); [p.update(origin='preprocessed') for p in d['value_profiles'].values()]; json.dump(d, open(sys.argv[2],'w'))" %zkc-registry-dir/protocol-vocabulary.json %t.origin.json
// RUN: not zkc-opt -pir-seal='protocol-vocabulary=%t.origin.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' %S/logup-bus.mlir 2>&1 \
// RUN:   | FileCheck %s --check-prefix=SEAT
// SEAT: [zkc-E169] value profile 'logup_column_1024' declares origin 'preprocessed'
// SEAT-SAME: does not belong on slot 'values'
// SEAT-SAME: that seat carries content of origin 'prover_message'
