// RUN: zkc-opt '-pir-link=producer=prod consumer=cons %pir-link-authorities' %pir-seal-full \
// RUN:   '-pir-project=protocol=link(prod,cons) protocol-vocabulary=%zkc-registry-dir/protocol-vocabulary.json construction-profile-registry=%zkc-registry-dir/construction-profiles.json' \
// RUN:   %S/../Transforms/pir-link.mlir | FileCheck %s
//
// What a composed protocol's second coin binds.
//
// Composition raises a question no single protocol can ask: when the consumer
// derives a challenge, does the producer's material influence it? The three
// answers a composition can give are all coherent -- carry the whole lineage,
// carry a smaller domain identifier, or exclude provenance entirely -- and they
// differ in whether a proof for one composite can be replayed inside another.
//
// The answer is not in the challenge domain string. Link renames the two coins
// `left.producer.challenge` and `right.consumer.challenge`, and those prefixes
// are positional: they disambiguate two faces of one spine and would read the
// same whichever producer had been linked. Reading provenance off them would be
// reading a label rather than a binding.
//
// The answer is in the sponge. The checks below follow the state by SSA value
// across the segment seam: the producer's squeeze result is absorbed into the
// state the consumer's own values extend, and the consumer's squeeze consumes
// exactly that state. Nothing resets at the boundary.
//
// This is a falsifier, not an illustration, and it fails in a reachable world.
// A link that opened the consumer's segment from a fresh sponge -- which is
// what excluding provenance looks like when implemented -- would absorb the
// consumer's first value into an initial state rather than into `%out`, and the
// capture below would not match. So would a link that carried lineage only in
// the domain string.
//
// Projecting a composite also needs the `protocol` selector. Composition leaves
// the operands in the module beside their composite, and this fixture's producer
// only exports a claim, so projecting every seal refuses the module at zkc-E234
// for a protocol nobody asked to project. That refusal is why no composed
// protocol had been projected before.

// The producer's coin, over a state carrying only producer material.
// CHECK:      %[[S1:.*]] = oir.absorb %{{.*}}, %arg0
// CHECK-NEXT: %[[PROD:.*]], %{{.*}} = oir.squeeze %[[S1]] "left.challenge"
// CHECK-SAME:   domain "left.producer.challenge"

// The seam. The consumer's first value extends the producer's post-squeeze
// state; it does not start a new one.
// CHECK-NEXT: %[[S2:.*]] = oir.absorb %[[PROD]], %arg1
// CHECK-NEXT: %[[S3:.*]] = oir.absorb %[[S2]], %arg2
// CHECK-NEXT: %[[S4:.*]] = oir.absorb %[[S3]], %arg3

// The consumer's coin, over the state that transitively carries the producer's.
// CHECK-NEXT: %{{.*}}, %{{.*}} = oir.squeeze %[[S4]] "right.challenge"
// CHECK-SAME:   domain "right.consumer.challenge"

// One verifier face, carrying the consumer's check over the composite.
// CHECK:      oir.check_call "right.opening_check"
// CHECK-SAME:   kind "zkc.check.kzg-opening"
