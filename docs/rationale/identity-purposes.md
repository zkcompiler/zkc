# Identity depends on what is being identified

Artifact binding, live resource identity, immutable preparation, probability
provenance and continuation authority have different validity conditions. The
[binding contract](../spec/realization/artifacts.md#identity-purposes) distinguishes
them; the [artifact guide](../../lean/docs/guides/artifact-binding.md) explains their use.

## Why one identifier is insufficient

A content digest identifies bytes under its stated assumptions. It does not
grant permission to use a resource, establish a resource's live generation, or
show that two draws were independent. An authority also needs its installed
policy and actual ledger state. Copying a digest supplies none of those facts.

Lifetimes differ too. An immutable prepared value can remain valid after a
mutation invalidates a fact about a live object. Rebinding its provider is sound
only where retained entries agree. An allocator's name can be fresh in its own
pool and already present in another world. The reference
[allocation law](../../lean/docs/spec/profiles/compiler/factor-preparation.md#monotone-allocation-and-registration)
therefore states the pool and world relationship explicitly.

One universal identifier would couple otherwise independent caches, resource
lifetimes and disclosure policies. Separate relations let each boundary bind
only the dependencies its claim uses. A hash can accelerate key lookup; it does
not replace full-key equality or the required provider agreement.

The cost is several explicit binding checks instead of one universal comparison.
An identifier may serve more than one interface when its actual referent and
lifetime satisfy every interface's law. Separate purposes do not require
separate identifier formats when those laws coincide.
