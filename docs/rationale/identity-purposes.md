# Each purpose of identity has its own relation; no one identifier serves them all

The binding chapter lists five
[identity purposes](../spec/realization/artifacts.md#identity-purposes): source
and captures, a live runtime object, an immutable preparation, probability
provenance and continuation authority. Each is compared inside the contract
that gives the comparison its meaning, and each boundary tracks only the
dependencies its own proposition uses. One identifier may serve several
interfaces only when every interface's law is established for its actual
referent and lifetime.

## Alternatives

**One universal generative identifier.** The purposes have different lifetimes,
and one identifier would have to obey all of them at once, entangling caches,
probability laws and publication policy that change independently. Two cases
show the difference. A cached immutable value
[remains valid](../spec/core/contracts.md#provider-rebinding) after a mutation
invalidates a live fact about the same object, and rebinding its provider is
sound only where the retained entries agree. An allocator's chosen name is
[fresh relative to its pool](../spec/profiles/compiler/factor-preparation.md#monotone-allocation-and-registration):
an empty pool beside a populated world can select a name that world already
uses, so pool freshness is not freshness in the world.

**Content digests only.** A digest identifies bytes under its own assumptions.
It carries no owner, world or generation for a live object and no installed
policy or ledger entry for an authority, so copying one digest cannot establish
those. A hash may index keys and speed up their comparison. It does not replace
equality of the full key or agreement of the providers behind it.

## Reason

Separate relations admit the reuse that is lawful and nothing more. An
immutable preparation outlives the mutable fact it was computed beside. An edit
to a definition outside a claim's
[interpretation closure](../spec/realization/artifacts.md#interpretation-closure)
leaves the claim standing. A native reference still has to resolve within its
declared world and lifetime, which
[storage and ownership](../spec/realization/representations.md#storage-and-ownership)
states as its own obligation.

## Reopen when

Two of the purposes are shown to have the same validity conditions on every
supported profile, so that the law of one identifier implies both. That pair
may then share an identifier; the other purposes stay separate.
