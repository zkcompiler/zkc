# Exact artifact identity

Native execution uses exact identities at explicitly different boundaries.
An application authorizes a package, deployment or bundle with a digest obtained
from trusted compilation or distribution. Computing that digest from an unknown
received file does not authorize its contents.

Versioned tags identify format and construction families. During development,
zkc-owned versions stay at `0` under the [format version policy](../development/maintenance.md#format-versions).
A digest identifies exact bytes; it does not establish that a different build
interprets those bytes with the same semantics.

## Publication and invocation

| Identity | Binds |
|---|---|
| Entry package | Exact published `zkc.entry/0` bytes, including original/interface, compilation choices and selected artifact |
| Native deployment or joint bundle | Exact emitted envelope bytes and the executable, policy or schedule they contain |
| Native proof source | Exact retained UTF-8 mathematical source bytes under the proof profile |
| Invocation context | The selected policy's canonical public values, application context and authorized setup configuration |
| Relation Asset | Canonical relation contents, exact field and ordered layout under its data format |

Use [Entry execution](../language/entries.md) for package authorization and
[native proof execution](../spec/profiles/compiler/native-proofs.md) for the exact
source/deployment/root encodings. [Joint bundles](../spec/profiles/compiler/run.md)
have their own envelope digest and invocation contract. These identifiers are
not interchangeable.

Formatting, declaration changes or recompilation can change an exact source or
publication identity even when mathematical behavior is equivalent. Authorization
applies to the exact bytes selected by the trusted digest.

## Identity is not a proof

A digest binds content under its cryptographic assumption. It does not prove
source correspondence, relation satisfaction, setup integrity or kernel
correctness. Public data and setup authority must come from the application;
proof-supplied labels cannot authorize themselves.

The semantic [artifact laws](../spec/realization/artifacts.md) distinguish source,
runtime, preparation, probability and continuation identities by purpose. Their
independent formal results do not establish adequacy of the native byte encoding.
