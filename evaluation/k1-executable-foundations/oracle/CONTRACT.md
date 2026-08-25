# K1 independent oracle contract

> **Status:** Frozen K1 evaluation contract
> **Scope:** canonical Foundation values and disjoint typed identity constructors
> **Authority:** evaluation instrument; not a current zkc specification

This directory is an independently written oracle. It does not import the K1
reference evaluator or treat JSON, Python values, object insertion order, or a
carrier rendering of an identifier as semantic content.

## 1. Constitutional bootstrap

`FoundationMetaProfileV0`, named `zkc.foundation.meta.v0`, is an un-IDed
constitutional prior. It fixes the value grammar, framing, prior-meta domain,
SHA-256 construction, and the closed prior-meta kind set. This avoids asking an
identity profile or hash suite to identify itself.

The closed K1 prior-meta kinds are exactly:

```text
foundation.identity-profile
foundation.hash-suite
foundation.semantic-regime
```

Carrier and evaluator profiles are not content-addressed by K1. A semantic
module is not prior meta: it is an ordinary, regime-qualified semantic subject.
The frozen fixtures construct real identity-profile and hash-suite descriptors,
then use their exact `PriorMetaId` values as all ordinary identity axes.

## 2. Canonical value grammar

`u64(x)` is the eight-byte unsigned big-endian representation of `x`.
`frame(x) = u64(len(x)) || x`. Every length and ordinal must fit in an unsigned
64-bit integer.

| Value | Canonical bytes |
|---|---|
| Unit | `0x00` |
| False | `0x01` |
| True | `0x02` |
| Natural | `0x03 || u64(len(magnitude)) || magnitude` |
| Integer | `0x04 || sign || u64(len(magnitude)) || magnitude` |
| Bytes | `0x05 || u64(len(bytes)) || bytes` |
| Symbol | `0x06 || u64(len(ascii)) || ascii` |
| Sequence | `0x07 || u64(count) || frame(child_0) || ...` |
| Record | `0x08 || u64(count) || u64(ordinal_0) || frame(value_0) || ...` |
| Variant | `0x09 || u64(case_ordinal) || frame(payload)` |

Natural and integer magnitudes are minimal unsigned big-endian byte strings.
Zero is the one byte `0x00`; any other leading zero is noncanonical. Integer
sign is `0x00` for nonnegative and `0x01` for negative. Negative zero is
noncanonical. A Symbol is nonempty and every byte is in `0x21..0x7e`.

Record ordinals are strictly increasing. There is no semantic map or host
object constructor. A domain that needs a map or set defines it as a sorted,
duplicate-free Sequence in its own schema. Record ordinals, Variant cases, and
Sequence order are semantic.

## 3. JSON-lines fixture transport

Each input line is one JSON object. Duplicate keys and non-finite JSON numbers
are malformed. The `case`/`op` envelope is checked before operation support;
for a known operation, unknown request fields and missing fields are malformed.
Object member order is never read. Semantic records use an explicit ordered
`fields` array.

Values use these transport forms:

```json
{"tag":"unit"}
{"tag":"bool","value":false}
{"tag":"nat","value":"42"}
{"tag":"int","value":"-7"}
{"tag":"bytes","value":"00ff"}
{"tag":"symbol","value":"pir.core"}
{"tag":"seq","items":[VALUE, VALUE]}
{"tag":"record","fields":[{"ordinal":"0","value":VALUE}]}
{"tag":"variant","case":"2","value":VALUE}
```

Natural values, integer values, record ordinals, and variant cases are
canonical decimal strings with no leading zero, plus sign, whitespace, or
negative zero. Bytes are even-length lowercase hexadecimal. JSON is transport,
not the identity encoding.

Every request has `case`, `op`, `foundation_profile`, and optional `limits`.
The operations are:

- `encode(value)` and `decode(canonical_hex)`;
- `prior_meta_id(subject_kind, value)` and
  `verify_prior_meta_id(expected_subject_kind, value, content_id)`; and
- `content_id(identity_profile, hash_suite, subject_kind, semantic_regime,
  value)` and `verify_id(...)` with the same three expected typed axes.

The two identifier transports are disjoint. A `PriorMetaId` has exactly:

```json
{
  "id_type":"prior-meta",
  "foundation_profile":"zkc.foundation.meta.v0",
  "subject_kind":"foundation.semantic-regime",
  "digest":"64 lowercase hexadecimal characters"
}
```

A `SemanticContentId` has exactly:

```json
{
  "id_type":"semantic-content",
  "foundation_profile":"zkc.foundation.meta.v0",
  "identity_profile":PRIOR_META_ID_OF_KIND_IDENTITY_PROFILE,
  "hash_suite":PRIOR_META_ID_OF_KIND_HASH_SUITE,
  "subject_kind":"pir.core",
  "semantic_regime":PRIOR_META_ID_OF_KIND_SEMANTIC_REGIME,
  "digest":"64 lowercase hexadecimal characters"
}
```

There is no null regime and no optional-regime exception. Only the three closed
kinds can use `PriorMetaId`; none can use `SemanticContentId`. Every other kind,
including `foundation.semantic-module`, uses `SemanticContentId` and carries all
three exact typed axes. `id_type` and the nested reference kinds are checked;
coincident digest bytes never make unlike kinds interchangeable.

## 4. Exact identity bytes

For a prior-meta identifier `M`, define its nonsemantic-transport-independent
typed reference:

```text
PriorMetaRef(M) = frame(M.foundation_profile ASCII)
                  || frame(M.subject_kind ASCII)
                  || raw 32-byte M.digest
```

For canonical meta body `B` and closed meta kind `K`:

```text
Pmeta = "zkc/prior-meta-id/v0\0"
        || frame("zkc.foundation.meta.v0")
        || frame(K)
        || frame(B)

PriorMetaId.digest = SHA-256(Pmeta)
```

For ordinary semantic body `B`, identity-profile ID `I`, hash-suite ID `H`,
subject kind `K`, and semantic-regime ID `R`:

```text
Psemantic = "zkc/content-id/v0\0"
            || frame("zkc.foundation.meta.v0")
            || frame(PriorMetaRef(I))
            || frame(PriorMetaRef(H))
            || frame(K)
            || frame(PriorMetaRef(R))
            || frame(B)

SemanticContentId.digest = SHA-256(Psemantic)
```

The digest is excluded from its own preimage. The abstract structured tuple is
identity; JSON, text, bytecode, URI, and database-key spellings are carriers.
Exact tuple equality, evaluator support, and checked migration are separate.

The oracle supports only the frozen profile IDs:

```text
IdentityProfileId digest = 0764186d53048eb619e79783581331dd7ef7c3939215b8000239c94768237ac1
HashSuiteId digest       = c24b580c31bf26bf314e746c87a93cb7ff61d3c33880fbd0ad8e31b307110805
```

Their canonical descriptor bodies and the exact regime-root descriptor are in
`cases/requests.jsonl`; `cases/expected.jsonl` freezes their computed IDs. The
selected root has digest
`bfe22f86f4afc4ffaa79d7ec02db42f0c3fad30f6e6e81163cf21a52e05cce77`
and the following identity-bearing shape:

```text
Record {
  0: Symbol("zkc.foundation.portable-semantics.v0"),
  1: Nat(0),
  2: Record {
       0: Seq(
            unit, bool, nat, int, bytes, symbol, seq, record, variant,
            literal, variable, let, record-construct, project, inject, case,
            sequence-construct, sequence-length, fail, strict-index,
            bounded-append, primitive-call, bounded-iterate, conditional),
       1: Bytes(EXACT_SEMANTIC_CORE_LAW_SOURCE),
     },
  3: Seq(),
  4: Symbol("local-ordinals-and-closed-scc-v0"),
  5: Symbol("extension-modules-same-root-dag-v0"),
}
```

`EXACT_SEMANTIC_CORE_LAW_SOURCE` is an ASCII octet string with a final LF. It
is stored in full, as lowercase hexadecimal, in the `id-regime-root` request;
that frozen request is the exact oracle input rather than a prose
reconstruction. The installed source is 39,468 octets and has SHA-256 digest
`4c0115cb4301240c555e1484ce98863bd2f3400a1ac0cf456ff89248229452d3`.
It fixes the declaration-reference grammar and resolution law, declaration-
local type lifting, root and module value-domain support boundaries, exact
primitive declaration binding, derived direct primitive references,
`DirectModuleRoots`, `RequiredModuleClosure_B`, module authentication order,
term typing and evaluation, charging, and validation precedence. The complete
encoded regime descriptor is 40,383 octets and has SHA-256 digest
`e7fa336ad42e028d272f7eb870cc5a9213068253a74f07c710ae111da3205eb0`.
Because these exact octets are in the root preimage, they are authenticated
laws rather than prose names that an implementation may reinterpret.

The term grammar has one `bounded-iterate` constructor; map, fold, find,
pairwise traversal, and worklists are not independent core syntax. The root
does not import a same-regime semantic module. Exact primitives live in ordinary
semantic modules under that root; those modules import only earlier same-root
modules as a DAG, and consumers must cite the exact used closure.

The semantic-module identity contrast uses the ordinary module envelope:

```text
Record {
  0: Seq(exact imported SemanticModuleId references),
  1: Seq(sorted per-kind Record { 0: declaration-kind, 1: ordered bodies }),
  2: domain payload,
}
```

Its fixture has no imports, exact semantic-failure and semantic-primitive
declaration catalogs, and a Unit domain payload. Its ordinary semantic-module
digest is
`0e89ce7e005432619f5c80a9180e6ca8916cf863857b4fd4537e41e4a6906bd5`.
The oracle computes an identity over those exact bytes. It does not validate
declaration meaning, import-DAG admission, or exact-used closure.

## 5. Constitutional and local resource bounds

The constitutional `FoundationMetaProfileV0` bounds a root-zero canonical
meta-value at most `2^20` canonical bytes, `2^14` value constructors,
`2^14` child edges, and depth `384`. The depth of the root value is zero. These
are canonical grammar limits, not the semantic schema or term limits.

A finite semantic schema has depth at most `48`. Portable term syntax has at
most `4096` nodes and root-zero depth at most `48`, as authenticated by the root
law source above. Those two bounds apply to their domain objects even when the
surrounding canonical meta-value remains within its separate depth-384 limit.

This oracle intentionally uses a stricter local evaluation profile. Its limits
are validation inputs and never enter semantic identity:

```json
{
  "max_input_bytes":262144,
  "max_output_bytes":262144,
  "max_nodes":4096,
  "max_depth":64,
  "max_work":1048576
}
```

Entries are positive JSON integers (booleans are not integers) and may lower,
but not raise this oracle's local hard limits. The oracle preflights cumulative
counters before emitting canonical bytes or returning an identifier:

- `nodes` counts every value constructor once and root depth is one;
- child edges are checked against `max_work` on every cumulative addition;
- on binary Sequence and Record decode, `current_nodes + declared_count` and
  cumulative child edges are checked before allocating child-bound, ordinal, or
  task arrays;
- input is the exact body or identity-preimage size, plus canonical claimed-ID
  bytes for verification;
- output is the exact body size or 32 digest bytes; and
- work charges input bytes, nodes, child edges, and a conservative square of
  decimal digit count before host integer conversion.

Because this local profile stops at root-one depth `64`, its depth controls do
not claim to exercise the constitutional depth-384 edge. Exact and one-over
controls for that outer bound belong to the Foundation reference evaluator.

A limit failure yields `ResourceExceeded`, no partial ID, and no semantic
verdict. The runner separately refuses a source line larger than 2 MiB before
JSON parsing.

## 6. Outcomes and precedence

```text
Completed
Malformed       (including NonCanonical, wrong constructor, or wrong ref kind)
Unsupported
Mismatch        (including WrongKind, axis mismatch, or DigestMismatch)
ResourceExceeded
```

For a parsed request, precedence is the `case`/`op` envelope, operation
support, exact field shape for that known operation, constitutional profile,
complete identifier shape and constructor, supported identity/hash IDs,
expected subject kind, expected typed axes, resource/canonical-body validation,
then digest comparison. In particular, a well-shaped wrong subject kind
refuses before a malformed body, and an explicit axis mismatch refuses before
body evaluation. Incidental host failure is not converted into a semantic
outcome.
An unknown binary `MetaValueV0` tag is malformed, not an extension or an
unsupported semantic operation.

## 7. Explicit nonclaims

This oracle checks FoundationMetaProfileV0 values and the two exact typed
identity constructors. It does not admit PIR, establish a regime's adequacy,
validate module imports or exact-used closure, execute domain predicates,
validate cryptographic primitive implementations, convey authority, or prove
collision resistance. CarrierProfileId and EvaluatorProfileId construction are
deferred. It is an identity/value oracle, not a portable-term evaluator.
