# K1 executable-foundations instrument

This package exercises the selected non-authoritative K1 semantic foundation.
It is a research instrument, not compiler code, a protocol implementation, or
an admission authority.

## Contents

- `reference_model.py` implements `FoundationMetaProfileV0` structural encoding, typed
  content IDs, domain-indexed values, a bounded first-order term calculus,
  exact fixture primitives, deterministic charging, and qualified outcomes.
- `oracle/` is separately written. It imports no reference-model code and
  independently checks the constitutional value encoding and typed content identity against
  frozen JSONL vectors.
- `tests/` covers the reference evaluator and requires agreement with every
  frozen oracle vector over their common surface.

Run the bounded gate from the repository root:

```sh
python3 -B evaluation/k1-executable-foundations/run.py --check
```

The final bounded gate runs 90 reference/parity tests and 26
independent-oracle tests over 20 frozen oracle vectors: 116/116 pass. The
reference/parity lane contains 88 direct `reference_model` tests, one
record-by-record cross-check, and one exact durable-law transcription check.
The record cross-check recomputes exact shared positive
constructions and checks bounded contrasts or declared projections for the
remaining records; it is not an equivalent reference implementation of every
raw oracle request. The package covers exact finite fixtures only.

The frozen semantic-core law source is exactly 39,468 bytes with SHA-256
`4c0115cb4301240c555e1484ce98863bd2f3400a1ac0cf456ff89248229452d3`.
The complete encoded regime descriptor is exactly 40,383 bytes with SHA-256
`e7fa336ad42e028d272f7eb870cc5a9213068253a74f07c710ae111da3205eb0`.
Its semantic-regime digest is
`bfe22f86f4afc4ffaa79d7ec02db42f0c3fad30f6e6e81163cf21a52e05cce77`.

## Evidence boundary

The instrument demonstrates, over its frozen cases:

- unique strict encoding and round-trip decode for all nine constitutional
  constructors;
- authentication of exact presented typed ID/preimage pairs, including profile,
  hash suite, kind, semantic regime, and body axes;
- exact root and module declaration references, derived direct primitive
  references and module roots, and authenticated same-regime required module
  closure;
- domain mismatch and diagnostic-label/provider-binding noninterference;
- derived bounded traversal patterns expressed through the single
  `BoundedIterate` constructor;
- state-passing transcript hashing, bounded rejection search, explicit lossy
  projection, and semantic partiality;
- pairwise separation of unsupported, missing-dependency, kind-mismatch,
  malformed, refused, deterministic-limit, checker-failure, and completed
  domain-failure outcomes, including strict-decode versus post-decode owner
  admission and structural versus typing failure;
- rejection of one failure declaration carrying conflicting payload types;
- rejection as `Malformed` of host subclasses that attempt to override authenticated algorithm,
  term, module, contract, or primitive-cost-formula semantics; and
- cumulative wide-value refusal before aggregate encoding.

The oracle is independent only for canonical values and typed identity. There
is one Python term/module evaluator; direct `hashlib` calculations check
selected fixture results but are not a second semantic implementation.

The package does not decode the specification's complete serialized
evaluation-request carrier. Algorithm, contract, and module bodies are typed
Python objects, and the ID-only contract path uses a trusted local registry.
It therefore does not falsify:

- raw asserted prior-meta ID/body pairing or a well-formed but unsupported
  prior-meta basis in the reference evaluator;
- raw algorithm direct-primitive field omission, padding, or reordering;
- separately supplied asserted-ID/body mismatch for an algorithm, contract,
  or module;
- duplicate or unsorted raw module-map carriers or noncanonical raw module
  bodies, because the module bundle is an exact built-in `dict` or the
  package's exact immutable fixture-mapping singleton; or
- the optional `CanonicalValueId` surface.

Global one-ID/one-preimage binding is conditional on the digest law governing
each constructor: constitutional SHA-256 for prior-meta IDs and the
authenticated hash-suite descriptor for ordinary IDs. The package cannot
exercise a real `HashBindingConflict` without a collision or second preimage;
it tests pair recomputation, typed-axis non-aliasing, and the request-local
ledger's fail-closed conflict mechanics under a synthetic digest substitution.
Each evaluator call that passes boundary 1 creates one fresh ledger. It
observes only the request-supplied and immutable support bodies whose
validation boundaries it reaches. Runtime uses the same admitted resolver
snapshot rather than consulting a mutable replacement. The ledger has a
derived host cap of 20,486 entries--the exact
sum of the selected prior-meta, contract, algorithm, request-module,
evaluator primitive-support-module, and maximum distinct direct-primitive
constituents--so it adds no valid semantic refusal.
After request-basis authentication succeeds, the evaluator co-observes its
exact supported prior-meta descriptor bodies before any contract routing,
including on later malformed requests.

The evaluator copies an exact built-in `dict` or the package's exact immutable
fixture-mapping singleton once and then recursively validates an exact frozen
dataclass graph. The subclass regression prevents
host method/property overrides from changing authenticated meaning. It does
not cover catastrophic allocation or arbitrary reflective mutation after the
snapshot. Evaluator support registries must be exact tuples and are capped at
`2^14` entries before member inspection; that is realization evidence rather
than a new semantic-identity axis.

The package also cannot construct an authenticated cyclic module graph without
finding a hash fixed point or collision. Its forged-cycle case confirms that
the claimed preimage is rejected before traversal, while the
authenticated-cycle branch is specified but unexercised. It does not establish
SHA-256 correctness, primitive-provider conformance, protocol expressiveness,
PIR admission, strong Fiat--Shamir, cryptographic security, formal correctness,
constant-time behavior, production readiness, or integrated-kernel closure.
The bounded standalone K1 candidate is complete and green; K2/K3 integration
remains open.
