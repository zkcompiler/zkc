# K1 executable-foundations instrument

This package exercises the selected non-authoritative K1 semantic foundation.
It is a research instrument, not compiler code, a protocol implementation, or
an admission authority.

## Contents

- `reference_model.py` implements `FoundationMetaProfileV0` structural
  encoding, typed content IDs, exact semantic-language profiles and effective
  contexts, including an exact build-once/check-many subject-authentication
  seam over an already authenticated inert context, inert source-authority
  envelopes, domain-indexed values, a bounded first-order term calculus, exact
  fixture primitives, deterministic charging, and qualified outcomes.
- `oracle/` is separately written. It imports no reference-model code and
  independently checks the constitutional value encoding and typed content identity against
  frozen JSONL vectors.
- `tests/` covers the reference evaluator and requires agreement with every
  frozen oracle vector over their common surface.

Run the bounded gate from the repository root:

```sh
python3 -B evaluation/k1-executable-foundations/run.py --check
```

The final bounded gate runs 105 reference/parity tests and 26
independent-oracle tests over 24 JSONL vectors plus two compact frozen natural
byte-bound recipes: 131/131 pass. The
reference/parity lane contains 103 direct `reference_model` tests, one
record-by-record cross-check, and one exact durable-law transcription check.
The record cross-check recomputes exact shared positive
constructions and checks bounded contrasts or declared projections for the
remaining records; it is not an equivalent reference implementation of every
raw oracle request. The package covers exact finite fixtures only.

The frozen semantic-core law source is exactly 45,933 bytes with SHA-256
`f603cee6ce7acc601ca92a35b3de3787dcd9b9ea47a85486c8f4fb2732212658`.
The complete encoded regime descriptor is exactly 46,870 bytes with SHA-256
`f9a91f67c10a1efd92e40f6f7fb31cdb1ab37524a8ed961ac4b66124d1eeba06`.
Its semantic-regime digest is
`0c537a1d1638992bd0c3efd2256ed4c3506ecb96bb6136b6084189de10b86bef`.

## Evidence boundary

The instrument demonstrates, over its frozen cases:

- unique strict encoding and round-trip decode for all nine constitutional
  constructors, including acceptance of a natural whose complete encoding is
  exactly `2^20` octets and refusal one octet beyond that bound;
- authentication of exact presented typed ID/preimage pairs, including profile,
  hash suite, kind, semantic regime, and body axes;
- standalone exact semantic-language-profile identities, exact no-extra
  profile-import closures, profile-qualified subjects, exact-ID evaluator
  support, local/imported profile-declaration resolution, and exhaustive
  refusal of every standalone Foundation semantic kind and every prior-meta
  kind in profile formation, profiled-ID formation, and profiled
  authentication;
- fixed-lane canonical-value identities with identity-bearing caller purpose,
  and the exact standalone external-operation-contract identity equation;
- exact root and module declaration references, derived direct primitive
  references and module roots, and authenticated same-regime required module
  closure;
- domain mismatch and diagnostic-label/provider-binding noninterference;
- derived bounded traversal patterns expressed through the single
  `BoundedIterate` constructor;
- state-passing transcript hashing, bounded rejection search, explicit lossy
  projection, and semantic partiality;
- pairwise separation of unsupported, missing-dependency, cannot-answer,
  kind-mismatch, malformed, refused, deterministic-limit, checker-failure, and
  completed domain-failure outcomes, including strict-decode versus
  post-decode owner admission and structural versus typing failure;
- rejection of one failure declaration carrying conflicting payload types;
- inert portable authority-envelope formation, owner/family and same-regime
  checks, field sensitivity, and refusal to serialize, hash, copy, deep-copy,
  or pickle an owner-local binding;
- rejection as `Malformed` of host subclasses that attempt to override
  authenticated profile, algorithm, term, module, contract, or
  primitive-cost-formula semantics; and
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
- duplicate or unsorted raw profile/module-map carriers or noncanonical raw
  profile/module bodies, because these bundles use exact built-in `dict`
  carriers, with the package's immutable fixture-mapping singleton additionally
  accepted for modules; or
- arbitrary application-defined value domains beyond the fixed
  `CanonicalValueId` fixtures.

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
derived host cap of 36,870 entries--the exact sum of the selected prior-meta,
contract, algorithm, maximum profile closure, maximum request-module closure,
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

The package also cannot construct an authenticated cyclic profile or module
graph without finding a hash fixed point or collision. Its forged-cycle cases
confirm that a claimed preimage is rejected before traversal, while the
authenticated-cycle branches are specified but unexercised. Authority tests
do not authenticate owner objects, derive a policy closure, execute owner
admission, or exercise a live capability. The package does not establish
SHA-256 correctness, primitive-provider conformance, protocol expressiveness,
PIR admission, strong Fiat--Shamir, cryptographic security, formal correctness,
constant-time behavior, production readiness, or integrated-kernel closure.
The bounded standalone K1 candidate is complete and green. K3-E subsequently
exercised one bounded finite K1/K2/K3 consumer join; general durable
integration, broader protocol coverage, and kernel freeze remain open.
