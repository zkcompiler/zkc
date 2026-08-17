# zkc Identity and the v0 Contract

Status: **current normative declaration (2026-08-09).**

zkc is at v0. At v0 there is exactly one stability promise: **the artifact
id**. A content id (`sha256:<hex>` under a fixed ASCII domain tag) names the
same bytes forever; everything else — formats, schemas, flags, encodings,
tool output — may break between any two revisions, and a break is the norm,
not an event. Real versioning begins at v1, when an external consumer exists
whose acceptance is a trust boundary. Until then the repository carries no
compatibility machinery: no supported-version enumerations, no upgrade hooks,
no legacy decoders, no version fields whose only reader is a check that the
field equals its only value.

## 1. What is fixed

| Surface | Identifier | Rule |
|---|---|---|
| Content identity | `sha256:<hex>` under a fixed domain tag per artifact kind. Artifacts: `"zkc/pir\n"`, `"zkc/oir\n"`, `"zkc/oir-semantic\n"`. Claim descriptors: `"zkc/claim\n"`, `"zkc/claim-vector\n"`. Material expressions: `"zkc/material-expr\n"`. Vocabulary entries: `"zkc/claim-profile\n"`, `"zkc/check-contract\n"`, `"zkc/check-predicate-spec\n"`, `"zkc/hole-contract\n"`, `"zkc/reduction-contract\n"`, `"zkc/terminal-rule\n"`. Construction entries: `"zkc/profile-codec\n"`, `"zkc/profile-sponge\n"`. Soundness: `"zkc/soundness-rule\n"`, `"zkc/soundness-binding\n"`, `"zkc/soundness-signature\n"`, `"zkc/derivation-judgment\n"`. This list is exhaustive: a tag hashed anywhere in the implementation and absent here is a defect in one of the two. | an id names its exact preimage bytes; a preimage change mints new ids and never reinterprets old ones; the stored id is excluded from its own preimage and every consumer recomputes it before use |
| Diagnostic ids | `[zkc-Eddd]` per the §3 allocation registry | append-only: a shipped id never changes meaning; retirement leaves the number dead; a new id takes the next number in its component's range |
| Carrier version blob | MLIR dialect version 0.0 for both dialects | the one marker read before decoding, where an identity recheck cannot help: a different blob refuses rather than being decoded under the current layout. An artifact from a different encoding regime is named as such, not upgraded and not confused with a tampered one |
| Producer marker | `zkc_v<release>` in the bytecode header | error locality only: it names a foreign or stale artifact clearly; acceptance never rides on it — the identity recheck and the version blob are the gates |

Registries (`zkc.protocol_vocabulary`, `zkc.construction_profiles`,
`zkc.relation_contract`, `zkc.soundness_signature`,
`zkc.diagnostic_allocation`, `zkc.upstream_pins`, `zkc.derivation_request`,
`zkc.derivation_witness`) are named by their `registry` string and carry no
version field. Their loaders are fail-closed — unknown fields, duplicate
keys, floats, unresolved references, and ABI divergence refuse — so a schema
change surfaces as a refusal at the seam, which at v0 is the intended
signal. The flat sealed cited-entry sections of the vocabulary remain the
sole artifact digest authority.

The signature digest covers the schemas, the rules, and the bindings, and
nothing else. It is what names an analysis: two derivations are comparable
when they cite the same signature digest. Annotations are outside it for the
same reason they are outside a declaration preimage — correcting a citation
must not make an artifact's analysis a different analysis. A derivation
witness records the question in full and the answer by digest; a checker
supplies its own signature and re-runs the derivation rather than reading the
recorded conclusion.

## 2. What is not fixed

Everything else, explicitly including: `.mlirbc` bytes across zkc revisions ·
PIR/OIR textual syntax · registry schemas · family-description input format ·
tool flags · `reference/oracle` module layout (only its parity verdicts and
printed documents are load-bearing) · diagnostic *message text* (ids are the
contract; prose is not) · report rendering and evaluation views · replay
fixtures and adapter records. None of these mint versions at v0; when one
breaks, goldens are re-minted through both implementations and the change
lands as one change set.

## 3. Diagnostic-id allocation

Diagnostic ids are the stable conformance surface; message prose is not.
A new check takes the next available number in its component's allocated
range. Every live id must be emitted by the declared source component and
asserted by a test in the same change, unless the allocation records a
specific coverage exemption. Reserved ids must not be emitted.
Every allocated id — live or reserved — carries one sentence saying what
condition it names. The stability rule above is a claim about meaning, so the
meaning is written where it can be read back and held to; an id whose meaning
lives only in the code it is emitted from cannot be checked against reuse, and
a number held in reserve with no recorded purpose is indistinguishable from one
held by accident.

The exact range, source allowlist, live-id, reserved-id, meaning, and
coverage-exemption allocation is machine-readable in
[`registry/diagnostic-allocation.json`](../../registry/diagnostic-allocation.json).
That file is the single allocation authority. The lint checks that emitted
diagnostics belong to their declared source ranges, live ids have emitters and
test assertions, reserved ids are not emitted, every allocated id has a
sentence and every sentence an allocated id, and exemptions carry reasons.
