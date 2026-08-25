# K1 Research and Selection

> **Document kind:** Temporary research and candidate-decision record
> **Document state:** Bounded standalone candidate selected and validated
> **Provisional owner:** `foundation`, with domain-owned semantic leaves
> **Authority:** None
> **Disposition:** Rewrite accepted design conclusions into
> [`executable-foundations.md`](../../../foundation/executable-foundations.md),
> preserve executable evidence under `evaluation/`, and delete this page with
> the K1 package before cutover.

## 1. Decision question

What is the smallest representation-independent mechanism that lets two
implementations reconstruct the same semantic identities and evaluate the
same finite portable functions, while refusing ambiguous, partial, cyclic,
unsupported, or over-budget attempts without turning Foundation into a
universal ZK runtime?

The mechanism must serve PIR and at least one independent semantic domain. It
must also preserve the distinction between identity, authentication,
admission, evaluator support, external implementation, authority, and theorem
judgment.

This page records why the integrated candidate was selected. The durable
target owns its exact rules; [`validation.md`](validation.md) alone may credit
executed evidence.

## 2. Evidence method and limits

K1 used four kinds of pressure:

1. reconstruction of the authoritative v0 mechanisms and the unresolved
   names in the target corpus;
2. algorithm-needs analysis across the selected P01--P10 protocol families;
3. comparison with primary specifications for canonical data, portable
   languages, semantic evolution, and cryptographic operations; and
4. independent falsification of bootstrap cycles, dependency closure, binder
   behavior, typed failure, and deterministic resource handling.

The portfolio analysis is a design-pressure result, not proof that every
protocol in a family is expressible. The reference evaluator and independent
identity oracle are finite instruments, not formal semantics or cryptographic
implementations. Their final bounded matrix and strict run are recorded in
[`validation.md`](validation.md); they complete the standalone K1 candidate,
not the integrated semantic kernel.

## 3. Reconstructed pressure

### 3.1 Current and target facts

**Current:** Authoritative v0 content IDs bind exact domain-tagged preimage
bytes. Encoders, registries, admission algorithms, execution profiles, and
error vocabularies are owner-specific. These are useful positive controls but
do not form a shared semantic foundation.

**Earlier target:** Stage 1--4A assumed generic regimes, canonical values,
finite algorithms, ABIs, totality, and content-addressed contracts. It did not
close their constructors, equality, support, typing, dependency, evaluation,
or resource laws.

**K1 requirement:** Preserve semantic guarantees and desired capabilities,
not the present host types, MLIR layout, JSON spelling, identifier strings, or
checker organization.

### 3.2 Algorithm pressure

The executed P01 witness, repaired FRI-Grind source residual, and
commitment/value/guard probes require at least:

- typed injective framing and explicit state passing;
- fixed-width scalar and group codecs;
- bounded indexed rejection sampling with early success;
- strict sequence alignment and duplicate rejection;
- lossy as well as lossless value transforms;
- authenticated path traversal; and
- cumulative work and result bounds that refuse before oversized commitment.

The bounded P02--P10 analysis adds runtime batch sizes, Merkle and IPA depth,
finite graph/worklist traversal, exact field/group/pairing leaves, and bounded
recursive-verifier descent. It found no verifier-side requirement for general
recursion. Prover strategies, Fresh coins, oracle construction, proof
generation, setup, theorem search, general parsing, and opaque adapters are
effects or judgments and must remain external.

This rejects both a tuple-only calculus and an all-purpose ZK VM. It does not
justify a separate universal constructor for every observed traversal pattern.

### 3.3 Bootstrap and extension pressure

The first candidate still contained two incompatible ideas:

- a regime chose machinery needed to identify its own descriptor; and
- the regime enumerated modules or primitives that should be independently
  extensible.

The first creates a root cycle. The second rotates every regime-qualified
subject when an unrelated extension is added. Making the regime field optional
only hides the cycle and creates one identifier type with two incompatible
construction rules.

K1 therefore requires a small constitutional prior, disjoint prior-meta and
ordinary constructors, a root that contains only its minimum interpretive
basis, and ordinary post-root modules cited by exact users.

### 3.4 Failure and resource pressure

An output-only function ABI cannot state which completed failures are
semantic. An untyped string or host exception cannot be authenticated as part
of a portable denotation. Conversely, evaluator exhaustion and incidental host
failure cannot be reported as if the semantic function returned a failure.

Charging only after construction admits a second defect: an output can be too
large to materialize even when the final checker would reject it. K1 therefore
requires a derived failure row, static completion-capacity preflight, atomic
charges, and a boundary at which catastrophic host failure produces no false
semantic record.

## 4. Primary-source lessons

These sources constrain the selection; none is adopted as a complete design.

1. [RFC 8949 deterministic encoding](https://www.rfc-editor.org/rfc/rfc8949.html#section-4.2)
   separates a data model from deterministic byte rules and requires a chosen
   profile. K1 fixes one bounded bootstrap profile instead of inheriting a
   library's current serialization.
2. [RFC 8785](https://www.rfc-editor.org/rfc/rfc8785.html#section-3) shows that
   canonical JSON needs strict input restrictions, duplicate handling, exact
   strings, and deterministic ordering. K1 uses no general JSON semantic
   value and excludes floating point.
3. Protocol Buffers explicitly warns that its
   [serialization is not canonical](https://protobuf.dev/programming-guides/serialization-not-canonical/).
   Stable schemas and deterministic mode do not by themselves establish
   semantic identity.
4. [StableHLO compatibility](https://github.com/openxla/stablehlo/blob/main/docs/compatibility.md)
   and [VHLO](https://openxla.org/stablehlo/vhlo) make compatibility a
   versioned conversion contract. K1 likewise separates exact identity from
   directed checked translation.
5. The [MLIR bytecode format](https://mlir.llvm.org/docs/BytecodeFormat/)
   separates carrier evolution from dialect semantics. Carrier profiles do
   not silently enter semantic-object identity.
6. [Dhall's standard](https://github.com/dhall-lang/dhall-lang/tree/master/standard)
   demonstrates normalization and canonical forms, but its language and
   semantic equality are larger than K1 needs. K1 identifies admitted typed
   syntax structurally rather than claiming extensional equality.
7. The [CEL language definition](https://github.com/cel-expr/cel-spec/blob/master/doc/langdef.md)
   demonstrates a terminating expression language, but termination alone
   does not bound nested finite work. K1 separately identifies charging and
   preflight rules.
8. [WebAssembly Core](https://webassembly.github.io/spec/core/) is a useful
   portability boundary, but its memory, control, validation, and embedding
   semantics are much larger than the selected workload requires.
9. [RFC 9380](https://www.rfc-editor.org/rfc/rfc9380.html) distinguishes exact
   hash-to-field/group algorithms, encodings, bias, and constant-time
   requirements. These remain exact primitive or domain laws, not consequences
   of a generic `bytes -> value` shape.
10. The CFRG [Fiat--Shamir transform draft](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-fiat-shamir)
    reinforces explicit state, typed codecs, unambiguous framing, session
    binding, and deterministic verifier behavior. K1 must support that shape;
    K2 still owns the strong-FS law.
11. [Git's hash-function transition design](https://git-scm.com/docs/hash-function-transition)
    motivates explicit identity and hash axes plus directed migration state,
    instead of treating a digest spelling as timeless semantics.
12. An [OCI descriptor](https://github.com/opencontainers/image-spec/blob/main/descriptor.md)
    binds media type, digest, and size but does not define the denotation of
    referenced code. Content addressing alone cannot turn a supplier contract
    into a portable semantic function.

## 5. Equal-resolution candidates

### A. Static catalogs only

Every operation is an exact named entry interpreted by an owner-specific
evaluator. This is small and reviewable, and remains appropriate for domain
predicates and expensive primitive leaves.

It becomes combinatorial for framing, batching, projection, and state-passing
composition. A names-only callback catalog is worse: an authenticated name and
ABI still do not determine one function.

### B. Small canonical calculus plus exact leaves -- selected

Use one intrinsically total typed calculus for structural semantic glue, exact
versioned primitives for algebraic and cryptographic leaves, domain-owned
evaluators for authority-bearing judgments, and disjoint contracts for
external suppliers.

This composes the common finite work without absorbing protocol admission,
theorem judgment, prover behavior, or implementation trust. Static domain
catalogs remain valid where a term would add no value.

### C. Typed deterministic VM

A metered WebAssembly-like VM offers broad implementation choice. It also
introduces a much larger validation, memory, control-flow, versioning, and
conformance surface. Metering does not prove totality or recovery from host
exhaustion. No current K1 pressure case needs it.

### D. Opaque content-addressed contract graph

Authenticated ABIs, dependencies, and supplier bindings are operationally
necessary for external work. They are not a semantic denotation: two suppliers
can satisfy the same shallow shape and return different values. This remains
the external-operation layer, not an implementation of the portable calculus.

### 5.1 Decision matrix

| Axis | A: catalogs | B: small calculus | C: VM | D: opaque contracts |
|---|---:|---:|---:|---:|
| Unique portable denotation | strong per entry | strong | conditional on full VM profile | absent |
| Intrinsic termination | per-entry obligation | structural | requires stronger validation | not established |
| Small semantic surface | strong | strong | weak | deceptively small |
| Compositional finite glue | weak | strong | strong | weak |
| Domain-authority separation | strong | strong | possible but fragile | weak |
| Independent evaluator feasibility | medium | strong | expensive | impossible from contract alone |
| Extension locality | medium | strong | medium | operational only |
| Current portfolio fit | viable but combinatorial | strongest | unnecessary | supplier layer only |

Candidate B wins. Candidate A remains the domain-local baseline and a reversal
option.

## 6. Integrated selection and reasons

### 6.1 Two disjoint identity constructors

`FoundationMetaProfileV0` is an un-IDed constitutional prior. It fixes the
bounded structural data and encoding needed to construct exactly three
`PriorMetaId` kinds:

```text
foundation.identity-profile
foundation.hash-suite
foundation.semantic-regime
```

Every other subject uses `SemanticContentId` and must carry exact
identity-profile, hash-suite, subject-kind, and semantic-regime axes. The
ordinary constructor refuses all three prior-meta kinds. There is no null
regime and no branch inside one identifier type.

This is intentionally less generic than the earlier optional-regime model. A
closed constitutional constructor makes the bootstrap visible, makes kind
confusion testable, and prevents later ordinary kinds from acquiring a
privileged no-regime path.

Exact tuple equality, evaluator support, and directed checked translation are
different relations. Carrier rendering, successful decode, or coincident
digest bytes imply none of them.

Recomputation authenticates the exact typed ID/preimage pair presented to one
check; it does not prove that no second preimage can produce the same digest.
Kinds and axes remain unconditionally disjoint because they are part of typed
ID equality even when digest octets coincide. One closed validation scope is
one top-level transaction containing all successfully authenticated request
and consulted registry, resolver, or cache preimages. If its request-local
ledger observes distinct exact preimages authenticating under the same typed
ID, it raises `HashBindingConflict` and admits neither as uniquely named. Global
one-ID/one-preimage binding is conditional on the selected hash suite's
collision and second-preimage assumptions for ordinary IDs, and on
constitutional SHA-256 for prior-meta IDs. Those assumptions belong in
downstream Analysis claims, not in structural authentication.

### 6.2 Root before ordinary modules

The semantic-regime root embeds only the minimum base value/term grammar,
local-ordinal rule for declarations that must be identified together, and the
extension envelope. It imports no post-root semantic module and does not hold
a whole-regime catalog of future primitives.

Semantic modules and primitives are ordinary regime-qualified semantic IDs.
Module imports must stay under the same root and form a finite DAG. Mutual
definitions are represented inside one explicit aggregate module by local
ordinal rather than by an inter-module hash fixpoint. A consuming subject cites
the exact module roots it uses, and authentication requires every and only
member of their unique-node, unique-edge closure.

This order simultaneously closes bootstrap and preserves extension locality:
adding an unrelated module does not rotate the root or an existing subject,
while changing a used module rotates every identity that cites it.

### 6.3 One canonical bounded iterator

The canonical calculus is first-order and pure. Its irreducible constructors
are:

- arguments, constants, and `let`;
- records/projection, tagged injection/exhaustive case, and conditional;
- bounded sequence construction, length, strict index, and bounded append;
- exact primitive call;
- typed semantic failure; and
- one indexed state-passing `BoundedIterate` over a finite sequence or bounded
  natural range.

`BoundedIterate` can continue with a new state or break with a result. Map,
zip, fold, find, argmin, sort, duplicate detection, pair/chunk traversal,
Merkle traversal, and worklists are derived patterns or domain-owned
algorithms. They are not separate universal syntax constructors.

The earlier broad combinator list was rejected because it enlarged the
normative semantics, created overlapping laws and binder cases, and would
rotate the language whenever a new traversal idiom appeared. A single indexed
state machine retains the required finite expressiveness and provides one
place to specify nesting, early exit, and charging. General recursion, cyclic
calls, callbacks, ambient registries, dynamic code, filesystem/network access,
clock, implicit randomness, reflection, exceptions as meaning, and
implementation-defined arithmetic remain forbidden.

Algorithm identity is structural typed syntax plus exact semantic
dependencies. It is not source spelling, diagnostic labels, evaluation
history, normalization, or extensional equality.

### 6.4 Exact primitives and external work

An admitted primitive has an exact ordinary semantic ID, typed input/output,
typed completed failures, and one normative operation law or immutable source
designation. Primitive references are derived from term syntax and checked by
exact ID. A provider is an implementation dependency; its build ID does not
become the primitive's denotation unless provider choice is itself declared
semantic.

The following classes remain disjoint:

```text
PortableAlgorithmCandidate   portable total term
SemanticPrimitive            exact normative leaf
DomainPredicateOrEvaluator   owner-specific judgment
ExternalOperationContract    capability-mediated work without inherited denotation
```

Hashes, XOF/duplex transitions, field/group operations, MSMs, and pairings can
be primitives only when their exact semantics are fixed. PIR admission,
relation satisfaction, theorem applicability, compiler assessment, and
projection correctness remain owner judgments. Prover strategies, Fresh
coins, setup, proof generation, storage, parsing, and opaque adapters remain
external operations.

### 6.5 Derived success and failure ABI

The type checker derives:

```text
SemanticFunctionType = {
  inputs,
  success_type,
  failures: CanonicalSortedUniqueSeq<
    SemanticFailureType(module_id, local_ordinal, payload_type)
  >
}
```

The failure alternatives are the union reached through typed `Fail`, strict
sequence operations, and exact primitives. A semantic failure completes the
function with its authenticated type and payload. An undeclared failure or a
payload of the wrong type is a checker defect, not a new semantic answer.

This removes authored output assertions, free-form failure names, and the
mistake of treating a host exception as domain meaning. Capability, wire,
checker, and endpoint contracts remain separate namespaces even when their
field shapes resemble a semantic function type.

### 6.6 Evaluation contract and request limits

Semantic evaluation order is fixed by the term language itself. Allowing an
evaluation contract to choose order would let a contract change meaning while
leaving the algorithm ID fixed.

An ordinary identified `EvaluationContract` instead fixes:

- validation precedence;
- atomic term-step and iteration charges;
- exact primitive work formulas;
- completion-envelope encoding and charge; and
- the static maximum-completion rule.

The request supplies concrete mathematical-natural limits. Changing the charge
schedule rotates the evaluation-contract ID but not the algorithm ID. Changing
request limits rotates neither.

Before execution, the evaluator derives the maximum completion envelope from
the success schema and all typed failure payload schemas. If it cannot fit,
evaluation does not begin. During execution, counters are checked before work
is committed; both success and semantic failure charge their exact emitted
completion size. The bounded instrument uses term steps, iteration items,
primitive work, and result bytes. Foundation does not infer native runtime,
circuit cost, side-channel behavior, or one universal resource vector from
those counters.

Incidental `MemoryError`, process death, or unavailable hardware may yield no
record. Catching such a failure and relabeling it `Malformed` or a semantic
failure would be a false claim.

### 6.7 Completion is not universal judgment

The evaluator distinguishes completed success or typed semantic failure from
malformed input, kind mismatch, unsupported semantics, missing dependency,
dependency refusal, deterministic exhaustion, and recoverable checker defect.
The selected instrument fixes one exact precedence so multi-defect tests are
reproducible.

Foundation owns the need for that separation, not a universal `Result`,
`Resource`, diagnostic vocabulary, or judgment lattice. Protocol rejection,
relation negative, Analysis `CannotAnswer`, supplier abort, and semantic sample
exhaustion keep their owning meanings.

## 7. Candidate variants rejected during K1

| Earlier variant | Why rejected | Replacement |
|---|---|---|
| one content-ID type with optional regime | concealed two constructors and admitted future null-regime ordinary kinds | closed `PriorMetaId` plus mandatory-regime `SemanticContentId` |
| regime root importing semantic modules | root/module identity cycle | root embeds minimum basis; ordinary modules follow it |
| whole-regime extension or primitive registry | unrelated-extension identity churn | exact subject-local module roots and closure |
| many universal iteration combinators | overlapping semantics, binder surface, and language churn | one indexed state-passing `BoundedIterate` |
| authored output ABI and totality evidence | redundant authority and identity cycles | type and totality derived from syntax/declarations |
| untyped domain failure payload | not compositional or authenticated | module/ordinal/payload-typed failure alternatives |
| evaluation contract chooses term order | could alter meaning without rotating algorithm ID | order fixed by language; contract owns charging/preflight |
| result limit checked only after evaluation | may materialize the forbidden result | static completion-capacity preflight plus exact finish charge |
| opaque content-addressed callback as term | content ID authenticates bytes, not denotation | external contract or checked bridge to exact semantics |

## 8. Validation obligations

The executable package must pressure at least:

- both disjoint identity constructors, wrong-axis cases, and the absence of a
  null-regime ordinary path;
- unrelated-extension locality and used-module identity rotation;
- same-root exact-used module closure, including missing, extra, wrong-kind,
  cross-regime, cycle, and shared-diamond cases;
- nested binder behavior and derived primitive dependencies;
- transcript state passing, bounded rejection, authenticated path folding,
  nested count-by-retry sampling, strict sequence access, and a lossy
  projection;
- derived output and failure alternatives, typed partial arithmetic, and
  undeclared/wrong-payload checker defects;
- semantic retry exhaustion versus deterministic evaluator exhaustion;
- exact-limit and one-less-limit behavior for each charge dimension;
- static result-capacity refusal before term execution and exact charging for
  both success and semantic failure;
- invalid limits, validation precedence, and host-failure nonclassification;
  and
- byte and ID parity with a separately written oracle over the exact common
  surface.

Agreement is diversity evidence, not a proof of SHA-256, primitive law,
protocol correctness, or the durable specification.

### 8.1 Final bounded selection result

The strict standalone gate passed 116/116 tests: 90 reference/parity tests
(88 direct `reference_model` tests, one replay of every frozen oracle record,
and one exact durable-law transcription check) and 26 independently written
oracle tests. The accepted frozen anchors are:

- semantic-core law source: 39,468 bytes, SHA-256
  `4c0115cb4301240c555e1484ce98863bd2f3400a1ac0cf456ff89248229452d3`;
- encoded regime descriptor: 40,383 bytes, SHA-256
  `e7fa336ad42e028d272f7eb870cc5a9213068253a74f07c710ae111da3205eb0`;
  and
- semantic-regime digest:
  `bfe22f86f4afc4ffaa79d7ec02db42f0c3fad30f6e6e81163cf21a52e05cce77`.

The final regressions include a conflicting failure-payload declaration and
host subclasses that attempt to override authenticated algorithm, term,
module, contract, or resource-formula semantics. Both refuse at the intended
boundary.

The evidence remains deliberately narrower than the selected law. There is no
complete raw serialized request decoder; algorithm, contract, and module
bodies use typed Python objects. Consequently the package does not test raw
algorithm direct-primitive field omission/padding/reordering, separately
asserted algorithm/contract/module ID-body mismatch, duplicate or unsorted raw
module-map carriers, noncanonical raw module bodies, or optional
`CanonicalValueId`. An authenticated cycle cannot be constructed without a
hash fixed point or collision, so only the forged-cycle authentication order
is exercised. A synthetic digest substitution exercises the request-local
`HashBindingConflict` ledger and checker-failure branch, but it is not evidence
of a real collision or unconditional global hash binding. Canonical value and
identity have an independent oracle, but term and module evaluation have one
evaluator. Host evidence is limited to a one-time snapshot from an exact
built-in dictionary or the package's exact immutable fixture-mapping singleton
and recursively exact frozen
dataclass graph; catastrophic allocation and reflective mutation remain
outside the claim.

## 9. Reversal conditions

Reopen the selection if:

1. a required verifier-side transform cannot be represented with finite
   structural terms, exact primitives, and the single bounded iterator;
2. the core grows toward a general VM or starts duplicating domain evaluators;
3. independent implementations cannot agree without shared implementation
   code or ambient registries;
4. exact-used content-addressed modules impose identity churn without buying
   demonstrated local extension or replay value;
5. static schema analysis cannot preflight an admitted term's completion size,
   or deterministic accounting cannot refuse before committing over-limit
   work; or
6. a static-catalog rival expresses the same pressure fixtures with less
   semantic surface and no loss of independent denotation.

The bounded standalone K1 selection and executable gate are complete. This
record remains non-normative, and the integrated kernel is not frozen. The
provisional durable Foundation absorption and cold K1 audit are complete; K2
owns Protocol and Fiat--Shamir closure, and K3 owns minimum consumer co-design
and the final extraction test. A K2/K3 contradiction that meets a reversal
condition above reopens the narrow K1 decision it falsifies.
