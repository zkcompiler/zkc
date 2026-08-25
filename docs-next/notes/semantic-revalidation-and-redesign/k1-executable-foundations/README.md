# K1 Executable Foundations

> **Document kind:** Temporary bounded work-package charter
> **Document state:** Bounded standalone K1 candidate complete; integrated kernel open
> **Provisional owner:** `foundation`, coordinated by `project`
> **Authority:** None. This package records research and validation work;
> current normative rules remain under [`docs/`](../../../../docs/README.md).
> **Activated:** 2026-08-25
> **Disposition:** Promote the accepted mechanism and its exact limits to its
> durable owners, retain the executable fixtures, then delete this package
> before cutover.

## Scope

K1 closes only the executable substrate required before the Protocol and
Fiat--Shamir kernel can be repaired. It selects and tests:

- a noncircular bootstrap and two disjoint identity constructors;
- regime roots, ordinary semantic modules, and exact-used dependency closure;
- typed canonical values and references;
- a small portable, first-order, bounded semantic calculus;
- exact semantic primitives and typed completed failures;
- the separation of portable semantics from predicates and suppliers;
- a derived semantic function type;
- identified deterministic charging and preflight rules; and
- semantic completion versus qualified noncompletion.

K1 does not redesign Protocol execution, strong Fiat--Shamir, Relations,
Analysis, the Compiler, OIR, or Realization. Those owners are consumers and
falsifiers here. K2 owns Protocol and Fiat--Shamir; K3 owns minimum consumer
co-design.

## Reconstructed gap

**Current:** The authoritative v0 has concrete domain-separated SHA-256
identities, bounded canonical JSON and carrier encodings, fixed construction
registries, owner-specific admission engines, and fail-closed operational
outcomes. It does not expose one shared semantic identity, value, algorithm,
failure, or deterministic evaluation mechanism.

**Pre-K1 target:** Earlier target pages used names such as
`SemanticRegimeId`, `CanonicalSemanticValue`, `ClosedFiniteTerm`, exact ABIs,
and totality evidence without fixing enough construction, comparison,
dependency, typing, evaluation, or resource laws for independent
implementations to agree.

**K1 correction:** Recomputing content identity authenticates one presented
typed identifier and exact canonical preimage pair. Global uniqueness of that
preimage remains conditional on the digest law governing its constructor:
constitutional SHA-256 for `PriorMetaId`, and the authenticated `HashSuiteId`
for `SemanticContentId`. A co-observed collision is a checker failure with no
admitted object. The closed scope is one top-level validation/evaluation
transaction and includes all successfully authenticated request and consulted
resolver preimages; the reference instrument implements it with one fresh
typed-ID-to-body ledger per call. Identity does not prove adequacy, totality of
opaque code, evaluator support, provider
conformance, admission, or theorem truth. K1 makes each transition explicit
instead of loading it into an identifier.

## Selected and validated standalone candidate

K1 selected and validated the following dependency order on its bounded
standalone surface:

```text
FoundationMetaProfileV0                         constitutional, un-IDed
  -> PriorMetaId                                exactly three closed kinds
       identity-profile | hash-suite | semantic-regime
  -> SemanticContentId(regime, kind, body)      every ordinary subject
       including semantic modules and primitives
  -> same-regime semantic-module DAG            exact used closure
  -> domain-indexed canonical values
  -> PortableAlgorithmCandidate                 small bounded core
       exact SemanticPrimitive IDs
  -> derived SemanticFunctionType
       success type + canonical typed failure alternatives
  -> EvaluationContractId                       charging and preflight ABI
  -> EvaluationRequest                          concrete limits and inputs
```

There is no null or optional semantic regime. The three prior-meta kinds use a
constructor disjoint from ordinary semantic content. A regime root embeds only
the minimum base grammar and local-ordinal/aggregate rule needed to interpret
later subjects; it does not import post-root modules or enumerate every future
primitive. Ordinary semantic modules are regime-qualified IDs, import only
same-regime modules as a DAG, and are cited only by subjects that use them.
This breaks the bootstrap cycle without rotating unrelated subjects when an
extension is added.

The canonical term core contains arguments and constants, `let`, records and
projection, tagged injection and exhaustive case, conditionals, bounded
sequence construction/access, exact primitive calls, typed failure, and one
indexed state-passing `BoundedIterate`. Map, zip, fold, find, canonical sort,
tree traversal, and worklists are derived patterns or domain-owned algorithms,
not universal constructors. General recursion and effects are excluded.

`SemanticFunctionType` is derived from the typed term and contains the exact
ordered input types, success type, and canonical set of
`SemanticFailureType(module_id, local_ordinal, payload_type)` alternatives.
An authored output ABI or untyped failure string carries no authority.

Semantic evaluation order is fixed by the term language. An identified
evaluation contract fixes validation precedence, atomic charge schedules,
primitive work formulas, completion encoding, and static result preflight. A
schedule change rotates the contract ID, not the algorithm ID; request limits
rotate neither. Foundation does not define one universal result, resource,
judgment, or domain failure enum.

The detailed alternatives, reasons, and reversal conditions are in
[`research-and-selection.md`](research-and-selection.md). Exact executed
evidence belongs only in [`validation.md`](validation.md).

The final strict gate is green: 90/90 reference/parity tests and 26/26
independently written oracle tests, or 116/116 total. The reference/parity lane
contains 88 direct `reference_model` tests, one replay of all frozen oracle
records, and one exact durable-law transcription check. The frozen semantic-
core law is 39,468 bytes with SHA-256
`4c0115cb4301240c555e1484ce98863bd2f3400a1ac0cf456ff89248229452d3`;
the encoded regime descriptor is 40,383 bytes with SHA-256
`e7fa336ad42e028d272f7eb870cc5a9213068253a74f07c710ae111da3205eb0`;
and the resulting regime digest is
`bfe22f86f4afc4ffaa79d7ec02db42f0c3fad30f6e6e81163cf21a52e05cce77`.

## Work-package records

This README owns the direct K1 inventory:

- [Research and Selection](research-and-selection.md) reconstructs the
  pressures, compares equal-resolution candidates, records the integrated
  selection and discarded variants, and cites primary sources.
- [Executable Validation](validation.md) owns the frozen instrument contract,
  falsifier matrix, executed result, exact claims, nonclaims, and promotion
  verdict.

The executable instrument lives under
[`evaluation/k1-executable-foundations/`](../../../../evaluation/k1-executable-foundations/).
It is bounded evidence, not production code or authority.

## Exit gate and verdict

The bounded standalone candidate satisfied executable criteria 1--8 below.
Criterion 9 is the remaining cross-consumer extraction constraint:

1. the prior profile, the three prior-meta kinds, ordinary semantic ID
   preimages, and typed-axis checks are explicit and noncircular;
2. the regime root cannot depend on post-root modules, and exact-used module
   closure is same-regime, finite, authenticated, and acyclic;
3. a portable term's output and typed failure alternatives are derived from
   admitted syntax and exact primitive declarations;
4. the single bounded iterator expresses the selected finite verifier-side
   pressure cases without adding general recursion or a universal VM;
5. external suppliers cannot inhabit portable semantic-function positions;
6. semantic failure is distinct from malformed input, kind mismatch,
   unsupported semantics, missing or refused dependencies, deterministic
   exhaustion, checker defects, and incidental host failure;
7. cumulative decoder and evaluator limits, including completion capacity,
   refuse before an over-limit aggregate or semantic result is committed;
8. a reference implementation and separately written identity oracle agree
   over their exact common surface; and
9. K3 demonstrates at least two aligned consumers of the selected shared
   mechanics without making Foundation the owner of domain predicates,
   universal results, universal resources, or judgments.

This verdict completes the standalone K1 selection and executable gate. It
does not freeze the integrated semantic kernel. The selected mechanism is now
absorbed into the provisional durable Foundation owner and the cold K1 audit
is complete. K2 still owns Protocol/Fiat--Shamir closure, while K3 owns the
minimum two-consumer co-design and final extraction test.

## Persistent nonclaims

- Passing finite fixtures would not establish protocol expressiveness,
  cryptographic correctness, primitive-provider conformance, constant-time
  behavior, theorem applicability, or implementation readiness.
- Intrinsic termination does not imply acceptable time, memory, result size,
  native cost, circuit cost, or side-channel behavior.
- Deterministic charges are abstract operation rules. They do not promise that
  a host can recover from out-of-memory, process death, or unavailable
  hardware.
- Support is evaluator-relative. Two evaluators may authenticate the same
  object while only one supports it; they must agree whenever both claim the
  exact operation.
- `FoundationMetaProfileV0` is a constitutional trust anchor, not an artifact
  proved correct by its own content identity.
- Global one-ID/one-preimage binding is conditional on each constructor's
  governing digest law. The instrument exercises the conflict-ledger mechanics
  under a synthetic digest substitution, but cannot exercise a real
  `HashBindingConflict` without a collision or second preimage.
- The term language is portable semantic glue. Prover strategies, Fresh coin
  generation, theorem engines, general parsers, setup, proof generation, and
  arbitrary cryptographic implementations remain outside it.
- The instrument has no full raw serialized evaluation-request decoder.
  Algorithm, contract, and module bodies are typed Python objects.
- It does not exercise raw algorithm direct-primitive field omission, padding,
  or reordering; separately supplied asserted-ID/body mismatch for algorithms,
  contracts, or modules; duplicate/unsorted raw module-map carriers;
  noncanonical raw module bodies; or optional `CanonicalValueId`.
- The authenticated module-cycle branch is unexercised without a hash fixed
  point or collision. The forged-cycle case instead proves authentication
  precedes the selected refusal.
- There is one term/module evaluator. Independent agreement covers canonical
  values and typed identity, not portable-term execution or module admission.
- The host snapshot copies an exact built-in `dict` or the package's exact
  immutable fixture-mapping singleton once and recursively validates exact
  frozen dataclass shapes. Semantic-override subclasses and
  conflicting failure payload declarations are rejected, but catastrophic
  allocation and reflective mutation remain outside the evidence.

## Intended durable destinations

Accepted shared mechanics go to `foundation/`. PIR, Relations, Analysis,
Compiler, and OIR retain their regime bodies, value-domain meaning, algorithm
kinds, predicates, semantic failures, admission judgments, endpoint behavior,
and resource policy. Project retains cross-domain authority and evolution
discipline. The executable fixtures remain under `evaluation/` with bounded
claim language.

## Deletion trigger

Delete this package after the selected shared mechanism is complete in its
durable owner; target placeholders cite that owner or an explicit domain-local
definition; the evaluator and oracle retain their exact evidence contract;
all unresolved alternatives have a durable reversal trigger; no durable page
depends on this package; and the parent temporary inventory is updated.
