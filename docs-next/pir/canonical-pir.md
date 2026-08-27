# Canonical PIR carrier and lifecycle

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Normative surface maturity:** Provisional K1/K2 carrier contract
> **Provisional owner:** `pir`
> **Authority:** This page specifies the selected carrier target for
> `docs-next/`. It remains non-normative until explicit consolidation and
> cutover; the current specifications under [`docs/`](../../docs/README.md)
> remain authoritative. It makes no implementation, compatibility, or
> migration claim.
>
> **Normative dependencies:** [Executable foundations](../foundation/executable-foundations.md),
> [Interactive Core](interactive-core.md), and
> [Fiat--Shamir interpretation](fiat-shamir.md)
>
> **Implementation status:** the current `pir`/`oir` TableGen dialects are
> pre-K2 regression evidence. They do not implement this carrier.

This page fixes how the K2 `InteractiveCore` and `Protocol` subjects inhabit
one canonical MLIR PIR graph. It supersedes the earlier carrier candidate based
on roles, ports, objects, randomness declarations, endpoint obligations, and a
universal dependency row. Those were fields of the pre-K2 model and are not a
second spelling of the K2 subjects.

The language-independent algebra owns meaning. MLIR is its one structural PIR
carrier:

```text
(InteractiveCore, Protocol over that Core)
             <-> one canonical MLIR PIR graph

raw transport
  -> transport decoding
  -> canonical graph and dependency authentication
  -> K2 Core and Protocol admission
  -> opaque process-local AdmittedProtocol
```

This page freezes the semantic groups, field disposition, correspondence laws,
and refusal boundary. It deliberately does not yet freeze TableGen class names,
operation mnemonics, assembly syntax, bytecode versioning, or a public exchange
format. A later physical profile must realize the exact groups below without
adding another Protocol schema.

## 1. Scope and invariants

The carrier contract has six load-bearing invariants.

1. One graph denotes exactly one `Protocol` and embeds exactly the
   `InteractiveCore` body named by that Protocol.
2. Every field in `InteractiveCoreBody` and `ProtocolBody` is present exactly
   once. No identity-bearing fact is inferred from a name, registry, SSA use,
   default, source position, or consumer.
3. An FS root carries only `TranscriptConstructionId`. The construction body
   and its dependencies are separately authenticated inputs.
4. K1 modules, declarations, primitives, algorithms, evaluation contracts,
   value domains, and failures remain independently identified dependencies.
   Their bodies are not copied into the Protocol graph.
5. Interface, Plan, Relations, Analysis, Evidence, OIR, runtime invocations,
   and execution records are not Protocol fields.
6. Transport validity, canonical authentication, and semantic admission are
   distinct. Success at an earlier boundary implies no later success.

The graph carries semantic structure, not live authority. A graph, stored ID,
signature, admission marker, or prior result never serializes a capability.

## 2. Exact subject and field disposition

### 2.1 Root subject pair

The carrier domain is the finite pair:

```text
CanonicalPirSubjectPair_B = {
  core: InteractiveCore,
  protocol: Protocol
}

where
  protocol.core_id =
    SemanticContentId<"pir.interactive-core">(
      B, InteractiveCoreBody(core))
```

The physical root carries the complete typed `core_id` and one claimed complete
typed `ProtocolId`. A `SemanticContentId` already contains the foundation
epoch, identity-profile ID, hash-suite ID, semantic-regime ID, subject kind, and
digest fixed by K1. There is no additional independently variable
`ProtocolSemanticRegimeId` field.

The exact descriptor preimages forming `PriorMetaAuthenticationBasis B` remain
external authentication inputs. Repeating their bytes in the graph would not
make an unauthenticated root authoritative.

### 2.2 `InteractiveCoreBody`

The Core body has exactly the fourteen K2 fields below, in this order. The
canonical MLIR graph carries every listed field. The exact nested
`MetaValueV0` record and variant tags are those in
[Interactive Core Appendix A](interactive-core.md#appendix-a-canonical-bodies);
this page does not create parallel encodings for them.

| Ordinal | Core field | Exact graph-carried content | External or excluded content |
|---:|---|---|---|
| 0 | `used_modules` | Canonically sorted unique sequence of complete typed direct-owner `SemanticModuleId`s | Module bodies and transitive imports are external |
| 1 | `public_inputs` | One declaration per ordinal with its exact `ValueType` | Invocation values are runtime data |
| 2 | `verifier_private_inputs` | One declaration per ordinal with its exact `ValueType` | Verifier-private invocation values are runtime data |
| 3 | `constants` | Exact `ValueType` and canonical datum | No host constant or printer spelling |
| 4 | `derived_values` | Portable-algorithm reference, evaluation-contract reference, ordered `ValueRef`s, and result type | Algorithm and contract bodies are external dependencies |
| 5 | `scopes` | Exact optional parent and `Initially`/`BeforeOccurrence` opening | No derived scope path cache |
| 6 | `bindings` | Scope, exact `Statement`/`SessionContext`/`PublicParameter` tag, and value reference | Bound invocation values remain runtime data |
| 7 | `challenges` | Scope, value type, domain declaration, fresh-law declaration, correlation, reduction-use policy, and ordered public conditions | No resolved challenge value or FS frame |
| 8 | `oracles` | Scope, index and element types, maximum entries, and exact publication mode including its references | Oracle carrier and confidential witness are runtime data |
| 9 | `checks` | Algorithm reference, evaluation-contract reference, and ordered inputs | Evaluator implementation and result are not identity fields |
| 10 | `claims` | Contract, scope, usage, and exact initial-binding or reduction-output source | Claim liveness is derived execution state |
| 11 | `reductions` | Contract, scope, ordered input claims, side inputs, challenges, publication requirements, and output contracts | Reduction result and theorem evidence are external |
| 12 | `terminals` | Verdict, public outputs, required checks, and ordered claim dispositions | Reached terminal and outputs are runtime records |
| 13 | `occurrences` | Scope, exact guard, and complete effect variant, including every `ModuleEffectRef` payload byte | Activity, outputs, receipts, and derived influence are not stored |

Every nested product field, sum tag, optional tag, sequence length and order,
typed ordinal, `ValueType`, canonical datum, `ContentRefV0`, and declaration
reference is graph-carried. Empty sequences and absent optionals use their exact
explicit K1/K2 form; omission is not a default.

The following K2 objects are deliberately not part of `InteractiveCoreBody` or
the graph:

- `CoreInvocationBody` and concrete public or verifier-private values;
- prover strategies, witness, advice, private randomness, private state, and
  supplier material;
- `RunRecord`, failure and challenge receipts, Oracle receipts, and partial
  execution records;
- `PublicCoinView`, dependency graphs, transcript prefixes, scope paths, and
  other mechanically derived views; and
- display names, source locations, diagnostics, provenance, evidence, and
  compiler routes.

### 2.3 `ProtocolBody`

The Protocol part of the root carries exactly:

```text
ProtocolBody(P) = {
  0: ContentRefV0(P.core_id),
  1: Fresh
     | FiatShamir(ContentRefV0(P.transcript_construction_id))
}
```

The same physical `core_id` is the Protocol field and the claimed identity of
the embedded Core. A second Core-ID spelling is forbidden. `ProtocolId` is a
claimed root header checked against this exact body; it is not a field of its
own preimage.

Fresh and FS Protocols over one literal Core therefore have different
`ProtocolId`s while sharing one `CoreId`.

### 2.4 External `TranscriptConstructionBody`

For FS, the graph carries only the exact typed `TranscriptConstructionId`.
Authentication separately receives the complete K2 construction body:

```text
TranscriptConstruction = {
  core_id,
  transcript_state_type,
  transcript_bytes_type,
  natural_type,
  initial_state,
  absorb,
  squeeze_bytes,
  advance_state,
  application_domain,
  sampling_exhausted_failure,
  ordered total challenge_rules
}
```

Its strict K1 `MetaValueV0` decode/re-encode and ID law are independent of the
Protocol graph. The body contains no self-ID; the K2
`BindConstructionSelfId` instruction uses the resolved authenticated ID.

Fresh accepts neither a construction reference nor construction preimage. FS
requires exactly one construction whose recomputed ID equals the root reference
and whose `core_id` equals the embedded Core. A missing construction is a
missing dependency; an extra construction for Fresh is refused by exact input
closure.

### 2.5 K1 dependencies and module closure

The graph carries typed references at the exact fields that own them. It does
not carry a generic dependency table and does not nest dependency bodies.

In particular:

- `used_modules` is the exact direct owner set, not its transitive closure;
- declaration references retain exact root/module owner, kind, and ordinal;
- portable-algorithm and evaluation-contract references retain complete typed
  content IDs;
- a `ModuleEffectRef` retains its module ID, exact
  `ModuleDeclarationRef<"pir.core-effect">`, and exact `MetaValueV0` payload;
  and
- primitive, value-domain, failure, algorithm, evaluation-contract, and module
  bodies remain explicit external preimages.

Authentication applies K1's typed-coordinate formation, strict body
authentication, and least `RequiredModuleClosure_B` laws. Admission then
requires `used_modules = DirectOwnerModules(core)`. Consequently an unrelated
module cannot enter the request, changing a used module rotates dependent
identities, and a shared import diamond authenticates each module once.

### 2.6 Satellite exclusion

`ProtocolInterface`, `ProverPlan`, Relations subjects, Analysis questions or
results, Evidence, OIR programs, endpoint realizations, and source audits are
separately identified or attributed objects. None occurs in the canonical
Protocol graph, including as an optional root reference.

A transport envelope may co-package separately encoded subjects, but package
membership grants no authority and is not part of `CoreId` or `ProtocolId`.
Changing only an Interface, Plan, relation subject, or realization must leave
both IDs unchanged. Injecting such material into the canonical graph is a
physical-form error.

Consumer operations receive satellites explicitly:

| Consumer | Additional admitted inputs |
|---|---|
| Verifier OIR projection | exact Interface, verifier purpose, and one affirmative checked `EndpointSourceView` from [Endpoint Projection Views](endpoint-projection-views.md) |
| Plan-specialized prover OIR projection | exact Interface and Plan, affirmative `CheckedPlanRealizes`, specialized-prover purpose, and one affirmative checked `EndpointSourceView` whose graph contains the reachable Plan component; neither a whole Plan nor `PlanWitnessSurface` enters target identity |
| `ProtocolRelationBinding` formation and admission | exact relation Interfaces and K1 dependencies reached by the candidate; no `ProtocolInterfaceId` |
| Protocol-level mapped correspondence | exact admitted `CorrespondenceQuestion`, every admitted operand it names, and owner-issued views plus matching live authority for `ManifestFor(question)`; no `ProtocolInterfaceId` unless that exact question reads one |
| External instance correspondence | the exact admitted external-instance question and operands, owner-issued views plus matching live authority for its manifest, exact `DecodedExternalAssignment`, and matching codec-evaluation authority |
| Analysis and Evidence | only the exact subjects and views named by their own read manifests |

The base binding relates K2 semantic Protocol coordinates to relation meaning;
it does not read external names, containers, codecs, or ABI presentation.
Only a question that follows an externally supplied instance through its
presentation consumes the exact `ProtocolInterfaceId`. This distinction keeps
Protocol-level relation meaning reusable across multiple lossless external
Interfaces.

## 3. Abstract canonical MLIR form

### 3.1 Physical groups, not frozen spellings

`CanonicalPirGraphV0` is one isolated root with one embedded Core. Its abstract
physical groups occur in this order:

```text
root header
core.used_modules
core.public_inputs
core.verifier_private_inputs
core.constants
core.derived_values
core.scopes
core.bindings
core.challenges
core.oracles
core.checks
core.claims
core.reductions
core.terminals
core.occurrences
protocol.challenge_interpretation
```

Each group has one finite ordered body. Each declaration occurs exactly once at
its canonical ordinal. These are abstract carrier groups; the final dialect may
choose operations, typed properties, and regions that realize them, but cannot
merge fields, create shadow fields, or retain a pre-K2 constructor.

A suitable realization uses structural operations for the root, Core, groups,
and declarations, and strongly typed K1/K2 attributes for IDs, value types,
datums, variants, and references. Encoding the entire Core as one opaque JSON,
dictionary, byte string, or generic `MetaValue` attribute is not a production
carrier: it would make MLIR unable to validate or transform its structure and
would merely embed a second parser.

### 3.2 Closed physical form

The eventual physical profile must fix and check:

- exactly one root, one embedded Core, and one instance of every field group;
- the exact permitted PIR and minimal builtin operation/type/attribute set;
- exact region and block counts;
- canonical declaration order and explicit empty/absent values;
- typed reference constructors, kind-specific ordinal spaces, and bounds;
- canonical ordering for semantic sets and maps, with duplicate rejection;
- absence of unknown operations, fields, properties, attributes, types, and
  nested dialect material; and
- absence of source locations and nonsemantic metadata inside the canonical
  graph.

MLIR operation pointers, block labels, symbol names, SSA names, host iteration
order, text formatting, bytecode producer strings, and transport version are
not semantic. SSA may appear only when a minimal carrier primitive requires it;
alpha-renaming is then its sole permitted variation.

Authoring IR may carry names, locations, and convenience syntax. It must erase
or extract them before entering this closed graph. A discardable MLIR attribute
is still forbidden here merely because a generic parser would ignore it.

### 3.3 Stable coordinates

Inside one Core, local references are typed dense ordinals into the exact
canonical sequence owned by their kind. Bare integers from different kinds are
never interchangeable.

A portable reference is stable only together with its subject identity:

```text
CoreRef<K> = (CoreId, K, canonical_ordinal)

ProtocolScopedRef<K> = (ProtocolId, CoreRef<K>)
```

Use `CoreRef<K>` for interpretation-independent Core facts and
`ProtocolScopedRef<K>` when Fresh versus FS affects meaning. A downstream OIR
source occurrence therefore uses `ProtocolScopedRef<occurrence>`, not a bare
event-position integer.

Inserting or reordering a declaration intentionally changes later ordinals and
`CoreId`; the old complete coordinate cannot silently name the new entry.
Renaming source labels, changing printer spelling, or alpha-renaming carrier SSA
does not change any coordinate or semantic ID.

## 4. Algebra-to-carrier correspondence

### 4.1 Domain

Fix candidate basis data `B` for lowering and later authentication. The
structural reader itself is basis-independent and grants `B` no authority:

```text
ClaimedCanonicalPirSubjectPair = {
  core_candidate: InteractiveCore,
  protocol_candidate: Protocol
}

Lower_B:
  CanonicalPirSubjectPair_B
    -> StructurallyCanonicalIdConsistentPirGraph_B

ReadStructural:
  StructurallyCanonicalPirGraph
    -> ClaimedCanonicalPirSubjectPair // algebraic data only; no authority

AuthenticateCanonicalPirGraph_B:
  (StructurallyCanonicalPirGraph,
   ClaimedCanonicalPirSubjectPair,
   ExactCanonicalPirDependencyEnvironment_B,
   exact K1 authentication and evaluator authority)
    -> Qualified<AuthenticatedCanonicalPirGraphHandle_B>

Read_B:
  AuthenticatedCanonicalPirGraphHandle_B
    -> AuthenticatedCanonicalPirSubjectPairView_B
```

`Lower_B` is defined only when the Protocol's `core_id` equals the recomputed ID
of the supplied Core. `ReadStructural` recognizes only the closed physical
grammar and reconstructs its claimed algebraic data before any basis has
authority. It reads claimed headers only as graph fields for later comparison
and does not authenticate them or add them to the semantic pair. It grants no
identity, dependency, admission, or capability authority. The subscript-free
domain is deliberate: parsing cannot assume the prior-meta basis that the next
boundary must authenticate.

`ExactCanonicalPirDependencyEnvironment_B` is the exact request-local tuple of
the authenticated prior-meta basis `B`; every and only Core dependency preimage
derived from the structurally reconstructed body and K1 module closure; for FS,
the one exact transcript-construction body and every and only dependency
preimage derived from it; and no construction for Fresh. The authentication
operation recomputes all claimed IDs, checks exact dependency-key closure, and
uses the supplied K1 authority. On success it mints one opaque
process-local `AuthenticatedCanonicalPirGraphHandle_B` bound to the identical
immutable graph object, structural reconstruction, complete dependency
environment, evaluator identity, authentication authority, and request-local
hash-binding ledger. The handle has no canonical body, ID, Boolean surrogate,
copy constructor, or serialized form. K2 admission receives fresh separate
checker authority under Section 5.2; the graph handle neither contains nor
serializes it.

`Read_B` is admission-facing access through that live handle. Its returned
immutable pair view retains the handle and exposes the exact authenticated Core
and Protocol candidates needed by K2 admission; it is not an admitted Protocol
and cannot outlive or detach from the handle. A graph, algebraically equal pair,
stored ID, or prior authentication report cannot substitute for the handle.

### 4.2 Exact inverse laws

For every pair `S` in the lowering domain and every graph `G` in the
structurally canonical, claimed-ID-consistent graph domain, the authority-free
structural functions satisfy:

```text
ReadStructural(Lower_B(S)) = S

Lower_B(ReadStructural(G)) = G
  modulo only in-memory operation identity and unavoidable SSA alpha-renaming
```

In the second equation, `G` is restricted mathematically to the structural
domain whose claimed basis data is exactly `B` and whose claimed IDs recompute
under that data. This restriction makes the pure encoding equation well typed;
it does not authenticate `B` or `G`. Operational authority arises only at
`AuthenticateCanonicalPirGraph_B`.

The second equation permits no reordering, default insertion, unknown metadata,
symbol renaming, alternate reference form, or inferred field.

Additionally:

```text
InteractiveCoreBody(ReadStructural(G).core)
  = the exact fourteen-field K2 MetaValueV0 body carried by G

ProtocolBody(ReadStructural(G).protocol)
  = the exact two-field K2 MetaValueV0 body carried by G
```

The structural inverse domain requires the recomputed `CoreId` and `ProtocolId`
to equal the claimed root IDs; this requirement grants no authority. For FS,
`ReadStructural` reconstructs the construction ID only. It cannot synthesize
the external construction body, module body, algorithm body, Interface, Plan,
or relation subject.

Authentication adds no third representation and has no serialization inverse.
For every successful
`h = AuthenticateCanonicalPirGraph_B(G, S, D, A)`, where
`S = ReadStructural(G)`, `D` is the exact dependency environment, and `A` is
the required K1 authentication/evaluator authority, the graph and data
preservation laws are exactly:

```text
UnderlyingGraph(h) = the identical immutable G object
ForgetAuthentication(Read_B(h)) = ReadStructural(G)
```

Neither law permits dependency omission, substitution, or authority recovery
from the right-hand side.

### 4.3 Independent conformance

The reader and lowerer must be independently implemented. They may share the
declared K1 primitive types, but one must not call the other or share one table
whose omitted field makes both implementations agree incorrectly.

Conformance requires all of:

1. both inverse laws;
2. comparison with independent expected `InteractiveCoreBody` and
   `ProtocolBody` K1 vectors;
3. direct ID-vector comparison;
4. mutation of every identity-bearing field; and
5. negative formation and dependency cases.

A printer/parser round trip alone is transport evidence, not this
correspondence result.

## 5. Authentication, admission, and live authority

### 5.1 Cross-owner capability contract and inert bindings

PIR uses the project-wide
[`ExactSourceAuthorityBinding`](../project/analysis-and-compiler-architecture.md#23-capability-neutral-source-bindings)
for admitted subjects, attenuated views, and checked results exported across an
owner boundary. Each PIR family retains its exact family-indexed
`PirCapabilityContractId`, ABI, consumer, purpose, source coordinate, and
transitive operation-policy closure. The contract uses the explicit
`OwnerDefinesNoOperationPolicy` disposition where PIR owns no separate policy.

The portable binding is inert. It is neither an admission receipt nor a
capability. A consumer reauthenticates the exact subject, contract, ABI, and
dependencies, re-runs the owning admission or check, and separately obtains a
fresh matching process-local capability. Attenuation cannot be widened, and
serialization or process crossing destroys live authority.

This page adds no portable carrier-specific capability channel. The process-
local graph handle remains inside authentication and admission and cannot cross
an owner boundary. The detailed binding, portable/owner-local result-coordinate,
reset, and replay laws remain those of the project authority model and the K1/K2
subject lifecycles.

### 5.2 Separate checker authority

Canonical authentication consumes unauthoritative graph and dependency data
plus the exact live authentication operations required by K1. Admission then
uses fresh exact K2 checker authority:

```text
authenticated embedded Core
  -> AuthenticateCore / AdmitCore

admitted Core + Fresh
  -> AdmitFresh

admitted Core + authenticated and admitted external construction
  -> AdmitFS
```

The owning operations are exactly those specified by
[Interactive Core](interactive-core.md) and
[Fiat--Shamir interpretation](fiat-shamir.md). This page does not duplicate
their scope, binding, strategy, Oracle, public-coin, transcript-influence,
sampling, replay, or failure laws.

Checker implementations, evaluator handles, capabilities, and admission
witnesses never enter Core or Protocol identity and never serialize. A caller
cannot supply claimed public-coin classes, transcript prefixes, occurrence
maps, influence sets, or derived dependency closure in place of recomputation.

### 5.3 Ordered boundaries and refusal taxonomy

The ordered boundary is:

1. decode the selected transport and parse MLIR;
2. require the closed physical form and run authority-free `ReadStructural`;
3. authenticate the complete prior-meta basis;
4. authenticate every typed Core dependency and exact K1 module closure;
5. for FS, authenticate the external construction and its dependencies;
6. recompute `CoreId`, `TranscriptConstructionId` when present, and
   `ProtocolId`;
7. mint the operand-bound `AuthenticatedCanonicalPirGraphHandle_B` and expose
   its immutable pair view through `Read_B`; and
8. run the exact K2 Core and selected interpretation admission.

The following distinctions are mandatory:

| Condition | Qualified boundary |
|---|---|
| Bytes do not decode or MLIR does not parse | transport failure; no semantic candidate |
| Unknown carrier op/attribute/type, missing or extra field/group/block, invalid local reference, noncanonical order, or implicit default | `Malformed` during canonical formation |
| Formed typed reference has the wrong subject kind, regime, owner kind, or other required axis | `KindMismatch` |
| Exact named construction, module, primitive, algorithm, contract, or other preimage is absent | `MissingDependency` |
| Supplied body does not recompute to its carried ID | `Malformed`; two pair-authenticated bodies under one typed ID are `HashBindingConflict` |
| Otherwise formed but unused extra dependency | `Refused` by exact key-set closure |
| Known `ModuleEffectRef` carrier names same-kind semantics unsupported by the evaluator | `Unsupported` |
| Supported effect payload fails strict owner-schema decoding | `Malformed` |
| Authenticated, supported candidate fails an owner or K2 semantic law | `Refused` |
| A declared deterministic bound is crossed | `DeterministicLimitExceeded` |
| An advertised checker/evaluator operation disagrees with its exact contract | `CheckerFailure` |

Unknown MLIR syntax is never semantic `Unsupported`. The known generic
`ModuleEffectRef` is the extension boundary at which an authenticated but
unimplemented same-kind meaning can produce `Unsupported` without guessing.

## 6. Imported-verification pressure

Recursive or imported proof verification must use the K2 extension mechanism,
not a dedicated pre-K2 carrier constructor:

```text
Occurrence.effect = ModuleEffectRef {
  module: imported-verification SemanticModuleId,
  declaration: ModuleDeclarationRef<"pir.core-effect">,
  payload: exact declaration-carried MetaValueV0
}
```

The authenticated module declaration fixes the payload schema, ordered inputs
and outputs, actor-visible history, transition, guard behavior, required
influence, replay, terminal interaction, decision class, dependency edges,
public reconstruction, and deterministic bounds. The carrier preserves the
payload exactly and supplies none of those laws itself.

Any future exact supported imported-verification effect contract must close its
payload's external semantic citations to only:

- independently specified and authenticated semantic verifier algorithms and
  their exact K1 evaluation contracts;
- module- or K1-owned proof-input ABI declarations, with actual proof material
  entering through the effect's ordinary typed K2 `ValueRef` inputs;
- the child `ProtocolId` and exact typed child Core or Protocol coordinates
  needed to identify its Statement, checks, claims, or terminals;
- nominal K1/K2 claim contracts, without importing a Relations-owned Interface
  or correspondence result; and
- exact K1 semantic parameters, either as admitted typed values or independently
  identified parameter subjects.

Such a supported payload must not cite or embed `ProtocolInterfaceId`,
`RelationInterfaceId`, any Plan or Plan view, OIR, Evidence, a relation
instance or correspondence result, an endpoint realization, or a concrete
realization-artifact identity. Those objects are satellites or observations,
not Core semantics. Their identities cannot select which verifier a Core
executes.

If an operational verifier currently depends on a concrete artifact, a future
supported effect contract must require that the semantics it relies on first be
extracted into an independently specified,
authenticated, and admitted semantic verifier algorithm or semantic parameter
subject. The Core cites that semantic subject and the module declaration checks
its exact ABI. Substituting the semantic verifier or parameter changes the
`ModuleEffectRef` payload or used dependency and therefore rotates `CoreId`.
A later correspondence result may relate a concrete realization to that
semantic subject, but the realization artifact itself never enters the Core.

That contract cannot use legacy label strings for `route` or `proof_slots` as
coordinates. A legacy `unabsorbed` Boolean is not retained: the effect
declaration's required-influence and framing law decides what must reach the
transcript.

K3-B validates only that the exact imported-verification reference and payload
survive both authority-free carrier inverse laws and every identity-field
mutation, and that a known same-kind declaration without an exact supported
`pir.core-effect` contract reaches typed `Unsupported`. It does not claim that
such a Core is admitted or standardize one universal imported-proof semantics.
The unsupported payload is preserved as exact carrier material but is not
decoded, classified, or granted the future contract's citation guarantees.
Only a separately specified exact supported effect contract can enable positive
Core admission. Until that contract exists, the carrier reaches typed
`Unsupported` at Core admission and no endpoint-projection question can be
formed. If a future exact module contract does admit the Core but the selected
OIR profile has no discharge rule for it, that distinct well-formed question
returns projection-level `Unsupported` and emits no partial program.

## 7. Authoring, persistence, and information loss

Rich MLIR, source languages, importers, and synthesis tools are outside
canonical PIR. Their boundary may produce one Core/Protocol candidate and zero
or more Interface, Plan, relation, source-map, or audit outputs. Success of one
output neither authenticates nor admits another.

Before erasure, the normalizer must classify every distinction as:

- retained in an exact K2 field;
- extracted into one separately typed satellite or nonsemantic audit output;
- eliminated under one named and checked source-language quotient; or
- refused.

Names, locations, macros, partial schedules, implicit defaults, imported
symbols, relation descriptions, private construction routes, and protected
effects cannot simply disappear because the canonical carrier has no slot for
them.

Persisted graph bytes remain raw material. Cold replay decodes transport,
reauthenticates the exact basis and dependency preimages, recomputes every ID,
readmits the Core and interpretation with fresh authority, and reruns any later
relation or projection. Equal bytes, equal IDs, or a prior affirmative result
may locate material but grant no authority.

## 8. Conformance fixtures and deferred realization work

The minimum positively admitted carrier witness contains:

- a multi-scope Core with public and verifier-private inputs;
- all public-binding classes, an exact guard, prover and deterministic-verifier
  messages, challenges, the Oracle publish/query/answer lifecycle, a check,
  initial and reduction-output claims, a reduction publication requirement, and
  terminals;
- Fresh and FS Protocols over the same Core;
- an external construction with bounded retry and typed sampling failure; and
- direct modules whose external transitive closure includes a shared diamond.

A separate carrier-only imported-verification witness carries one exact
same-kind `ModuleEffectRef` and payload, checks both structural inverse laws and
every identity-field mutation, then requires typed `Unsupported` and no admitted
Core while no exact supported `pir.core-effect` contract exists. Because no
admitted Protocol results, no OIR projection request or partial OIR can exist.
K3-D separately tests an admitted synthetic module-effect coordinate with no
OIR discharge rule as projection-level `Unsupported`; that synthetic case does
not standardize imported-proof verification.

The negative matrix mutates every identity-bearing field and covers missing,
extra, reordered, duplicate, wrong-kind, cross-regime, wrong-ID, unknown carrier
syntax, unsupported module semantics, and deterministic-limit cases. It also
checks that Interface/Plan/Relations changes leave Core and Protocol IDs stable,
that injection of those satellites is malformed, and that imported verification
stops at PIR admission while a separately admitted unsupported module profile
stops at K3-D projection without a partial OIR artifact.

The following remain later realization work and are not silently selected here:

- final operation mnemonics, TableGen classes, assembly syntax, builtin
  allowlist, bytecode profile, and version negotiation;
- standalone MLIR carriers for TranscriptConstruction, Interface, Plan, or
  Relations rather than their exact K1 algebraic transports;
- full OIR grammar, execution semantics, and projection correspondence;
- a standardized imported-verification module and endpoint support;
- K4 composition or protocol-family changes to the Core; and
- migration from the current pre-K2 `pir`/`oir` dialects.

Carrier formation, authentication, admission, or successful round trip does
not establish source-language correctness, relation satisfaction, protocol
soundness, completeness, knowledge, zero knowledge, Fiat--Shamir security,
compiler preservation, endpoint support, implementation conformance, or
production readiness. Those remain separately scoped checked conclusions.
