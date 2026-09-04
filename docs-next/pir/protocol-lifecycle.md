# Candidate Protocol subject and lifecycle

> **Document kind:** Architecture proposal
> **Document state:** Superseded
> **Baseline status:** Previous Stage 1 lifecycle candidate
> **Provisional owner:** `pir`
> **Authority:** Non-normative. This page records the first Stage 1
> reconstruction and its superseded design hypothesis. The current specifications
> under [`docs/`](../../docs/README.md) remain authoritative until an explicit
> normative migration and cutover.

> **Supersession notice — 2026-08-22:** This page remains the previous coherent
> lifecycle candidate and an evidence source. Comparative research completed
> in the Stage 1 package routed through the
> [temporary workspace inventory](../notes/README.md#working-note-inventory). Its
> durable [Protocol IR Architecture](../project/protocol-ir-architecture.md)
> supersedes this page's single-level carrier, identity, regime, Interface,
> ProverPlan, and canonical-form selections. The decoding, admission,
> capability, semantic-authority, and opaque-reference distinctions remain
> inputs unless the selected architecture explicitly refines them.

> **Stage 3 completion notice — 2026-08-22:** The durable
> [Protocol Semantic Model](protocol-model.md), [Canonical PIR](canonical-pir.md),
> [Interfaces and Plans](interfaces-and-plans.md), and [Fiat--Shamir and Core
> Composition](fiat-shamir-and-composition.md) now own the selected exact
> non-normative target. This page remains historical reconstruction only.

## 1. Previous provisional result

The earlier package found the current lifecycle architecturally coherent in
its main separations and proposed the following v0 factorization:

```text
one Protocol semantic subject
one internal canonical identity projection
one current PIR authoring and persistence carrier
one content-addressed seal-authority graph
many ephemeral, purpose-specific capabilities and derived views
```

This combines a carrier-independent Protocol model with the current MLIR/PIR
workbench and a capability-oriented lifecycle. It does **not** create a second
wire schema, a second persisted Protocol artifact, or a stable decoder for the
current canonical JSON output.

The immediate design decision is therefore semantic, not organizational:

- `Protocol` owns meaning and content identity;
- PIR is the sole supported v0 representation used to author, transform, and
  persist that meaning;
- the identified root owns typed digest references to exactly the seal
  declarations it consumes, while opaque subject references remain outside
  that authority graph;
- admission materializes and checks the reachable declaration preimages;
- decoding, resolution, admission, and consumer access do not mint new
  Protocol identities; and
- any downstream operation that uses information erased from Protocol
  identity must name that information as a separate input rather than recover
  it implicitly from carrier metadata.

The last rule is important. The current carrier contains some authoring and ABI
names that are erased by PIR identity but can affect later OIR identity. The
completed Stage 2 architecture resolved this boundary through separately
identified Interface and Plan subjects or explicit transition inputs; this
earlier Stage 1 model deliberately left the choice visible.

## 2. Reading discipline

This page uses four evidence labels:

| Label | Meaning |
|---|---|
| **Current normative** | Reconstructed from the owning specification under `docs/spec/` |
| **Implemented correspondence** | Directly visible in the current checkout, without making code semantic authority |
| **Provisional target** | Preferred design for the future v0 corpus, still non-normative |
| **Open transition question** | A decision intentionally routed to Stage 2 or a later owning package |

The current authority route is
[`docs/README.md`](../../docs/README.md). The primary semantic owners used here
are the [Protocol Kernel](../../docs/spec/kernel.md),
[Carrier](../../docs/spec/carrier.md),
[Vocabularies](../../docs/spec/vocabularies.md),
[Boundaries](../../docs/spec/boundaries.md),
[Versioning](../../docs/spec/versioning.md),
[Relations](../../docs/spec/relations.md),
[Soundness](../../docs/spec/soundness.md),
[Compiler](../../docs/spec/compiler.md), and
[Endpoints](../../docs/spec/endpoints.md).

Implementation and tests are correspondence evidence only. External research
is used to compare abstractions and future options; it does not establish zkc
conformance or correctness.

## 3. Reconstructed current lifecycle

### 3.1 Main path

The current normative signatures and implementation jointly imply:

```text
editable pir.protocol
    -- seal(ProtocolEnvironment) -->
identified pir.sealed carrier
    -- persist as MLIR bytecode -->
PersistedPirArtifact
    -- decode + structural verify + recompute id -->
DecodedPirArtifact
    -- recheck seal under ProtocolEnvironment -->
AdmittedPirArtifact
    -- derive through a controlled adapter -->
consumer-specific view or capability
```

Projection is one such consumer boundary and creates a new OIR subject with its
own identity. Analysis creates qualified judgments, not successor Protocols.
Compiler transformation rechecks successor identity and follows a different
branch. An identity plan may preserve the predecessor ID; a content-changing
plan may produce a different ID:

```text
AdmittedPirArtifact[id1]
    -- clone and reopen without authority -->
editable pir.protocol'
    -- checked transform + reseal + re-admit -->
AdmittedPirArtifact[id2, where id2 may equal id1]
```

Static composition is also an open-state path:

```text
link(OpenP, OpenP, faces, Envs) -> OpenP -> ordinary seal
```

The current signatures appear in
[`boundaries.md`](../../docs/spec/boundaries.md) and the implementation roles
are visible in [`Artifact.h`](../../include/zkc/Artifact/Artifact.h),
[`SealEngine.h`](../../include/zkc/Semantics/SealEngine.h), and
[`LinkEngine.h`](../../include/zkc/Semantics/LinkEngine.h).

### 3.2 What is already strong

The current model correctly separates:

- editable content from immutable identified content;
- content identity from carrier bytes and filenames;
- transport and structural authentication from registry-backed seal admission;
- admitted source authority from mutable transformation clones;
- Protocol identity from compiler-configuration identity;
- derived consumer facts from producer-populated mirrors; and
- serialization from capability continuity.

The current API reinforces these distinctions. `DecodedPirArtifact` owns a
private decoded root and authenticates carrier shape plus the stored identity,
while `AdmittedPirArtifact` additionally retains an immutable environment after
registry-backed recheck. Neither exposes the stored operation. Analysis and
projection privately derive their own consumer objects from that handle.

### 3.3 What is not yet owned precisely

The current corpus does not yet give one section complete ownership of:

- every identity-bearing Protocol field;
- the direct declaration manifest and recursively reachable authority graph;
- the difference between cited semantic closure and a larger loaded
  `ProtocolEnvironment`;
- the exact conceptual roles of persistence, decoding, and admission;
- the complete canonical-byte grammar;
- carrier metadata that survives serialization but is outside Protocol
  identity;
- the extra inputs that may influence projection or other consumers; and
- the exact authority carried by a process-local admitted handle.

The target factorization below gives those conceptual gaps provisional owners
and makes the model precise enough to enter transition research. It is not yet
a complete normative algebra or carrier grammar. It preserves current artifact
identities unless a later normative decision explicitly changes their
preimages.

## 4. Target subject factorization

### 4.1 Roles, not necessarily serialized types

| Role | Exact meaning | Identity | Mutability and authority |
|---|---|---|---|
| `ProtocolDraft` | Editable proposal expressed through Open PIR; references may be unresolved and a stamped closure may be absent or stale | No stable Protocol identity | Mutable and unauthoritative |
| `ResolvedSealCandidate` | Ephemeral draft plus the declaration material selected from one resolver environment for the attempted seal | No separately published identity | Immutable for one seal evaluation; not a boundary artifact |
| `ProtocolRoot` | Complete identity-bearing Protocol content plus the direct typed declaration manifest | Determines one `ProtocolId` | Semantic value; no admission claim by possession alone |
| `SealAuthorityGraph(root)` | Least content-addressed graph of seal-declaration preimages reachable through typed authority edges from the root manifest | Nodes retain their own content identities; no second Protocol id | Supplied and verified for seal checking; not inlined into the root |
| `ReferencedSubjectGraph(root)` | Opaque anchors, material references, and other cited external subjects whose interpretation is not admitted by seal | References retain their own identifiers | No authority to load, interpret, or trust the referenced subject is acquired by seal |
| `SealedProtocol` | A `ProtocolRoot` whose complete seal predicate succeeds against its resolved authority graph | The root's `ProtocolId` | Immutable semantic subject |
| `PersistedPirArtifact` | MLIR bytecode carrier claiming to represent one sealed Protocol root | Carries the same `ProtocolId`; carrier bytes have no Protocol identity of their own | Raw transport input at a new boundary |
| `DecodedPirCarrier` | Private in-process PIR carrier whose framing, supported dialect shape, structural verifier, and stored identity were checked | Same `ProtocolId` | Read-only handle; not seal-admitted |
| `AdmittedProtocol` | Opaque process-local capability establishing that the exact root was re-resolved and passed the seal predicate | Same `ProtocolId`; no capability id | Immutable authority for named consumers |
| `CarrierContext` | Authenticated read-only PIR representation and carrier-qualified fields retained for consumers but excluded from `ProtocolRoot` | No independent identity selected; exact inventory remains open | May be consumed only by a transition that names its field and role explicitly |
| `RetainedResolverEnvironment` | Broader immutable resolver retained by the current admitted handle beyond the minimal cited admission basis | No global environment identity selected | An uncited lookup is a separate declared authority input, not inherited Protocol meaning |
| `AdmittedPirCarrier` | Current implementation-shaped capability combining admitted Protocol authority, `CarrierContext`, and a `RetainedResolverEnvironment` | Same `ProtocolId`; retained context and resolver have separate status | Must not let carrier-only or uncited environment data silently become Protocol truth |
| `SemanticRegime` | Exact normative interpretation of intrinsic operations, policies, canonicalization, and seal predicates used by one checker | Implicit and process-local today; stable reference is open | Must be explicit before cross-version capability reuse or independent checking can compare admissions |
| `ProtocolInterface` | Explicit mapping from canonical Protocol positions to externally visible statement, witness, event, or endpoint ABI names | Historical baseline left identity open; selected architecture uses a dependent `ProtocolInterfaceId` containing `ProtocolId` | Required whenever a consumer uses names erased from Protocol identity |
| `ProtocolSubjectRef` | Reference to the whole Protocol or an exact occurrence within it, such as `(ProtocolId, ClaimRef)` | No new identity unless its owner specifies one | Used to scope a later judgment precisely |
| `ConsumerView` | Immutable facts mechanically derived from an admitted subject for one consumer | Normally no independent identity | Carries only the authority established by its derivation |
| `DerivedArtifactOrJudgment` | Durable OIR, relation correspondence, derivation judgment, or other independently meaningful consumer result | Owned by the producing domain | Not merely a view or capability over `ProtocolId` |

These names are provisional. Their distinctions are not. A final API may
combine several roles in one private storage object, but the specification must
not give them overlapping meanings.

### 4.2 Semantic subject versus runtime evidence of admission

`SealedProtocol` names the semantic subject that satisfies the seal predicate
under one semantic regime. Under this historical baseline the regime qualified
the admission predicate but did not enter `ProtocolId`. The selected
architecture replaces that choice: the applicable typed semantic regime is
identity-bearing.
The textual mnemonic `pir.sealed`, a stored ID field, or a structurally
verifying operation does not by itself establish that fact at a new boundary.
The current raw MLIR operation can be directly constructed or mutated; full
authority is recovered only through the seal or admission boundary.

The target documentation should therefore reserve unqualified
“sealed Protocol” for the semantic result and use a carrier-qualified term for
raw `pir.sealed` state. This is a terminology rule, not a demand to rename the
existing operation immediately.

### 4.3 Capability contract

A lifecycle capability is a narrow authenticated API handle, not a new
serialized artifact and not a claim that zkc implements a general
object-capability security system. A valid capability must have:

1. a controlled constructor;
2. an exact immutable subject identity;
3. minting only after its named predicate succeeds;
4. opaque storage with no mutable subject accessor;
5. explicit authority and permitted consumers;
6. no producer-populated fact mirror that can diverge from the subject; and
7. explicit degradation to raw input after serialization, reconstruction, or
   mutation outside the controlled boundary.

Different implementation languages may encode this contract through opaque
types, modules, ownership, or an explicit state machine. The semantic
predicates remain the same even if the programming-language mechanism changes.

## 5. Complete Protocol root and identity

### 5.1 Conceptual root

The compact current kernel object

```text
P = (E, <=, A, C, R, chi, K, anchors, B_M)
```

correctly exposes the transcript spine and claim-flow graph, but it is not a
complete inventory of the identified carrier content. The provisional complete
root is:

```text
ProtocolRoot =
    CoreProtocolContent
  + SealPolicy
  + ConstructionSelection
  + DirectTypedDeclarationManifest
  + ConstructionRoutes?
  + SpineSegmentation?
```

where `CoreProtocolContent` includes the ordered semantic events, normalized
claim sources and reductions, challenges, checks, anchors, material bindings,
and terminal sinks. The optional marker means the section may be absent for a
semantic default; it does not mean the field is outside the model.

The current canonical top-level correspondence is:

| Current canonical section | Protocol-root role |
|---|---|
| `policy` | Exact seal policy selection |
| `kappa` | Transcript and construction selection, including semantic parameters and references |
| `vocab` | Direct typed declaration manifest and consumed construction-entry pins |
| `transformers` | Normalized claim sources and reduction occurrences |
| `events` | Totally ordered transcript events and identity-bearing event data |
| `material_bindings` | Canonical local-value to stable material-reference edges |
| `sinks` | Normalized discharge, export, assumption, and residual outcomes |
| `routes` | Prover construction DAG and witness-facing declarations, when present |
| `segments` | Nontrivial spine segmentation, when present |

This is a semantic inventory, not a proposal to duplicate the current C++ ODS
model in a second manually maintained DTO.

### 5.2 Direct manifest and reachable authority graph

The root physically owns typed digest edges, not the entire registry and not
arbitrary copied declaration bodies:

```text
DirectTypedDeclarationManifest(root)
    = exact cited entry ids, sections, and content digests

SealAuthorityGraph(root)
    = least graph of digest-verified declaration preimages
      reachable from that manifest through typed seal-authority edges
```

The current source `ProtocolVocabulary` has seven semantic sections: predicate
specifications, claim profiles, value profiles, check contracts, hole
contracts, reduction contracts, and terminal rules. The current sealed table
has four always-present protocol sections, two conditional protocol sections,
and consumed construction-profile pins; predicate preimages are reached
transitively rather than duplicated as another artifact table.

The final specification must state these as four separate inventories:

1. source-environment sections;
2. direct artifact manifest sections;
3. recursively reachable declaration nodes; and
4. opaque referenced subjects that seal authenticates only as shaped
   identifiers.

That removes the current ambiguity between “seven source sections,” “six
protocol-entry families carried directly or conditionally,” and the additional
construction section. It also prevents a generic digest walk from importing
claim anchors or post-seal relation objects into seal authority.

A digest reference supplies content identity. It does not supply the preimage,
validate its schema, resolve its typed edges, establish ABI agreement, execute
an opaque predicate, or establish the truth of a declaration. Admission must
perform the applicable operations explicitly.

### 5.3 Internal canonical identity projection

The target identity relation is:

```text
CanonicalProtocolForm = normalize(ProtocolRoot)
ProtocolId = SHA256("zkc/pir\n" || encode(CanonicalProtocolForm))
```

`CanonicalProtocolForm` is:

- the one deterministic identity projection;
- a one-way normalization of the complete root;
- permitted to erase authoring names and ordering differences covered by the
  declared equivalence;
- forbidden from introducing independently authored facts;
- not a second semantic subject;
- not a supported ingress format;
- not a persisted capability; and
- not an external compatibility promise at v0.

At v0, `ProtocolId` permanently identifies the canonical preimage bytes, but
the repository does not promise that every future checker revision assigns
those bytes the same admitted meaning. Semantic statements involving a
Protocol must therefore be understood inside a named or locally fixed
`SemanticRegime`. A stable regime reference is required before admission
capabilities, caches, or independent checkers cross build or specification
revisions.

The current implementation approximates this role in
[`CanonicalEncoder.cpp`](../../lib/Encoding/CanonicalEncoder.cpp): it derives
event, transformer, and claim positions, builds a positional JSON document,
emits canonical JSON bytes, and hashes those bytes under the PIR domain tag.
The future normative identity owner must define enough grammar for an
independent implementation without making the diagnostic JSON view a public
wire format by accident.

### 5.4 Identity inclusions

The complete identity inventory must include, exactly once:

- event order, absorption, event kinds, typed payloads, domains, challenge
  spaces, dependencies, parameters, semantic arguments, and selected checks;
- normalized claim descriptors, exact anchors, reduction contracts,
  consumed-claim occurrences, produced profiles, and output anchors;
- terminal kinds, terminal-rule citations, route references, and selected
  discharge checks;
- `SealPolicy`;
- construction selection, semantic constants or references, and every
  consumed construction declaration pin;
- the direct typed vocabulary manifest;
- `MaterialBinding` edges;
- construction-route shape, HoleContract pins, normalized inputs, parameters,
  and witness payload classes;
- nontrivial spine segmentation; and
- every other Protocol-owned field whose change alters the accepted statement,
  transcript bytes, challenge authority, claim flow, or seal decision.

An external interface field that changes proof ABI follows the unresolved
`ProtocolInterface` decision instead: it must enter `ProtocolId`, enter a
separate `InterfaceId`, or be replaced by a canonical root-derived position.
It cannot be silently covered by the catch-all above.

Exact claim occurrences remain scoped by the enclosing `ProtocolId`. A claim
descriptor digest alone is not a globally unique occurrence identifier.

### 5.5 Identity exclusions

Unless a later decision changes their role, the Protocol identity excludes:

- the stored Protocol ID itself;
- the artifact filename and filesystem path;
- `protocol_name` and presentation-only SSA names;
- source locations and discardable diagnostic metadata;
- recomputable event, challenge, claim, check, and obligation tables;
- uncited environment entries;
- soundness rules, theorem selections, derivations, and judgments;
- post-seal relation-correspondence attachments;
- backend implementation names, scheduling, calibrations, and run results;
- evidence and reliance metadata; and
- transport producer markers and bytecode layout.

Every exclusion must satisfy a downstream-closure condition:

> If a later semantic or identity-bearing transition consults an excluded
> value, that value must be an explicit independently authenticated input to
> the transition or the transition must use a canonical value derived from the
> identified root.

This condition catches hidden dependencies without forcing every operational
name into Protocol identity.

### 5.6 Label and ABI pressure

The current model does not yet meet that condition uniformly. PIR author labels
are normalized away from Protocol identity, while OIR treats statement and
witness labels as identity-bearing ABI and relation correspondence uses labels
as wiring. Consequently, one `ProtocolId` can currently correspond to several
OIR IDs or correspondence inputs when only those carrier labels differ.

This baseline asked Stage 2 to compare three explicit choices:

1. make a `ProtocolInterface` part of the Protocol root and identity;
2. identify `ProtocolInterface` separately and make OIR and relation judgments
   cite `(ProtocolId, InterfaceId)`; or
3. remove the names from endpoint semantics and derive canonical ordinal names.

The selected architecture chooses the second direction, with the more precise
name `ProtocolInterfaceId` and with `ProtocolId` included in that dependent
identity. A future projection consumes the admitted Protocol and admitted
Protocol Interface explicitly. The current implementation may still consume
carrier-qualified ABI material until implementation and normative migration
occur.

## 6. Environment and admission

### 6.1 Four different graphs or closures

The design must name four different closures:

| Closure | Contents | Identity role |
|---|---|---|
| Protocol byte-identity closure | Complete `CanonicalProtocolForm` including typed declaration digests | Determines `ProtocolId` |
| Seal semantic-authority closure | Reachable declaration preimages needed to resolve and re-run the seal predicate | Nodes have their own content identities; no new Protocol id |
| Referenced-subject graph | Opaque anchors, material references, and external subject identifiers | Seal validates only their declared shape and use; it does not acquire interpretation authority |
| Execution or supplier closure | Concrete implementations and runtime behavior used to realize construction and endpoint requirements | Separate realization authority; not silently part of Protocol identity |

The second and third closures must not be conflated. A typed reference to an
opaque subject does not authorize seal to load or interpret that subject as a
declaration. The second and fourth closures must also remain distinct: pinning
a construction description or contract selects required semantics and shape;
it does not by itself establish that one concrete runtime supplier implements
them.

### 6.2 Protocol environment as resolver

The provisional semantic role of `ProtocolEnvironment` is a resolver and
provider:

```text
resolve(root, environment) -> SealAuthorityGraph(root) or refusal
```

The environment may contain uncited entries. Two environments are
Protocol-equivalent for one root when they supply the same validated reachable
authority graph under the same normative checking regime:

```text
E1 =~root E2
    iff resolve(root, E1) = resolve(root, E2)
```

This equivalence does not require or create a global environment identity. It
explains why adding an uncited registry entry can leave admission and
`ProtocolId` unchanged.

### 6.3 Admission basis

For one Protocol, the conceptual admission basis is:

```text
AdmissionBasis(root, E) =
    root
  + verified SealAuthorityGraph(root) supplied by E
```

It is not the complete environment by default. It also does not grant authority
over `ReferencedSubjectGraph(root)`. The current implementation may
retain the whole immutable `ProtocolEnvironment` because later consumers need
a resolver, but that retained object has a broader operational role than the
minimal Protocol admission basis.

The complete admission judgment additionally names the seal predicate and
`SemanticRegime`; they qualify how the basis is interpreted rather than being
duplicated inside it. Any consumer that consults uncited environment entries
must declare a separate authority input. The Compiler already has such a
distinct role: its configured
semantics reference covers the complete compiler environment, whereas
`ProtocolId` covers only the cited Protocol closure. These identities answer
different questions and must retain different names.

### 6.4 No portable admission receipt yet

An `AdmittedProtocol` is process-local authority. Copying the opaque capability
inside its protection boundary may preserve authority; serializing the subject
does not. A new process receives raw bytes and must decode, resolve, and admit
again.

This design does not introduce an admission certificate or checker receipt.
Stage 2 likewise selected no default portable witness. Any future proposal must
name its exact claim, consumer, checker, environment dependencies, replay
behavior, and identity. Current recomputation is not proof-carrying code.

### 6.5 Semantic-regime scope

The present capability is safest to interpret as process- or build-local:

```text
AdmittedProtocol[
  ProtocolId,
  AdmissionBasis,
  SemanticRegime
]
```

`SemanticRegime` includes the interpretation of intrinsic Protocol operations,
policy names, canonicalization, and seal predicates that are not supplied by
the artifact's declaration graph. It does not need a new public ID merely to
describe current in-process use. It must acquire a stable reference before a
long-lived cache, external checker, or cross-version API treats two admissions
as comparable.

## 7. PIR carrier correspondence

### 7.1 Sole supported v0 carrier

PIR/MLIR remains the v0:

- authoring surface;
- structural verification framework;
- transformation workbench;
- location-aware diagnostic surface;
- in-memory representation; and
- persisted bytecode carrier.

The target interpretation relations are:

```text
interpretOpenPIR : StructurallyValidOpenPirCarrier -> ProtocolDraft
interpretDecodedPIR : DecodedPirCarrier -> ProtocolRoot
```

`StructurallyValidOpenPirCarrier` is a descriptive input set, not a new public
capability: it means Open PIR that passes the applicable carrier formation and
structural checks, without seal authority. `DecodedPirCarrier` has already
authenticated sealed carrier shape and content identity but has not yet
re-established registry-backed admission.

The mapping is lossless with respect to Protocol semantics, not necessarily
textually or byte-for-byte reversible. Presentation names and discardable
metadata may disappear. Unknown semantic constructs must refuse rather than be
dropped.

### 7.2 Anti-drift obligations

The Protocol-to-PIR mapping must satisfy:

1. every PIR field is classified as Protocol semantics, authoring metadata,
   carrier metadata, explicit interface/ABI input, derived view, operational
   provenance, or evidence;
2. every Protocol field is represented or derivable exactly once;
3. every accepted PIR operation and property has one Protocol interpretation;
4. every identity-bearing field reaches `CanonicalProtocolForm` exactly once;
5. no value erased from identity is later consumed implicitly by a semantic
   transition;
6. structural verifiers cannot create facts that the Protocol owner never
   defines;
7. consumer views are derived from admitted inputs, not accepted from a
   producer as mirrored truth; and
8. a mapping change that alters meaning, judgments, or identity is reviewed as
   a Protocol change rather than labeled carrier-only.

The C++ encoder and the Python reference model can provide differential
evidence for this correspondence. Neither implementation becomes the owner.

### 7.3 Why the current canonical JSON is not a second carrier

The current encoder has no supported inverse decoder and v0 promises only
content identity, not encoding or tool-output stability. Treating its JSON as
an external format today would add a decoder grammar, unknown-field policy,
compatibility responsibility, declaration-packaging problem, and external
trust boundary without a current consumer.

An internal deterministic identity form can be observable for diagnostics and
testing without becoming supported ingress.

### 7.4 Trigger for a separate representation domain

A separate `representation/` domain or external checker package becomes
justified when at least one real pressure exists:

- a second production carrier;
- a non-C++ checker that must ingest complete Protocols;
- a stable cross-process or cross-organization exchange boundary;
- shared package mechanics used by several semantic artifact kinds; or
- first-class remote retrieval of content-addressed declarations.

At that point the new package must be explicitly versioned and map to the same
`ProtocolRoot`. It may reuse canonical-form bytes only after those bytes are
deliberately promoted into a stable decoder contract.

## 8. Minimum lifecycle transition ledger

Stage 2 subsequently selected the complete transition architecture. This
superseded Stage 1 page fixes only the earlier minimum non-overlapping meaning
of each role:

| Transition | Input | Successful result | Identity effect | Authority gained or lost |
|---|---|---|---|---|
| author or edit | authoring inputs and Open PIR | `ProtocolDraft` | none | none |
| link | two drafts, faces, one resolver environment | new `ProtocolDraft` | none until later seal | no inherited sealed authority |
| resolve for seal | draft and environment | `ResolvedSealCandidate` | none | exact candidate declaration material only |
| seal | resolved candidate | `SealedProtocol` and its PIR carrier | mint `ProtocolId` | seal predicate established at that boundary |
| persist | identified PIR carrier | `PersistedPirArtifact` | preserves Protocol id; bytes are not the id | process-local capability does not transfer |
| decode | raw persisted bytes and optional expected id | `DecodedPirCarrier` | recomputes same Protocol id | carrier, structure, and identity only |
| admit | decoded carrier and resolver environment | `AdmittedProtocol` or carrier-qualified equivalent | no new id | full seal predicate re-established under the resolved basis |
| derive view | admitted input and consumer adapter | ephemeral `ConsumerView` | normally none | only the named, derived facts |
| analyze | admitted subject, exact target, immutable analysis context/catalog authority, and explicit plan with typed assumptions | derivation and conditional judgment | judgment owner decides its id | no mutation or theorem transfer into Protocol |
| reopen | admitted subject | unauthoritative mutable draft clone | old id is stale and has no authority on the clone | admission authority deliberately discarded |
| checked transform | admitted predecessor, transform family, request, and compiler authority | admitted successor | recomputes successor `ProtocolId`; the identity plan preserves the predecessor id | successor reauthenticated independently |
| project | admitted Protocol or carrier-qualified source, endpoint kind, and any explicit extra inputs | OIR artifact and paired projection capability | new OIR id; source Protocol id retained as provenance | endpoint coverage only |

Failure categories remain qualified. Malformed carrier, identity mismatch,
seal inadmissibility, unsupported projection, negative analysis conclusion,
compiler illegality, and runtime failure are not one generic invalid state.

## 9. Downstream consumer constraints

### 9.1 Consumer-product categories

The word “view” applies only to ephemeral, mechanically derived input facts.
The downstream model must keep three categories separate:

| Category | Examples | Identity and lifetime |
|---|---|---|
| Ephemeral authenticated view | MLIR-free analysis facts, compiler observations | Process-local; normally no independent identity |
| Admission or paired capability | `AdmittedProtocol`, projected source/OIR pair | Process-local authority over exact subjects |
| Durable derived artifact or judgment | OIR artifact, relation correspondence, derivation judgment | Independently owned content or judgment with its domain-defined identity |

### 9.2 Relations

Post-seal relation correspondence consumes one exact sealed Protocol and a
separately authenticated `RelationContract`. It does not change Protocol
identity and must state whether its subject is the entire Protocol or an exact
claim occurrence. Pre-seal relation-interface ingress is a different future
role and cannot be retrofitted through a post-seal evidence attachment.

Relations that use statement or event names also require the unresolved
`ProtocolInterface` role; they cannot treat a relabel-invariant `ProtocolId` as
the complete naming interface.

### 9.3 Analysis

Analysis needs an immutable, representation-independent view tied to
`ProtocolId` and exact occurrence references. It must receive an explicitly
selected immutable context whose catalog owns executable rules and bindings, an
exact target, and an explicit plan. Typed external assumptions enter through
the plan and remain hypotheses in the result; arbitrary hypotheses are not a
parallel free-form input. The Protocol carries no theorem, and the analysis
view is not another Protocol schema.

### 9.4 Compiler

Compiler transformation consumes an admitted predecessor and a distinct
compiler-semantics authority. It creates an open clone internally, checks each
candidate transition, reseals every successor, and authenticates the recomputed
Protocol ID. The empty identity plan reproduces the predecessor artifact; a
content-changing plan may produce a different ID. The complete compiler
environment may legitimately affect
compiler configuration identity without entering the predecessor's
`ProtocolId`.

### 9.5 OIR projection

Projection consumes admitted source authority and creates an independently
identified endpoint artifact. A paired projected capability can retain the
stronger source-relative coverage judgment; raw serialized OIR must be
authenticated again and cannot recover source coverage from its own structure
alone.

Projection also exposes the strongest current counterexample to a pure
Protocol-only handle: some endpoint ABI labels survive in the PIR carrier but
are erased from Protocol identity. The transition contract must make that
dependency explicit or remove it.

### 9.6 Realization and execution

Realization consumes authenticated OIR plus exact suppliers and environmental
bindings. Supplier pins and configuration digests select required behavior;
they do not establish implementation correspondence by themselves. Successful
execution is an observation about one invocation, not a new fact about Protocol
identity or a general conformance result.

### 9.7 Independent checking

An independent checker needs:

- an ingress representation;
- the expected Protocol ID when known;
- all reachable declaration preimages;
- the normative canonicalization and seal predicates; and
- any consumer-specific question and authority.

The current Python reference model shows that an independent semantic model and
encoder are feasible without importing the C++ MLIR types. It is differential
evidence, not a supported persisted-artifact checker or a second specification.

## 10. Alternatives considered

The original candidates answer two different axes: semantic ownership and
lifecycle authority. The comparison therefore does not force one bundled
winner.

| Candidate | Main value | Main cost or risk | Provisional result |
|---|---|---|---|
| A. PIR-centered Protocol | Lowest immediate change and maximum direct MLIR leverage | Makes independent semantics and future carriers depend on the dialect contract | Retain as implementation posture; do not make PIR the sole semantic authority |
| B. Carrier-independent Protocol with PIR carrier | One complete semantic owner, cleaner identity, independent checker path | Can become a manually synchronized mirror if materialized without a consumer | Adopt as an abstract normative model and checked mapping, not a duplicate DTO |
| C. Separate Protocol and representation domains | Clean multi-carrier ownership and exchange | Adds a second concrete schema, version surface, and ownership seam too early | Defer until a real second carrier or external trust boundary exists |
| D. Capability-oriented lifecycle | Makes operational predicates and consumer authority non-overlapping | Too many wrappers can obscure the model if types are created without distinct predicates | Adopt as an orthogonal rule; combine roles in code only when meanings remain explicit |
| E. Semantic root, internal identity form, PIR adapter, and capabilities | Preserves MLIR benefits while opening independent checking and precise authority | Requires a complete field/mapping ledger and downstream closure checks | Preferred in this superseded baseline |

### 10.1 Why E is not a new universal IR

`ProtocolRoot` is the semantic object already presupposed by the kernel and
carrier. It is not an execution IR, backend IR, proof calculus, transition
record, or general artifact framework. PIR remains the concrete language in
which v0 Protocols are authored and stored.

### 10.2 Opportunity map

The preferred model enables or preserves:

- a small independent seal checker once ingress is deliberately specified;
- multiple carrier implementations later without rotating Protocol meaning;
- exact caching or packaging by `ProtocolId`, semantic regime, and reachable
  seal-authority graph;
- smaller consumer APIs derived from one admitted root;
- explicit compiler configuration identity without polluting Protocol identity;
- independent rechecking without a producer-populated validation flag; and
- a clear versioning trigger for external exchange.

It deliberately forecloses:

- treating a `pir.sealed` mnemonic or stored Boolean as admission authority;
- carrying capability authority through arbitrary serialization;
- allowing uncited environment entries to change Protocol meaning silently;
- letting consumer views become independently authored semantic mirrors;
- exposing the current canonical JSON as a stable wire contract accidentally;
- and permitting downstream semantics to depend on erased carrier metadata
  without an explicit input.

## 11. Scenario and counterexample results

### 11.1 Minimal closed Protocol

One small Protocol needs no representation domain. Draft, seal, persist,
decode, and admit remain distinct while sharing one `ProtocolId` after seal.

### 11.2 Relation-bound Protocol

Opaque anchors and `MaterialBinding` edges can remain identified Protocol
content while a post-seal relation contract separately interprets their role.
Future pre-seal relation-interface facts must be typed cited inputs if they can
change Protocol meaning. They do not become true merely by being cited.

### 11.3 Checked compiler transform

The preferred model naturally represents a checked successor relation. The
empty identity plan may return the same identified Protocol; a content-changing
plan returns a separately identified successor. The open clone is an
implementation mechanism with no authority, and the full compiler environment
remains a separate configured authority.

### 11.4 OIR projection

The paired projected capability and standalone OIR are different authority
states. The witness-label counterexample showed that projection inputs were not
fully closed by `ProtocolId`. Stage 2 resolved the extra ABI dependency through
an exact admitted Interface and tagged Plan basis rather than claiming pure
function behavior from `(ProtocolId, endpoint_kind)`.

### 11.5 Independent checker

The model supplies a provisional abstraction target sufficient for transition
research but intentionally leaves the normative algebra, carrier grammar, and
independent-checker ingress open. A future checker can either decode PIR/MLIR
independently or consume a new versioned checker package. No second format is
required to complete the Stage 1 factorization today.

### 11.6 Raw sealed carrier

A raw `pir.sealed` operation can have a correctly shaped ID field without
registry admission and can be directly mutated in C++. This does not falsify
the model; it confirms that carrier state and semantic authority are separate.
Persistence and consumer APIs should eventually state whether they require a
minted or admitted capability rather than accepting an unqualified raw op.

## 12. Implementation correspondence and target pressures

### 12.1 Strong correspondence

The current implementation already provides most lifecycle mechanics:

- `pir.protocol` and `pir.sealed` have separate carrier roles;
- `SealEngine` centralizes mint and recheck;
- canonical identity is over operation state rather than text or bytecode;
- persistence and decode recompute identity;
- decoded and admitted artifacts are opaque, copy-only handles;
- analysis and projection privately derive consumer objects;
- compiler successors are reopened, transformed, resealed, re-admitted, and
  independently checked; and
- linking returns a new open proposal.

### 12.2 Conceptual gaps to close before normative cutover

The future corpus must resolve, in exact owners:

1. the complete Protocol algebra and identity-field inventory;
2. the canonical byte grammar and optional-field rules;
3. source vocabulary, direct manifest, and transitive authority-graph
   inventories;
4. the complete `SealPolicy` matrix;
5. construction-profile, IV, constants, semantic-regime, and supplier authority
   boundaries;
6. `persist`, `decode`, and `admit` as first-class transition contracts;
7. label classes and their Protocol/OIR identity effects;
8. the producer marker's precise transport role;
9. link policy composition and other link-time semantic choices;
10. relation-correspondence subject granularity and result identity;
11. compiler configured-reference grammar and complete-environment authority;
12. stored IDs, computed semantic views, and process-local capability rules;
13. whether persistence should accept a raw sealed carrier or a stronger
    mint/admit capability; and
14. the concurrency and lifetime contract of shared in-process capabilities.

These are architecture and normative-ownership pressures, not security
findings and not automatic implementation-change requests.

### 12.3 No identity migration is selected here

This proposal aims to describe the current identified content completely before
changing it. Completing the abstract owner, adding lifecycle names, or making
the PIR mapping explicit need not rotate existing IDs.

Changes such as identifying a `ProtocolInterface`, promoting ABI labels into
Protocol identity, altering the
canonical grammar, completing missing construction semantics, or changing
domain tags can rotate identities. Each requires a separate migration decision
with current-to-target vectors and independent encoder agreement.

## 13. Previous provisional decisions and reversal conditions

### 13.1 Selections supplied to the first Stage 2 attempt

The following list records the baseline that the initial Stage 2 work received.
It is preserved for comparison and has no inherited force after Stage 1
convergence. The selected replacement is the
[Protocol IR Architecture](../project/protocol-ir-architecture.md).

1. The durable semantic subject is `Protocol`; PIR is its sole supported v0
   authoring and persistence carrier.
2. `ProtocolRoot` must become a complete abstract object, but no second
   materialized DTO or wire schema is authorized.
3. One internal `CanonicalProtocolForm` owns identity projection and is not
   supported ingress.
4. The root contains typed seal-authority commitments; reachable declaration
   preimages are supplied separately for resolution and admission, while
   opaque referenced subjects remain outside seal authority.
5. Protocol identity, admission basis, retained resolver environment, compiler
   configuration identity, and execution supplier authority are separate axes.
6. Decoded and admitted roles are carrier envelopes or capabilities over the
   same Protocol identity. Ephemeral consumer views remain derived, while OIR,
   relation judgments, and other durable results retain their own domain-owned
   identities.
7. Serialization ends capability continuity.
8. No consumer may depend implicitly on carrier data erased from Protocol
   identity.
9. The top-level domain remains `pir/` for now.
10. A separate representation domain and external checker package are deferred
    until a real consumer creates the corresponding boundary.
11. Admission authority is scoped to a semantic regime; cross-version reuse
    requires that regime to become explicit and stable.

### 13.2 Reopening criteria used by the previous model

- the abstract root cannot be kept mechanically aligned with PIR;
- a materialized carrier-independent object becomes a manual mirror with no
  real consumer;
- canonical field coverage cannot be independently checked;
- a downstream consumer cannot express its exact inputs without violating the
  root/carrier distinction;
- an independently evolving prover construction plan becomes valuable enough
  to separate from the verifier-facing Protocol root;
- a second production carrier or external checker creates a real exchange
  contract;
- the selected factorization would require identity migration without
  corresponding semantic or product benefit; or
- capability proliferation is less clear than an explicit runtime state
  machine in a target language.

Reopening the language-level capability encoding does not permit collapsing
the underlying predicates. Reopening the root should first consider a leaner
abstract inventory and mapping before promoting MLIR into permanent semantic
authority.

### 13.3 Previous latest-responsible directory criterion

Rename `pir/` to `protocol/`, or introduce a separate representation domain,
only after at least one of these holds:

- a complete Protocol specification is consumed without PIR carrier details;
- a second durable carrier maps to the same root;
- an independent checker needs a stable non-PIR ingress; or
- the current directory demonstrably forces semantic and carrier ownership to
  diverge in maintained documents.

Until then, `pir/` may own both the Protocol semantics and its sole carrier
mapping as explicitly separated sections.

## 14. Previous Stage 2 entry contract — superseded

The initial Stage 2 attempt was allowed to treat the following as its
provisional subject vocabulary. Reopened Stage 1 later revised it:

```text
ProtocolDraft
ResolvedSealCandidate
ProtocolRoot
SealAuthorityGraph(root)
ReferencedSubjectGraph(root)
SealedProtocol[ProtocolId] under SemanticRegime
PersistedPirArtifact[ProtocolId]
DecodedPirCarrier[ProtocolId]
SemanticRegime
ProtocolInterface or canonical positional interface
AdmittedProtocol[ProtocolId, AdmissionBasis, SemanticRegime]
AdmittedPirCarrier[
  ProtocolId,
  AdmissionBasis,
  SemanticRegime,
  CarrierContext,
  RetainedResolverEnvironment
]
ProtocolSubjectRef
ConsumerView
DerivedArtifactOrJudgment
```

Stage 2 did not assume that every role deserved a public type, serialization,
or stable identity. Its completed transition architecture determined, at
architectural resolution, the following questions transition by transition:

- source and target subject;
- authenticated authority inputs;
- carrier-only and ABI inputs;
- binding time;
- success and typed refusal;
- identity preservation or change;
- exact preservation, refinement, correspondence, or derivability claim;
- capability gained, narrowed, or discarded;
- replay and serialization behavior; and
- residual trust and non-claims.

The first counterexample to resolve is the relabel-invariant PIR identity versus
identity-bearing OIR and relation interfaces. The first authority distinctions
to preserve are seal authority versus opaque subject references, and cited
Protocol closure versus the complete compiler environment.

## 15. Research basis and limits

The [MLIR Language Reference](https://mlir.llvm.org/docs/LangRef/) describes
textual, in-memory, and compact serialized forms as representations of the same
semantic content. That supports retaining MLIR as a productive carrier while
keeping the domain object conceptually distinct. It does not supply zkc's
Protocol semantics.

MLIR's [interface model](https://mlir.llvm.org/docs/Interfaces/) shows how
analyses and transformations can consume abstract behavior without
special-casing every operation. It motivates derived consumer interfaces but
does not prove that any zkc view is complete.

The [MLIR bytecode specification](https://mlir.llvm.org/docs/BytecodeFormat/)
states that compatibility assumes immutable dialect definitions unless a
dialect takes responsibility for versioning and upgrade hooks. This supports
separating transport evolution from Protocol identity and deferring a stable
exchange contract at v0; it does not require zkc to add legacy decoders now.

Liskov and Zilles' work on
[specification techniques for data abstractions](https://research.ibm.com/publications/specification-techniques-for-data-abstractions--1)
supports specifying the subject at the right abstraction level rather than
equating it with one representation. The lesson used here is architectural,
not a correctness result.

Producer/consumer checking systems such as
[Proof-Carrying Code](https://people.eecs.berkeley.edu/~necula/ISSS02/) clarify
why supplied material and consumer recomputation should be distinguished.
Current zkc artifacts do not carry a portable proof certificate, so the
analogy stops at the separation of proposal and checking.

The original object-capability definition describes a capability as a narrow
token that designates an object and permits access to it. Here the term is used
only for an opaque authenticated API handle. The current C++ types are not a
general access-control or object-capability claim.

No source in this section establishes that zkc's current specifications are
complete, that its implementation conforms, or that a cryptographic property
holds. Those remain separate specification, conformance, and analysis tasks.
