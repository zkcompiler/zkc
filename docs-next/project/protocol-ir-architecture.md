# Protocol IR architecture

> **Document kind:** Architecture decision
> **Document state:** Active
> **Target decision status:** Selected Stage 1 package result; integrated
> semantic-kernel closure remains under revalidation
> **Provisional owner:** `project`
> **Authority:** Non-normative target architecture for `docs-next/`. The current
> specifications under [`docs/`](../../docs/README.md) remain authoritative
> until normative consolidation and explicit cutover. This decision selects
> the semantic and representation backbone; it does not claim implementation.
> The [v0 Semantic Design Program](v0-design-program.md#14-progress-and-change-control)
> owns the live integrated-closure gate.

> **K1/K2 reconciliation notice — 2026-08-26:** The architectural
> factorization remains a design input, but the body below predates
> [Executable Semantic Foundations](../foundation/executable-foundations.md),
> the active [Interactive Core](../pir/interactive-core.md), and the active
> [Fiat--Shamir construction](../pir/fiat-shamir.md). Its public-coin Core,
> port, abstract-prover-obligation, authored FS-map, and whole-Plan endpoint
> examples are historical where they conflict with those owners. K3-B must
> reconstruct Interface, Plan, Relations, and carrier consumers; K3-D must
> close the exact endpoint read and identity effect. This page is not an
> integrated semantic-kernel decision by itself.

## 1. Decision

The v0 target is a **layered canonical Protocol architecture**:

```text
rich MLIR authoring, import, and synthesis workbench
        |
        | exhaustive elaboration, closure, and normalization
        v
small closed canonical PIR level in MLIR
        |
        | authentication and whole-Protocol admission
        v
opaque immutable AdmittedProtocol capability
        |
        +--> Analysis judgments
        +--> checked Protocol successors
        +--> ProtocolInterface- and role-bound OIR projection
        +--> tagged ProverPlan basis at projection or realization
        `--> purpose-specific views or certificates when justified
```

Protocol meaning is specified independently of MLIR. MLIR remains the primary
structural carrier and transformation infrastructure for v0; it does not
define the semantics, identity, admission result, or correctness of a
transformation.

The canonical level is a real IR level, not merely a `sealed` flag on an
arbitrary authoring object. It has a closed vocabulary, one normalized
semantic operation graph per admitted Protocol, a selected total observable
schedule, and no unresolved or authoring-only content. The final spelling and
source layout are not selected here, but the intended ownership is that
**PIR names this canonical level**, while upstream authoring and import
dialects remain separate workbench languages.

This selects the strengthened form of research Candidate B, supplemented by
purpose-specific derived views. It does not select a complete parallel Rust
model, a carrier-neutral runtime package, a VHLO-like compatibility dialect,
or a universal fact database.

## 2. Why this boundary exists

The authoring-to-canonical boundary changes all of the properties that justify
a durable IR level:

1. an incomplete design, family, or proposal becomes exactly one Protocol;
2. unresolved choices and external names are either fixed, extracted into
   separately identified subjects, or rejected;
3. the legal extension set becomes closed;
4. exploratory rewrites become immutable-subject transitions requiring a
   named checked relation;
5. rejection-relevant distinctions must be validated before any irreversible
   erasure;
6. identity, admission, Analysis, and endpoint projection begin consuming the
   result; and
7. the result becomes small enough to admit without importing the optimizing
   pipeline.

Keeping those two roles in one unrestricted lifecycle dialect would make every
consumer responsible for respecting a semantic quotient over mutable carrier
state. Making a complete non-MLIR package primary would instead introduce a
second full representation and make MLIR/package correspondence the central
bridge before an independent consumer requires it. The selected boundary
avoids both global burdens.

## 3. Semantic subject model

### 3.1 `SemanticRegime`

A `SemanticRegime` fixes the interpretation required to compare or admit a
semantic subject. Regimes are typed by subject family rather than forced into
one global release number. A Protocol regime, Interface regime, and ProverPlan
regime may evolve independently while their dependent identities retain the
exact cross-reference. A regime owns:

- canonical operation and contract meanings;
- protected observation classes and intrinsic effects;
- framing and sampling primitives;
- whole-object admission rules;
- dependency-schema interpretation; and
- the semantic identity encoding domain.

It is not a tool release, MLIR bytecode version, dialect transport revision,
or local acceptance policy. Different meanings under the same carrier body
must not share a semantic identity.

### 3.2 `InteractiveCore`

An `InteractiveCore` is one ordered public-coin protocol, not an unordered
protocol template. It owns:

- roles and canonical typed semantic ports;
- typed prover and verifier events;
- fresh public-coin challenge occurrences and distributions;
- mandatory causal dependencies;
- one identity-bearing total observable schedule extending those dependencies;
- the claim, reduction, check, and terminal graph;
- abstract prover obligations;
- exact failure outcome classes; and
- typed semantic dependency references.

The total schedule belongs here because an interactive protocol is already an
ordered conversation. Fiat--Shamir compilation interprets that history; it
does not first invent its order. Partial-order authoring is allowed upstream,
but it denotes a scheduling problem or family until one total schedule is
selected. Different linear extensions normally have different `CoreId`s.

If a genuinely unordered batch is intended, it must be represented as one
explicit unordered aggregate event with specified internal semantics. It is
not obtained by silently quotienting permutations of separately observable
events.

### 3.3 `ChallengeInterpretation`

A Protocol selects exactly one challenge interpretation:

```text
ChallengeInterpretation =
    FreshPublicCoins
  | FiatShamir(TranscriptConstructionId)
```

A `TranscriptConstruction` is scoped to an exact Core and owns:

- initialization and domain separation;
- the event-to-transcript-atom mapping;
- injective typed framing and codecs;
- absorb and squeeze behavior;
- sampling maps, counts, and failure behavior;
- oracle, sponge, or hash references; and
- composition-context binding.

Fresh-coin and Fiat--Shamir Protocols over one Core are distinct Protocols.
Their relationship is a theorem-backed `FSCompile` judgment, not identity or
an ordinary representation lowering.

### 3.4 `Protocol`

```text
Protocol = InteractiveCore + ChallengeInterpretation
```

It is the complete abstract verifier-visible protocol semantics. The Core
already owns canonical semantic ports, proof/message order, transcript-visible
bytes, checks, claim flow, and abstract prover obligations. No downstream
interface or plan may reinterpret them.

### 3.5 `ProtocolInterface`

A `ProtocolInterface` binds one Protocol's canonical semantic ports to one
external callable contract. It may own:

- application-facing ABI names and positions;
- external value representations that preserve the fixed semantic value;
- external statement and proof packaging or parsing that maps exactly to the
  canonical values and proof-event occurrences;
- externally observable malformed-input behavior and a terminal-only external
  outcome mapping; pure Interface codecs have no refusal branch;
- role entry points;
- relation/application port binding; and
- endpoint packaging that does not alter Protocol observations.

It is a dependent subject: its identity commits to the exact `ProtocolId`.
It may not change semantic public values, canonical proof-event order,
transcript inputs or any encoding observed by challenge derivation, challenge
behavior, checks, claim routing, or terminal outcomes. External packaging may
vary only when decoding occurs before the separately fixed Protocol meaning.
Any supposed interface field that changes that meaning belongs to a new
Protocol.

This gives one abstract Protocol several valid external interfaces without
allowing an interface-sensitive consumer to read unidentified carrier labels.
OIR projection and external correspondence consume
`ProtocolInterfaceId`, not a bare Protocol plus hidden metadata.

The acceptance distinction is:

```text
AcceptProtocol(x, proof_trace)

AcceptInterface(statement, proof_bytes) iff
  DecodeStatementInterface(statement) = x
  and DecodeProofInterface(proof_bytes) = proof_trace
  and AcceptProtocol(x, proof_trace)
```

Protocol-level claims quantify over the first relation. External endpoint
claims quantify over the second and therefore cite the Interface identity.
A decoder that restricts otherwise valid semantic values, injects semantic
defaults, hashes fields into new values, or changes the checked relation is not
a pure Interface; it is a policy, adapter, or wrapper Protocol with its own
semantic identity.

### 3.6 `ProverPlan`

A `ProverPlan` is another dependent subject over `ProtocolId`. It may own:

- witness and construction DAGs;
- plan-local algorithms, scheduling, parallelism, and buffering;
- abstract supplier requirements;
- permitted private dependencies; and
- typed holes whose contracts remain explicit.

The Protocol retains all verifier-visible behavior and the abstract prover
obligations needed to state honest-prover properties. If a plan changes a
proof message, required distribution, transcript action, proof ABI, check, or
accepted language, it denotes a different Protocol rather than another plan.

Plan well-formedness and obligation coverage are structural judgments.
Completeness is a separately qualified judgment over the Protocol, plan,
relation/witness assumptions, and supplier assumptions.

### 3.7 Downstream subjects

- `AdmittedProtocol` is a process-local immutable capability, not a serialized
  authority token or a new semantic identity.
- `ConsumerView` is a purpose-specific immutable derivation from admitted
  authority. It is not an independent source of Protocol truth.
- OIR is a new endpoint subject derived from an exact
  `ProtocolInterfaceId` and role, with its own identity and validity.
- A durable projection record or certificate may authenticate a source/target
  correspondence. A target artifact or digest does not prove its own
  derivation.
- Analysis, transformation, correspondence, completeness, realization, and
  reliance results remain distinct judgments owned by their domains.

## 4. Identity algebra

The exact hash and byte grammar belong to the normative identity
specification. Stage 1 selects the compositional preimage shape:

```text
CoreId = H(
  "zkc/core",
  ProtocolSemanticRegimeId,
  CanonicalEncode(InteractiveCore))

TranscriptConstructionId = H(
  "zkc/transcript-construction",
  ProtocolSemanticRegimeId,
  CoreId,
  CanonicalEncode(TranscriptConstruction))

ProtocolId = H(
  "zkc/protocol",
  ProtocolSemanticRegimeId,
  CoreId,
  FreshPublicCoins)

or

ProtocolId = H(
  "zkc/protocol",
  ProtocolSemanticRegimeId,
  CoreId,
  FiatShamir,
  TranscriptConstructionId)

ProtocolInterfaceId = H(
  "zkc/protocol-interface",
  InterfaceSemanticRegimeId,
  ProtocolId,
  CanonicalEncode(ProtocolInterface))

ProverPlanId = H(
  "zkc/prover-plan",
  PlanSemanticRegimeId,
  ProtocolId,
  CanonicalEncode(ProverPlan))
```

These are semantic content identities, not hashes of MLIR text or bytecode.
Raw carrier or package digests, if useful, are separate transport identities.

The architecture obeys four substitution rules:

1. equal semantic IDs imply equal normative consumer results for the same
   explicitly identified additional inputs;
2. two interfaces over one Protocol are substitutable only for consumers
   quantified over the abstract Protocol, not for interface-bound consumers;
3. two prover plans over one Protocol are substitutable only for
   verifier-level questions, not for plan-sensitive completeness or cost; and
4. a semantic-regime change cannot silently preserve an identity, even when
   the remaining canonical body is byte-for-byte equal.

Human-readable diagnostics, source locations, author handles, and pure
presentation aliases remain outside semantic identity. An ABI-significant
name belongs to `ProtocolInterfaceId`; a name that changes Protocol behavior
was misclassified and belongs upstream.

A durable endpoint reference is at least:

```text
EndpointContractRef = (ProtocolId, ProtocolInterfaceId, EndpointRole)
```

An `OirId` commits to that reference and the canonical OIR content. If a
selected ProverPlan changes prover OIR rather than merely realizing it below
OIR, `ProverPlanId` is also an explicit projection input; it cannot arrive as
ambient plan state.

## 5. Canonical PIR contract

### 5.1 Closed semantic assembly level

Canonical PIR denotes exactly one Protocol. A legal root contains only the
closed PIR vocabulary and a minimal allowlist of carrier primitives. It has:

- one explicit `ProtocolSemanticRegimeId`;
- one normalized `InteractiveCore`;
- one challenge interpretation and, when applicable, construction;
- fixed canonical semantic ports and occurrence positions;
- a complete typed dependency manifest;
- no unresolved references or choices;
- no foreign semantic operations;
- no authoring macros, synthesis requests, plan data, interface labels,
  source locations, or arbitrary metadata; and
- an abstract endpoint obligation for every admitted semantic event kind.

The last requirement means source-level obligation completeness, not that
every target or backend supports every event. A target-specific projection may
still refuse. Syntax with no abstract obligation rule is authoring-only until
its semantics is completed; it cannot enter an endpoint-ready admitted
Protocol under a generic `sealed` label.

### 5.2 Meaning of physical normal form

For one regime and one Protocol there is one legal canonical PIR operation
graph modulo MLIR object identity and SSA alpha-renaming. This does not promise
unique MLIR text, printer output, bytecode, allocation, or generic
canonicalizer output.

The canonical graph has fixed structure and ordering, explicit defaults,
canonicalized unordered collections, positional semantic references, and no
unclassified attributes. Its specified semantic encoder is bijective with
that legal graph modulo the allowed carrier trivia.

MLIR's generic canonicalizer is best-effort and therefore cannot define this
normal form. Full dialect-conversion legality can enforce that noncanonical
operations disappeared, but zkc's own whole-Protocol checker defines semantic
closure and admission.

### 5.3 Information-loss frontier

Before normalization erases a distinction, the source side must validate every
rule whose rejection depends on that distinction. The canonical result keeps
or makes explicit every protected observation, causal dependency, selected
schedule, framing rule, message/wire fact, claim-flow edge, semantic port,
failure class, and identity-bearing dependency.

Normalization may extract interface data, plan data, provenance, and source
maps into separately typed outputs. It may erase source spelling, macro shape,
redundant defaults, search history, and order proved irrelevant to every
protected observer. Raising a canonical Protocol into a workbench produces a
generic editable proposal; it cannot reconstruct the original source.

## 6. Lifecycle and authority

The selected roles are:

```text
AuthoringUnit
  -> ResolvedAuthoringUnit
  -> CanonicalProtocolCandidate
  -> AuthenticatedCanonicalProtocol
  -> AdmittedProtocol
```

- An `AuthoringUnit` is mutable and unauthoritative. It may be partial,
  mixed-dialect, or family-valued and has no stable `ProtocolId`.
- A `ResolvedAuthoringUnit` binds one immutable input snapshot and the complete
  dependency closure actually read; resolution still creates no Protocol
  authority.
- A `CanonicalProtocolCandidate` is a closed PIR graph claiming an identity.
  Its syntax or root name does not confer authority.
- Authentication checks the canonical profile and recomputes all declared
  identities and dependency closure.
- Admission checks whole-Protocol semantics under the exact regime and mints
  an opaque immutable capability.
- Serialization never preserves a process-local capability.
- Reopening or mutating admitted content discards admission; any result must
  cross the boundary again.

This is a lifecycle and subject decision. The selected
[Stage 2 transition architecture](transition-and-bridge-architecture.md)
records the selection of common contract invariants, authority effects,
outcome model, checker selection, and bridge layering. Foundation and the
concrete domains own their exact definitions. Exact domain schemas remain
downstream work.

## 7. Order, effects, and transformation relations

Canonical PIR distinguishes at least these protected observation classes:

```text
TRANSCRIPT  WIRE  PUBLIC  CHECK  ARTIFACT  CLAIM  TERMINAL
```

Pure SSA independence is insufficient to reorder actions observed by any of
these classes. A transform may rely on a named independence or trace relation,
but there is no unqualified `semantic equivalence` escape hatch.

The architecture reserves distinct relations for:

- `RepresentationEq`;
- exact `CoreEq` and `ProtocolEq`;
- observer-indexed `TraceEq`;
- `TraceRefines`;
- distributional equality or closeness;
- `FSCompile`;
- `ProjectionCorrect`;
- `PlanRealizes`;
- `PropertyTransport`;
- `IntentionalChange`; and
- an orthogonal cost relation.

Stage 1 fixes the need for these distinctions. Stage 2 selected their common
contract requirements and kept their inputs, issuers, validation bases, and
composition laws relation-specific rather than placing them in one universal
transition algebra.

## 8. Composition skeleton

Composition constructs a new `InteractiveCore`; it is not graph union or
string concatenation. Even the v0 skeleton must make explicit:

- tagged occurrence namespaces, including repeated use of the same child;
- child-to-composite port and claim face maps;
- causal seams and one selected total interleaving;
- whether challenges are independent, shared, or derived;
- transcript and construction domain separation;
- failure and terminal propagation; and
- the new dependency and abstract endpoint-obligation closure.

The composed Core receives a new `CoreId`. A fresh-coin or Fiat--Shamir
interpretation is then selected for the composite. Property transport,
endpoint descent, recursion, and IVC remain later questions; this skeleton
prevents the root model from making them accidental graph-splicing behavior.

## 9. Consumers and independent checking

Full v0 admission consumes canonical MLIR PIR, not the entire optimizing
compiler. A bounded implementation needs only MLIR core decoding, the closed
PIR grammar, semantic identity encoder, exact dependency resolver, and
whole-Protocol admission checker. It does not need authoring dialects,
optimizer passes, candidate search, OIR backends, or realization code.

Specialized consumers should receive the minimum immutable facts they need.
Views are derived capabilities in process. A persisted fact root, projection,
or certificate is introduced only for a named cross-process consumer and must
state what it authenticates. A digest authenticates bytes; it does not prove
completeness or correspondence.

A source-free OIR can establish its own shape, identity, and local validity.
It cannot establish that every source Protocol obligation was projected,
because omitted source information is unrecoverable. Source-relative coverage
requires the admitted source or sufficient source-bound projection evidence;
otherwise the correct result is `unknown` or refusal.

## 10. Evolution and compatibility

v0 is exact and fail-closed. It separately names:

- semantic regime;
- semantic identity encoding;
- canonical PIR schema;
- MLIR transport schema;
- semantic dependency schemas;
- local admission policy;
- ProtocolInterface, ProverPlan, and OIR schemas; and
- producer release.

A carrier revision may preserve a semantic ID only when it decodes to the same
canonical subject under the same regime. A semantic change mints a new subject
identity or is related by an explicit checked migration judgment. Decoder
success alone never establishes preservation.

Stage 1 deliberately does not promise historical compatibility or select a
portable compatibility representation. That work becomes mandatory when a
real boundary requires at least one of:

1. an independently released full-Protocol consumer that cannot depend on the
   restricted MLIR carrier;
2. long-lived external Protocol artifacts with a declared retention window;
3. independent producer and consumer release cycles;
4. a deployment or trust constraint that excludes MLIR; or
5. a formal extraction boundary requiring a complete stable neutral package.

At that trigger, Candidate D or a compatibility dialect is reconsidered with
an owned schema, exact upgrade rules, at least two independent decoders or
checkers, and an explicit compatibility window. Until then, a complete second
representation would freeze unresolved semantics and add bridge obligations
without a distinct consumer.

## 11. Capabilities gained

The selected architecture makes the following possible without conflating
their identities or authorities:

- reuse one interactive Core under fresh-coin and several Fiat--Shamir
  constructions while keeping each Protocol distinct;
- reuse Protocol-level Analysis across several external interfaces;
- project several externally callable contracts from one abstract Protocol;
- compare several prover plans for one verifier-visible Protocol;
- author in partial order or higher-level combinators while deploying one
  exact total schedule;
- let MLIR drive synthesis and optimization while a smaller boundary admits
  the chosen result;
- add purpose-specific independent checks without publishing a universal
  shadow IR; and
- evolve the carrier without treating transport bytes as semantic identity.

These are structural capabilities. They do not themselves prove soundness,
completeness, zero knowledge, projection correctness, or compilation
correctness.

## 12. Rejected alternatives and reversal conditions

### Lifecycle quotient as the primary boundary

Rejected for the target because every normative consumer would carry a global
obligation to ignore or separately identify all representative-only carrier
state. The current label/interface seam demonstrates how easy it is for that
obligation to leak. Reconsider only if authoring and canonical vocabularies
remain essentially identical and a genuinely small canonical level provides
no consumer or checking benefit.

### Carrier-neutral complete package now

Rejected for v0 because it duplicates the complete semantic schema and moves
trust to an MLIR/package correspondence bridge before a named independent
full-Protocol consumer exists. Reconsider at the compatibility triggers in
Section 10.

### Portable compatibility dialect now

Rejected because a compatibility representation is a durable product promise,
not a free consequence of versioned bytecode. Reconsider when external
retention and release windows are concrete.

### Universal fact root

Rejected because accumulated purpose-specific facts can become a lossy second
Protocol model without an explicit completeness contract. Small derived views
and certificates remain useful complements.

### One dialect per lifecycle state

Rejected. Draft, decoded, authenticated, and admitted roles differ mainly in
closure and authority, not necessarily operation denotation. Distinct types
and opaque capabilities express those states. The real dialect boundary is
between rich authoring meaning and the closed canonical Protocol level.

## 13. Stage 2 result and Stage 3 completion

Stage 1 exports the following fixed inputs to transition research:

- the subject and identity factorization in Sections 3 and 4;
- one rich authoring workbench and one closed canonical PIR level;
- language-independent semantics with MLIR as the v0 structural carrier;
- total schedule ownership in `InteractiveCore`;
- dependent `ProtocolInterfaceId` and `ProverPlanId` subjects;
- explicit semantic-regime qualification;
- fail-closed canonical extension and exact-v0 evolution rules;
- opaque admission capabilities and purpose-specific consumer views;
- the protected observation classes and named relation taxonomy;
- obligation-complete canonical admission with target-specific projection
  refusal; and
- the information limit on source-free OIR coverage.

Stage 2 could refine transition names and schemas, but could not silently move
an Interface field, ProverPlan field, regime qualifier, or observable effect
across these subject boundaries. A contradiction would have had to reopen the
affected Stage 1 decision explicitly.

Stage 2 completed on 2026-08-22 without reopening those boundaries. The
selected [Transition and Bridge Architecture](transition-and-bridge-architecture.md)
adds domain-owned contracts under shared invariants. In particular, it:

- separates carrier authentication from whole-Protocol admission;
- admits a changed target before checking its exact predecessor/successor
  relation;
- projects OIR from the exact Protocol, Interface, role, and tagged Plan basis;
- keeps `LocalOirValid` distinct from source-relative `ProjectionCorrect`;
- treats bytes as incapable of preserving process-local authority; and
- keeps observation, evidence, policy appraisal, and consumer reliance in one
  directional chain with no semantic backflow.

These are non-normative target decisions, not public API, schema,
implementation, or conformance claims. Stage 3 later consumed these inputs and
selected the package-resolution candidate recorded by the
[Protocol and Relations Architecture](protocol-and-relations-architecture.md).
That later decision refines rather than silently rewrites this Stage 1 record;
post-selection revalidation determines whether the integrated candidate is
closed enough to freeze.

## 14. Deliberate deferrals

Stage 1 did not select:

- exact dialect, operation, attribute, C++ type, or filesystem spellings;
- the complete normalized PIR grammar or hashing algorithm;
- the normalization algorithm, implementation, or proof/certificate format;
- every Interface and ProverPlan field;
- exact effect-interface implementation;
- the complete structural composition algebra;
- a consumer-view wire format;
- an OIR operational semantics or backend correspondence grade;
- a proof-assistant representation;
- a compatibility window or historical upgrade machinery; or
- migration and implementation sequencing from the current checkout.

Stage 3 subsequently selected candidate abstract Protocol grammar, canonical
PIR profile and bijection, Interface and Plan fields, and structural Core
composition at its non-normative package resolution. Integrated closure of
those candidate contracts is reopened. Concrete hash primitives, stable byte
encodings, implementation and proof artifacts, OIR semantics, compatibility
policy, and migration remain downstream. Historical deferral does not by
itself reopen the semantic ownership and representation decisions recorded
above.

## 15. Evidence and decision boundary

The decision is based on the zkc-native design-force and implementation
correspondence studies, cross-family case research, protocol-semantics study,
equal-resolution candidate instantiation, and protocol-specific scenario
evaluation recorded by the Stage 1 package in the
[temporary workspace inventory](../notes/README.md#working-note-inventory).

The external mechanisms are used with explicit limits:

- [MLIR dialect conversion](https://mlir.llvm.org/docs/DialectConversion/)
  supplies legality machinery, not Protocol admission;
- [MLIR generic canonicalization](https://mlir.llvm.org/docs/Canonicalization/)
  is best effort and cannot define zkc semantic normal form;
- [MLIR bytecode](https://mlir.llvm.org/docs/BytecodeFormat/) is a versioned
  container whose dialect compatibility still belongs to the dialect owner;
- [StableHLO compatibility](https://openxla.org/stablehlo/compatibility) and
  the [StableHLO/VHLO distinction](https://openxla.org/xla/terminology)
  demonstrate the value and permanent cost of an explicit compatibility layer
  after a real compatibility promise exists;
- long-lived IRs demonstrate that validation, environment, schema, transport,
  and producer versions must not be collapsed; and
- [multi-round Fiat--Shamir analysis](https://eprint.iacr.org/2021/1377.pdf)
  reinforces that ordered round history, construction semantics, and
  quantitative theorem conditions cannot be reduced to ordinary SSA
  equivalence.

This closes the bounded Stage 1 architecture-selection package. The Stage 2
and Stage 3 selections are separate dependent architecture results. None
authorizes normative cutover, implementation changes, migration, or automatic
activation of Stage 4.
