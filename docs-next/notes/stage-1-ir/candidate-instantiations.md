# Stage 1 candidate architecture instantiations

> **Document kind:** Temporary architecture research note
> **Document state:** Candidate instantiation for Stage 1 convergence
> **Authority:** None. This note compares complete candidate architectures at
> one semantic resolution; it does not ratify an architecture or define v0
> semantics.
> **Disposition:** Absorb the selected architecture and rejected-alternative
> rationale into durable owners, then delete this note at the documentation
> cutover.

## 1. Purpose and comparison discipline

The first research wave identified several representation directions but did
not instantiate them against one fixed semantic subject. Comparing a rich
neutral package with an underspecified MLIR dialect, or a full Protocol with a
fact view, would make representation preference look like a semantic result.

This note therefore gives strengthened Candidates A, B*, and D the same:

- Protocol semantics;
- factorization and identity boundaries;
- admission obligations;
- transform and projection obligations;
- consumer requirements; and
- fail-closed extension rule.

Candidate E is evaluated separately because it is a consumer-surface
complement, not a complete carrier for the common subject. Candidate C, the
immediate introduction of a stable compatibility dialect, is also not a
separate semantic architecture: it is a compatibility mechanism that could be
added to B* after a concrete compatibility contract exists.

The candidate vocabulary refines the preliminary portfolio in the
[cross-case synthesis](cross-case-synthesis.md). It is grounded in the
[current zkc correspondence](cases/current-zkc-correspondence.md), the
[Protocol-semantics theory study](cases/protocol-semantics-theory.md), the
[multi-level MLIR study](cases/multilevel-mlir.md), the
[portable-IR study](cases/portable-ir-contracts.md), and the
[long-lived-IR study](cases/long-lived-ir-contracts.md).

## 2. Common semantic subject

All three complete candidates carry the following model. Representation is
not allowed to change it.

### 2.1 Factorization

```text
SemanticRegime R[kind]
  = subject-family meanings and semantic dependencies
  + canonical semantic encoding and admission rules

InteractiveCore I
  = roles and typed semantic ports
  + typed protocol events
  + mandatory causal constraints
  + one selected total observable schedule consistent with those constraints
  + typed linear claim and reduction graph
  + public bindings, checks, and terminal behavior
  + abstract endpoint obligations

ChallengeInterpretation X
  = FreshPublicCoins
  | FiatShamir(TranscriptConstruction K)

Protocol P
  = InteractiveCore I + ChallengeInterpretation X

ProtocolInterface J
  = deployable binding from external ABI names and encodings
    to the canonical semantic ports of Protocol P

ProverPlan L
  = separately identified honest-prover construction for Protocol P
```

The total observable schedule belongs to `InteractiveCore`, not only to a
Fiat--Shamir compilation result. An interactive protocol is already an ordered
conversation. A workbench may permit a partially ordered template, but it must
select a total schedule before producing an admitted Core. The Fiat--Shamir
construction interprets that schedule; it does not invent the underlying
conversation order.

`FreshPublicCoins` and `FiatShamir(K)` produce different Protocol subjects.
They may be related by an explicit, theorem-backed Fiat--Shamir construction
judgment; they are not representation aliases.

### 2.2 Identity boundaries

Every candidate implements the same dependency-shaped identity model:

```text
CoreId
  = H(core-domain, ProtocolSemanticRegimeId, canonical InteractiveCore)

TranscriptConstructionId
  = H(construction-domain,
      ProtocolSemanticRegimeId,
      CoreId,
      canonical TranscriptConstruction)

ProtocolId
  = H(protocol-domain,
      ProtocolSemanticRegimeId,
      CoreId,
      FreshPublicCoins)
  | H(protocol-domain,
      ProtocolSemanticRegimeId,
      CoreId,
      FiatShamir,
      TranscriptConstructionId)

ProtocolInterfaceId
  = H(interface-domain,
      InterfaceSemanticRegimeId,
      ProtocolId,
      canonical ProtocolInterface)

ProverPlanId
  = H(plan-domain,
      ProverPlanSemanticRegimeId,
      ProtocolId,
      canonical ProverPlan)
```

The exact hash and binary grammar remain a later normative choice. The
architecture requirement is that each subject family's exact regime and its
dependency edges are in the identity preimage. Identical payload bytes
interpreted under two semantic regimes do not identify one semantic subject.

`ProtocolInterfaceId` depends on `ProtocolId` but does not enter
`ProtocolId`. It owns deployable choices such as ABI names, dispatch labels,
and external bindings that must not be read from ignored carrier metadata.
`ProverPlanId` is a sibling dependency on `ProtocolId`, not a child of an
Interface. It owns witness routes, local construction choices, and private
actions only while they do not alter verifier-visible Protocol behavior.

### 2.3 Common semantic laws

Every candidate must enforce at least these laws:

1. Every Protocol-visible transcript, wire, public-binding, check, claim,
   artifact-verification, and terminal action is an explicit typed event.
2. Transcript and proof-stream states evolve linearly; challenge occurrences
   cannot be merged by ordinary common-subexpression reasoning.
3. Typed framing, domain context, codecs, sampling maps, and composition
   occurrence namespaces are explicit where they affect a construction.
4. The selected total schedule extends all declared causal constraints.
5. Every admitted event has an abstract endpoint-obligation status; reserved
   or unsupported authoring syntax cannot masquerade as an endpoint-complete
   admitted Protocol.
6. Unknown meaning-bearing content fails closed. Only material structurally
   classified as non-semantic may be ignored.
7. Property judgments, assumptions, derivations, and cost claims are identified
   results over a Protocol; booleans stored in the carrier do not mint them.
8. A transformation names its relation, protected observers, source, target,
   checker, and any assumption or property delta. Generic validity is not a
   preservation claim.
9. OIR projection consumes an admitted Protocol plus a separately identified
   Protocol Interface and role. Source coverage is checked against the
   Protocol obligations, not inferred from a source-free endpoint artifact.
10. Composition constructs a new Core with tagged child occurrences, explicit
    causal seams, challenge sharing, and an identified total interleaving. It
    is not graph union or unchecked concatenation.

These requirements follow from the coupled effect-and-claim structure studied
in the [theory dossier](cases/protocol-semantics-theory.md) and the native
counterexamples in the
[current correspondence](cases/current-zkc-correspondence.md).

## 3. Shared lifecycle and judgment boundaries

The candidates may realize the steps in different carriers, but they share
this authority flow:

```text
authoring/import/synthesis material
        -> mutable workbench proposal
        -> exhaustive closure and semantic normalization
        -> closed candidate subject
        -> independent admission under one SemanticRegime
        -> immutable AdmittedProtocol capability
             -> analyses and qualified judgments
             -> checked Protocol transformations
             -> Interface-bound OIR projection
             -> ProverPlan conformance checking
```

Closure constructs a candidate. Admission independently checks the candidate;
it does not trust a stored ID, a lifecycle marker, or the producer that ran
normalization. Admission proves only the named structural and semantic
admissibility judgment. It does not prove soundness, completeness, zero
knowledge, implementation correctness, or transform preservation.

A normalizer may safely be untrusted with respect to the validity of its
output, because admission checks that output. It remains trusted if the system
claims that the output preserves the meaning of its authoring input without a
separate translation-validation or proof obligation. This distinction applies
equally to A, B*, and D.

## 4. Candidate A — strengthened lifecycle quotient

### 4.1 Concrete architecture

```text
one MLIR PIR dialect
  open Protocol representative
      -> close and seal
  sealed Protocol representative
      -> canonical semantic projection
      -> identity and admission
      -> opaque admitted capability and bounded views
```

Open and sealed Protocols use one MLIR operation vocabulary and substantially
the same body schema. Lifecycle state, ownership, and capability types prevent
mutable proposals from acquiring admitted authority. A sealed body is not
required to be the unique physical representative of its subject. Authored
names, incidental block presentation, and other declared quotient-neutral
details may differ while the canonical semantic projection and `ProtocolId`
agree.

The common semantic factorization is represented inside this dialect:

- the root cites `SemanticRegimeId`;
- Core events carry causal constraints and the selected total schedule;
- the challenge mode is fresh coins or a referenced/embedded canonical
  Transcript Construction;
- Protocol Interface and Prover Plan are separate identified roots that refer
  to `ProtocolId`; and
- non-semantic diagnostics are explicitly outside all normative projections.

### 4.2 Carrier and canonicality

The complete carrier is a closed `pir` MLIR root plus its cited semantic
dependencies. MLIR text and bytecode remain transports. The semantic encoder
decodes permitted representatives into the common subject and produces the
canonical identity preimage.

Candidate A therefore has a canonical semantic quotient, not a unique
canonical carrier body:

```text
x ~A y  iff
  canonical_subject(R, x) = canonical_subject(R, y)
```

The quotient may erase only fields enumerated by the normative projection.
It may not discover equivalence using best-effort MLIR canonicalization.

### 4.3 Checker and admission model

The admission checker:

1. parses the permitted MLIR profile;
2. verifies local dialect structure;
3. verifies whole-Protocol closure and the common semantic laws;
4. resolves exact semantic dependencies under the cited regime;
5. recomputes the canonical subject and all dependent IDs; and
6. returns an opaque immutable capability rather than raw mutable MLIR.

Every normative consumer must either consume that canonical subject projection
or obey the following quotient-congruence law:

```text
canonical_subject(R, x) = canonical_subject(R, y)
  =>
consumer(x, identified_inputs) = consumer(y, identified_inputs)
```

This must hold for projection, analysis, relation correspondence, transform
checking, persistence comparisons, and every future normative consumer.
Protocol Interface and Prover Plan inputs close the behavior that the Protocol
quotient intentionally excludes.

### 4.4 Trust and implementation boundary

The trusted semantic base contains the normative semantics, regime resolver,
whole-object admission rules, and canonical semantic encoder. A checker using
the MLIR carrier additionally trusts or validates the relevant MLIR parser,
IR invariants, and dialect accessors. The general optimizer need not be in the
admission TCB.

The global quotient law creates a distributed obligation: each consumer's
implementation must be audited against every field erased by identity. Opaque
capabilities and purpose-specific views reduce accidental access but do not
remove the semantic requirement.

### 4.5 Version and compatibility model

- Semantic meaning and canonical projection are selected by
  `SemanticRegimeId`.
- A changed meaning creates a new regime; capabilities cannot reinterpret an
  existing operation spelling.
- MLIR bytecode revision and tool release are separate from Protocol identity.
- v0 promises only exact fail-closed decoding and admission, not a backward or
  forward compatibility window.
- A future migration either reconstructs the same subject under its original
  regime or creates a new subject plus an explicit migration relation.

### 4.6 Extension model

Canonical semantic operations form a closed admitted set. Authoring
conveniences in the same source ecosystem require a total lowering contract,
a last legal phase, and refusal tests. External semantic dependencies enter
through typed, content-identified declarations. Unknown semantic operations
fail admission; registered non-semantic material is excluded from every
normative consumer as well as identity.

### 4.7 Strongest case and fatal risk

Candidate A has the smallest representation count and maximizes direct reuse
of the current MLIR workbench. It is viable when:

- the canonical vocabulary remains small;
- the quotient is finite and easy to specify;
- every consumer is forced behind admitted capabilities and canonical views;
- an admission checker can be built without importing optimizer behavior; and
- no durable external compatibility artifact is promised.

Its fatal risk is **quotient leakage**. A field omitted from `ProtocolId` may
still affect a normative result through raw carrier access. The current
label-to-OIR seam is already a concrete example of the class, as documented in
the [current correspondence](cases/current-zkc-correspondence.md). Every new
field and consumer extends the global congruence burden. If A adds a compulsory
physical normal-form firewall so consumers cannot observe alternative
representatives, it has substantively converged toward Candidate B*.

## 5. Candidate B* — closed canonical MLIR Protocol level

### 5.1 Concrete architecture

```text
mixed MLIR authoring/import/synthesis workbench
        -> exhaustive closure and zkc-defined normalization
small closed canonical MLIR PIR level
        -> independent admission
        -> opaque AdmittedProtocol capability
        -> consumer-specific views and Interface-bound OIR
```

B* introduces one boundary because denotation, admissibility, legal
transformations, retained information, and consumer access all change there.
It does not introduce one dialect per lifecycle state or subsystem. The
upstream workbench may reuse canonical operations and mix explicitly permitted
authoring/import dialects. All authoring-only operations, unresolved choices,
and partial-order templates must lower away before the canonical level.

The canonical level represents exactly the common semantic subject. It is a
small, closed MLIR PIR level or strict dialect profile with:

- canonical positional references rather than author presentation names;
- all semantic defaults materialized;
- one selected total observable schedule plus its causal constraints;
- explicit challenge interpretation and Transcript Construction references;
- closed semantic dependencies and endpoint-obligation status;
- no unresolved holes, macros, target hooks, or unknown operations; and
- diagnostics and source locations outside the semantic payload.

The form is physically canonical at the zkc semantic-structure level. This
does not require MLIR textual spelling or bytecode bytes to be unique. SSA
print names, bytecode revisions, container compression, and diagnostic
attachments remain transport concerns.

### 5.2 Carrier and canonicality

The v0 complete carrier is the closed canonical MLIR PIR level. Its normative
denotation is language-independent: operation meanings, whole-object laws,
normal-form grammar, identity projection, and admission rules are specified by
zkc rather than inherited from C++, MLIR's generic verifier, or its generic
canonicalizer.

`ProtocolId` is derived from the canonical semantic subject, not MLIR text or
bytecode. A carrier decoder may change while preserving an ID only when it
reconstructs the same canonical subject under the same regime.

### 5.3 Checker and admission model

Closure and admission are deliberately separate:

1. a workbench normalizer chooses every unresolved semantic decision and emits
   a canonical candidate;
2. full conversion or an equivalent exhaustive check rejects remaining
   authoring/import content;
3. an admission checker independently verifies the canonical normal form,
   dependency closure, schedule, effect and claim laws, endpoint-obligation
   completeness, regime, and IDs; and
4. admitted consumers receive an opaque immutable capability or a typed view.

MLIR dialect conversion can help establish syntactic target legality, but that
is only one input to admission. MLIR's best-effort generic canonicalizer is not
the normal-form authority. These distinctions are supported by the
[multi-level MLIR study](cases/multilevel-mlir.md).

The target candidate can be admitted without trusting its producer. A claim
that authoring input and canonical target denote the same Protocol requires a
separate checked transform relation. Optimization may therefore remain an
untrusted search procedure while a smaller validator accepts or rejects each
claimed successor.

### 5.4 Trust and implementation boundary

The semantic TCB is the normative semantics, exact normal-form and admission
rules, dependency resolver, and checker. A v0 implementation may link the
MLIR core, bytecode parser, and the closed dialect definitions. It need not
link optimization passes, authoring dialects, synthesis engines, or backend
realizations into the checker.

Because the admitted payload has one observable semantic structure, consumers
cannot accidentally distinguish two quotient-equivalent raw bodies. The
semantic specification remains implementation-language independent, so a
future checker or formal model can implement the rules without becoming a
second authority. It may still need an MLIR decoder while MLIR is the complete
v0 carrier.

### 5.5 Version and compatibility model

- `SemanticRegimeId` fixes meaning, normal form, identity grammar, and
  admission rules.
- Existing canonical spellings are modeless: a capability or target profile
  may reject them but cannot reinterpret them.
- MLIR dialect schema, MLIR bytecode, canonical identity grammar, semantic
  regime, dependency schemas, and tool release are named as separate axes even
  if v0 deliberately releases them together.
- v0 is fail closed and makes no compatibility-window promise.
- No VHLO-style compatibility dialect is created until a named consumer,
  artifact lifetime, release-cadence split, and owned migration policy justify
  its permanent conversion surface.

StableHLO/VHLO demonstrates that a compatibility dialect can quarantine
history, but also that it becomes an indefinite product obligation. The
[portable-IR study](cases/portable-ir-contracts.md) therefore supports a
version hook now, not an unowned compatibility promise.

### 5.6 Extension model

The canonical level is closed. New canonical semantics require a new
regime-recognized operation or typed dependency with an exact specification,
identity grammar, admission rule, and consumer coverage. Authoring extensions
live upstream and must lower completely. Target hooks live downstream.
Non-semantic annotations use a separately classified channel and cannot affect
any normative consumer. Unknown meaning-bearing content fails admission.

This preserves MLIR extensibility where it is useful without making admitted
Protocol meaning open world.

### 5.7 Strongest case and fatal risk

B* provides a narrow independent-checking surface while retaining MLIR for the
work it is good at: typed structure, SSA, mixed authoring forms, diagnostics,
passes, and multi-level lowering. It prevents representative-specific data
from leaking past the admission boundary and leaves language-independent
semantics available for formalization and future carriers.

Its fatal risks are:

- normalization erases information needed to reproduce a rejection judgment;
- a duplicated canonical operation family develops different semantics from
  its workbench counterpart;
- the physical normal form freezes incidental compiler choices; or
- the authoring-to-canonical bridge is treated as preservation evidence merely
  because the target admits.

The mitigations are architectural, not testing slogans: retain every
rejection-relevant distinction, reuse operation definitions where denotation
is truly identical, keep the canonical grammar semantic rather than
optimizer-shaped, and validate any claimed source-to-target relation
separately. The CIRCT and IREE histories in the
[multi-level study](cases/multilevel-mlir.md) make these failure modes concrete.

## 6. Candidate D — complete carrier-neutral Protocol package

### 6.1 Concrete architecture

```text
normative language-independent Protocol schema
        -> one tagged, dependency-closed canonical package
        -> neutral parser and admission checker
        -> opaque AdmittedProtocol capability

MLIR authoring/transformation IR
        <-> checked adapter
        <-> neutral canonical package
```

D materializes the common semantics as a full zkc-owned data model and
canonical binary package that can be parsed without MLIR. The package, rather
than an MLIR operation tree, is the complete persisted and independently
consumed representation.

The package contains a regime-qualified Core, challenge interpretation, and
all cited semantic dependencies needed for closure. Protocol Interfaces and
Prover Plans are separately addressed companion packages that depend on the
`ProtocolId`. The package must preserve the total observable schedule, causal
constraints, typed claim graph, Transcript Construction, checks, terminal
behavior, and endpoint obligations at the same resolution as A and B*.

MLIR remains the authoring and optimizer workbench. Import and export are
semantic adapters, not pretty-printers or identity authorities.

### 6.2 Carrier and canonicality

The complete carrier is a zkc-defined tagged and length-delimited schema with
one deterministic canonical encoding. The logical schema and the byte grammar
are separate specifications: parsers may use different in-memory types, but
canonical bytes decode to exactly one common semantic subject.

This instantiation does not select protobuf, CBOR, FlatBuffers, or a custom
container. Selecting one prematurely would confuse a library choice with the
architectural requirement. Any selected format must support:

- deterministic encoding and unambiguous framing;
- closed, typed semantic variants;
- exact dependency identities;
- explicit schema and canonical-encoding versions;
- resource limits and fail-closed decoding; and
- independent implementations with a shared conformance corpus.

`ProtocolId` remains a semantic identity rather than a hash of arbitrary
package transport bytes.

### 6.3 Checker and admission model

A neutral checker, with no MLIR dependency, performs decoding, canonical-form
validation, dependency closure, whole-Protocol admission, and identity
recomputation. At least one independent implementation or differential oracle
is required before neutrality is treated as operational rather than nominal.

The MLIR-to-package adapter must establish that the emitted package denotes
the intended MLIR subject. Package admission alone shows only that the result
is a valid Protocol. The reverse adapter must likewise reconstruct a workbench
representative without changing the package subject. Cross-adapter
conformance, round trips over semantic corpora, and translation validation are
permanent architecture surfaces.

### 6.4 Trust and implementation boundary

An independent package consumer trusts the normative semantics, the neutral
schema and canonical encoding, its parser, dependency resolver, and admission
checker. It need not trust or link MLIR.

The producing compiler additionally depends on the correspondence between its
MLIR model and the neutral package. Unless that relation is checked or proved,
the adapter is in the end-to-end trust base. D therefore removes MLIR from
consumer TCBs but adds a second complete implementation boundary and makes
correspondence central.

### 6.5 Version and compatibility model

- Semantic regime, package schema, canonical encoding, dependency schema,
  transport envelope, and tool release are separate version axes.
- Existing semantic tags are modeless; unknown semantic variants fail closed.
- v0 may initially promise exact-version decoding only, but publication of a
  neutral package creates strong pressure for independent producer/consumer
  release cadences and long artifact lifetimes.
- Any compatibility window requires historical interpretation, checked
  migrations, downgrade refusal, and a conformance matrix for every supported
  edge.
- Migration preserves an ID only when both packages decode to the same subject
  under the same regime; otherwise it produces a new ID and named relation.

The [long-lived-IR study](cases/long-lived-ir-contracts.md) shows why byte
readability, current interpretation, and semantic identity must remain
separate even when historical artifacts are accepted.

### 6.6 Extension model

The core package schema is closed and registry-governed by zkc. A new semantic
variant requires a specification, canonical tag, dependency and identity
rules, checker behavior, and version policy. Unknown semantic tags fail.
Opaque vendor payloads cannot enter Protocol meaning. Decomposable authoring
extensions remain in MLIR and disappear before package emission. Explicit
external semantic dependencies are content identified; non-semantic sidecars
are outside the package identity and all normative consumers.

### 6.7 Strongest case, trigger, and fatal risk

D is strongest when a real consumer must inspect complete Protocol semantics
without MLIR, especially when it has an independent implementation language,
trust boundary, deployment environment, or release cadence. It also gives a
formal model or small checker a direct carrier, provided that the model is not
allowed to drift from the normative schema.

Its fatal risk is a **premature shadow IR**. The neutral schema duplicates the
complete semantic vocabulary before the subject has stabilized, weakens MLIR
transformation ergonomics, and makes two-way correspondence a permanent
obligation. A differential Python model or aspirational Rust consumer is not
by itself an independently deployed consumer contract.

D should therefore be deferred until at least one named consumer requires the
complete Protocol but cannot accept the closed MLIR carrier, and the project
can own:

1. the consumer's exact trust or deployment reason;
2. an independent compatibility and release policy;
3. two independently exercised decoders or checkers;
4. a cross-carrier semantic conformance corpus; and
5. stable answers for the common subject and extension model.

Deferral does not require changing the common semantics later. B* can preserve
the language-independent specification, regime-qualified identities, closed
normal form, and opaque consumer boundaries needed to emit D when its trigger
becomes real.

## 7. Candidate E — authenticated consumer views as a complement

### 7.1 Why E is not a complete candidate

```text
complete admitted Protocol subject
        -> source-bound typed view or projection certificate
        -> narrow independent consumer
```

E does not carry enough information to author, transform, compose, re-admit,
or project an arbitrary Protocol. It therefore cannot replace A, B*, or D.
It is a way to keep consumers from importing a complete compiler IR when their
questions are narrower.

### 7.2 Exact view model

Each view has its own small schema and identity:

```text
ConsumerView
  = source ProtocolId
  + SemanticRegimeId
  + view kind and view-schema version
  + exact consumer inputs, including ProtocolInterfaceId where required
  + typed facts or obligations
  + producer/checker identity or derivation certificate
```

Examples include an endpoint-projection coverage certificate, a relation
interface view, a compiler cost-input view, or a soundness-kernel premise
view. Views are purpose-specific and monotone only under their own declared
rules. There is no universal `ProtocolFacts` record that grows whenever a new
consumer appears.

A digest authenticates bytes and source binding; it does not establish that
the facts were derived correctly. A consumer must recompute the view, trust an
identified producer, or check a derivation certificate. In particular, a
source-free OIR cannot prove exhaustive source-Protocol coverage merely by
carrying the source ID.

### 7.3 Carrier, trust, version, and extension model

- A view uses a small closed schema chosen for its exact consumer; it need not
  share the complete Protocol carrier.
- Its checker imports only the semantic rules and source facts needed for that
  view, or checks a purpose-specific certificate.
- The source Protocol remains the sole authority for complete meaning.
- View-schema version is independent of Protocol regime and carrier version.
- Unknown fact kinds fail closed for consumers that rely on them.
- Adding a view cannot add semantics to the source Protocol or upgrade a
  property judgment.

### 7.4 Value and fatal risk

E can reduce consumer TCBs, make dependency reads explicit, and avoid forcing a
formal checker, endpoint verifier, or cache key implementation to understand
the entire optimizing workbench. It combines naturally with B*: B* owns one
complete admitted subject and E exposes only bounded views from it.

Its fatal risks are:

- a shared fact root accretes into an undocumented second Protocol schema;
- consumers treat source binding as proof of correct derivation;
- a lossy view is reused for a stronger question than it was designed to
  answer; or
- duplicated facts acquire independent mutation or authority.

The mitigation is to create a view only for a named consumer and judgment,
version it independently, state its non-claims, and keep the complete Protocol
as the sole semantic authority.

## 8. Equal-resolution comparison

| Question | Candidate A | Candidate B* | Candidate D | Candidate E |
|---|---|---|---|---|
| Complete Protocol carrier | Lifecycle-aware MLIR PIR representative | Closed canonical MLIR PIR level | Neutral full package | No; bounded view only |
| Normative semantics | Language independent | Language independent | Language independent | Inherited subset for one consumer |
| Canonicality | Semantic quotient over multiple carrier bodies | One canonical semantic structure; transport spelling may vary | One canonical neutral schema and encoding | Per-view closed schema |
| Independent checker input | MLIR representative plus quotient projection | Closed canonical MLIR level | Neutral package without MLIR | Narrow view or certificate |
| Main permanent obligation | Every consumer respects quotient congruence | Normalization and admitted-level discipline | Full dual-model correspondence and compatibility | View derivation and scope discipline |
| MLIR role | Workbench, complete carrier, and persisted transport | Workbench plus canonical v0 structural carrier | Workbench adapter only | Source-dependent or absent per view |
| Unknown semantic content | Reject at admission | Must lower away; reject in canonical level | Reject in neutral parser/checker | Reject when relevant to the view |
| v0 compatibility | Exact fail-closed only | Exact fail-closed only | Exact initially, but public-package pressure begins immediately | Per-view exact contract |
| Principal failure | Quotient leakage | Bad or premature canonical boundary | Premature shadow IR | Second schema by accretion |
| Unique justification | Minimum representation count | Strong carrier firewall with MLIR leverage | Named independent complete consumer | Named narrow consumer |

## 9. Instantiation-level conclusion

At equal semantic resolution, B* is the strongest v0 candidate. It keeps
MLIR's demonstrated structural and transformation value while making the
admitted Protocol a small closed level whose denotation, identity, and
admission remain zkc-owned and language independent. It localizes the carrier
firewall instead of imposing A's perpetual quotient-congruence audit on every
consumer.

D is coherent and can carry exactly the same subject, but it solves a consumer
and compatibility problem that has not yet been named. Introducing it now
would freeze a second complete schema while the Protocol model is still being
settled. B* should retain explicit reversal hooks—language-independent
semantics, regime-qualified IDs, a closed normal form, and purpose-specific
views—so D can be introduced without redefining Protocol when a concrete
trigger appears.

E should accompany B* selectively, beginning only with consumers that have a
specific smaller trust or deployment boundary. A universal fact root is not a
v0 requirement.

Candidate A remains a plausible minimum architecture only if zkc can prove and
enforce quotient congruence for every normative consumer. Once it adds the
physical admitted-surface firewall needed to make that obligation local, its
substantive architecture is B*.

This conclusion is an input to Stage 1 scenario evaluation and convergence. It
does not by itself ratify B* or begin downstream schema design.
