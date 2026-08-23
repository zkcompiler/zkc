# Stage 1 convergence record

> **Document kind:** Temporary research synthesis
> **Document state:** Complete for Stage 1 convergence
> **Authority:** None. The durable selected target is the
> [Protocol IR Architecture](../../project/protocol-ir-architecture.md).
> This page preserves the comparison, rejected alternatives, and reversal
> conditions until the temporary research package is absorbed.

## 1. Question closed

The reopened Stage 1 asked which semantic and representation architecture is
best for an ideal zkc v0 before current implementation or migration cost is
allowed to constrain it.

The selected answer is:

```text
language-independent normative Protocol semantics
  + explicit compositional semantic subjects and identities
  + rich MLIR authoring/import/synthesis workbench
  + distinct small closed canonical PIR level in MLIR
  + opaque immutable admission capability
  + purpose-specific derived consumer views
  + no complete portable shadow representation until a real trigger exists
```

This is strengthened Candidate B with the useful part of Candidate E. It is
not a compromise with the current implementation. It is the candidate that
best satisfies the complete semantic, transformation, consumer, and evolution
forces without installing a permanent duplicate authority.

## 2. Evidence used

The convergence draws on four evidence classes:

1. zkc-native subject, identity, lifecycle, effect, endpoint, composition, and
   implementation correspondence pressures;
2. portable, multi-level, long-lived, and ZK-adjacent IR case studies;
3. protocol, interaction, Fiat--Shamir, projection, effect, and translation-
   validation theory; and
4. equal-resolution candidate instantiations attacked with the same twelve
   protocol-specific scenarios.

The main source routes are:

- [Zkc-native Design Forces](zkc-design-forces.md);
- [Current zkc Correspondence](cases/current-zkc-correspondence.md);
- [Portable IR Contracts](cases/portable-ir-contracts.md);
- [Multi-level MLIR Systems](cases/multilevel-mlir.md);
- [Long-lived IR Contracts](cases/long-lived-ir-contracts.md);
- [ZK and Proof-adjacent IRs](cases/zk-proof-adjacent-irs.md);
- [Protocol Semantics and Transformation Theory](cases/protocol-semantics-theory.md);
- [Cross-case Synthesis](cross-case-synthesis.md);
- [Candidate Instantiations](candidate-instantiations.md); and
- [Scenario Results](scenario-results.md).

External designs were evidence of mechanisms, costs, and installed-base
pressure. They did not vote on the zkc result. In particular, no MLIR system
supplies zkc's content identity, Protocol admission, ordered cryptographic
semantics, or endpoint-coverage claim.

## 3. Convergence method

Candidates were not scored by an arbitrary weighted sum. A candidate first
had to satisfy hard coherence gates:

| Gate | Requirement |
|---|---|
| Functional closure | Every normative result is determined by identified semantic subjects and explicit identified inputs |
| Ordered-protocol fidelity | Transcript, wire, binding, checks, claims, and terminal observations cannot be hidden behind SSA equivalence |
| Identity qualification | Meaning, carrier, schema, policy, and release versions cannot be silently collapsed |
| Authority separation | Bytes, decoded structure, authenticated identity, admitted capability, judgment, and evidence remain distinct |
| Endpoint honesty | Canonical admission owns complete abstract obligations; unsupported target projection refuses |
| Extension closure | Unknown canonical semantics fail; authoring-only content has a last legal phase |
| Transformation honesty | Equality, refinement, Fiat--Shamir compilation, property transport, intentional change, and cost remain distinct relations |
| Composition explicitness | Occurrences, interleaving, challenge sharing, domains, faces, and failure propagation are constructed explicitly |
| Independent inspectability | Full admission excludes authoring, optimizer, search, and backend machinery |
| Single authority | No second complete representation exists without its own consumer, laws, and synchronization mechanism |

A correct refusal counts as success when the requested conclusion is
information-theoretically unavailable. The source-free OIR coverage scenario
is the central example.

Candidates that passed the gates were then compared by transformation leverage,
semantic surface, trust and bridge burden, extension cost, enabled new
capabilities, compatibility commitment, formalization surface, and reversal
cost.

## 4. Semantic axes resolved

### 4.1 Subject factorization

Selected:

```text
InteractiveCore I
  = roles
  + canonical semantic ports
  + typed protocol events
  + causal constraints
  + one total observable schedule
  + claim/reduction/check/terminal graph
  + fresh public-coin challenge occurrences
  + abstract prover obligations

ChallengeInterpretation C
  = FreshPublicCoins
  | FiatShamir(TranscriptConstruction scoped to I)

Protocol P = I + C

ProtocolInterface J depends on P
ProverPlan L depends on P
```

The total schedule is part of the admitted `InteractiveCore`. A partial order
may exist in authoring input, but it does not identify one interactive
protocol until a schedule is chosen. Fiat--Shamir interprets this already
ordered interaction.

### 4.2 Identity

Selected:

- every semantic identity is domain-separated and regime-qualified;
- `CoreId` names one ordered interactive protocol;
- `ProtocolId` commits to the Core and Fresh/Fiat--Shamir interpretation;
- `ProtocolInterfaceId` includes `ProtocolId` and the exact external binding;
- `ProverPlanId` includes `ProtocolId` and plan content; and
- carrier bytes and tool releases do not define semantic identity.

The Protocol/Interface disagreement was resolved by distinguishing an abstract
Protocol from its externally callable binding. Protocol-level judgments and
plans may be reused across compatible interfaces. Every deployable or ABI-
sensitive result consumes the dependent `ProtocolInterfaceId`, so no hidden
interface input remains.

### 4.3 Protocol versus Interface

The Protocol owns canonical semantic values, proof/message order and codecs,
transcript actions, challenges, checks, claim flow, and terminal behavior.
The Interface owns only an external binding that preserves those facts.

Changing an ABI name or external layout can change `ProtocolInterfaceId`
without changing `ProtocolId`. Changing an absorbed value, proof codec,
semantic public input, challenge schedule, or check is not an interface-only
change.

### 4.4 Protocol versus ProverPlan

The Protocol owns verifier-visible behavior and abstract prover obligations.
The Plan owns one way to construct the required prover behavior. Plan changes
may alter internal algorithms, suppliers, parallelism, buffering, and cost,
but not the verifier-visible distribution or proof/transcript contract.

Structural plan coverage is not a completeness theorem. A completeness
judgment cites both IDs and its exact assumptions.

### 4.5 Order and effects

Selected:

- one total admitted schedule;
- explicit protected observation classes for transcript, wire, public
  binding, check/failure, artifact verification, claim flow, and terminal
  outcome; and
- observer-indexed transformation relations.

An explicitly unordered aggregate may have order-insensitive internal
semantics. Separate observable events are not made interchangeable merely
because the SSA graph lacks a dependency.

### 4.6 Semantic regime

Selected: `SemanticRegimeId` enters semantic identity and admission. It fixes
meaning and intrinsic rules. A local admission policy can accept a stricter
subset without redefining the subject; that policy qualifies the capability
or judgment rather than the Protocol ID.

### 4.7 Endpoint obligation status

Selected: every canonical admitted event kind has one abstract endpoint-
projection obligation. This does not promise that every target supports every
event. Unsupported target projection refuses. Reserved syntax lacking an
abstract obligation rule remains authoring-only rather than masquerading as a
generally endpoint-ready admitted Protocol.

### 4.8 Composition

Selected at skeleton level: composition creates a new Core with tagged child
occurrences, explicit face maps, causal seams, total interleaving, challenge-
sharing rules, domain separation, failure propagation, and new closure. It is
not graph union. Exact constructors and property-transport laws remain later
work.

## 5. Representation axes resolved

### 5.1 Normative meaning and carrier

Normative meaning is language-independent. MLIR remains the v0 structural
carrier and optimization workbench because its SSA, regions, typed operations,
interfaces, diagnostics, conversion infrastructure, and multi-level lowering
directly serve zkc's compiler needs.

This is not “the semantics live in Rust” and not “MLIR defines the semantics.”
The specification defines the semantics; the canonical PIR MLIR dialect is
the primary v0 representation implementing that contract.

### 5.2 Authoring and canonical levels

Selected: a genuine level boundary.

- The workbench may be mixed-dialect, partial, family-valued, extensible, and
  mutable.
- Canonical PIR is small, closed, normalized, exact, and immutable after
  admission.
- All authoring-only semantics must lower away, be extracted into a separately
  identified subject, or cause refusal.

PIR is reserved for the canonical Protocol level. The number and names of
authoring dialects are selected only when their denotation and transformation
laws justify them.

### 5.3 Physical canonicality

Selected with qualification: one legal canonical semantic operation graph per
Protocol, modulo MLIR object identity and SSA alpha-renaming. MLIR text,
generic printer output, bytecode, and generic canonicalizer output are not the
identity or promised physical singleton.

The zkc normal form is specified independently and is bijective with the legal
canonical graph after carrier trivia is removed.

### 5.4 Checker input

Full v0 admission consumes the restricted canonical MLIR PIR artifact. The
checker does not import the authoring dialects, optimizer, search, or backend
pipeline. Purpose-specific consumers receive derived views or certificates.

A complete carrier-neutral input is not selected. If the identity projection
is later published as a complete independently accepted runtime artifact, the
architecture has crossed into Candidate D and must own that decision rather
than pretending it is merely a hash codec.

### 5.5 Compatibility

Selected: exact fail-closed v0 with separated version axes and no historical
compatibility promise. A stable compatibility dialect or neutral package is
introduced only for a named independent consumer, retention promise,
independent release cycle, MLIR-excluding deployment boundary, or formal
extraction requirement.

## 6. Candidate dispositions

### Candidate A — lifecycle quotient

Coherent only in its strongest form, where every consumer is congruent with a
specified finite quotient and all carrier-only facts are inaccessible or
identified inputs. It retains maximal direct MLIR flexibility but imposes a
permanent global noninterference obligation. Once strengthened with a strict
closed normal-form firewall, it approaches Candidate B. Not selected.

### Candidate B — closed canonical MLIR Protocol level

Passes the scenarios after subject, regime, effect, and identity factorization
are made explicit. It retains MLIR transformation leverage, creates a small
admission surface, and avoids a complete second representation. Selected.

### Candidate C — optimizing PIR plus compatibility dialect

Architecturally useful after a real compatibility contract exists. Premature
now because it installs dual-schema conversion and historical-evolution work
without an external retention or release promise. Deferred with trigger.

### Candidate D — carrier-neutral semantic package

Semantically coherent and the cleanest input for a full checker that cannot
import MLIR. It does not solve the unresolved semantic factorization by
itself, and it requires a complete second schema plus bidirectional
correspondence. Deferred until that independent full-Protocol consumer or
deployment boundary exists.

### Candidate E — fact root and consumer projections

Useful only as a complement. Purpose-specific views and checked certificates
are selected. A universal fact root is rejected because it can accumulate
into a lossy shadow Protocol authority.

## 7. Why B wins rather than merely survives

Candidate B creates a semantic assembly boundary that is useful to several
different consumers while remaining native to the transformation system. It
enables:

- rich and potentially novel authoring models without expanding the admitted
  vocabulary;
- deterministic closed subjects without relying on a global quotient
  discipline in every consumer;
- a smaller checker and clearer extension refusal boundary;
- reuse across challenge interpretations, interfaces, and prover plans;
- explicit effect-aware transformations and composition; and
- later introduction of a neutral package without changing the abstract
  subject model.

The asymmetry with Candidate D matters. A well-designed B can later emit a
neutral package whose subject identity remains the same after a checked
correspondence is established. Publishing D first commits zkc to a second
schema before the Protocol vocabulary is mature and makes withdrawing it an
external break.

## 8. Residual obligations, not Stage 1 indecision

The following remain required work but do not reopen the selected backbone:

- exact canonical PIR grammar and semantic field ledger;
- exact identity encoding and test vectors;
- exact normalization/refusal contract;
- precise Interface and ProverPlan schemas;
- transition signatures and validation bases;
- complete composition constructors;
- consumer-specific view and certificate designs;
- exact compatibility triggers and owner when one fires; and
- current-to-target implementation and migration mapping.

These are routed to later stages. The architecture is reopenable only when a
new contradiction or capability requirement defeats one of its fixed subject,
identity, or representation laws.

## 9. Reversal conditions

Reopen the canonical-level decision if:

- the supposedly small PIR level grows into another optimizing workbench;
- normalization must decide general behavioral equivalence rather than a
  finite declared authoring quotient;
- rejection-relevant source distinctions cannot be validated before erasure;
- a clean admission checker still imports most compiler or plugin machinery;
- authoring and canonical forms prove semantically identical and no consumer
  benefits from the level boundary;
- multiple committed full-Protocol consumers require a non-MLIR contract;
- long-lived external artifacts require a compatibility window; or
- purpose-specific views collectively recreate a complete second Protocol
  schema.

Reopen a subject boundary if an Interface or ProverPlan substitution changes a
consumer that was claimed to depend only on `ProtocolId`.

## 10. Stage boundary

The durable result and Stage 2 input contract are in the
[Protocol IR Architecture](../../project/protocol-ir-architecture.md).
Stage 1 is complete. At this convergence point Stage 2 had not begun; it was
subsequently activated on 2026-08-22 under the fixed entry contract.
