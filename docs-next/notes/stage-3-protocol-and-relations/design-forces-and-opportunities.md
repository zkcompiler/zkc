# Stage 3 design forces and opportunity ledger

> **Document kind:** Temporary generative-research ledger
> **Document state:** Stage 3.2 complete; candidate and convergence input
> **Authority:** None. This page states requirements, pressures, opportunities,
> and falsifiers. It does not select a semantic model or authorize a migration.
> **Scope:** Protocol, canonical PIR, Interface, Plan, Relations,
> Fiat--Shamir, and semantic composition.
> **Disposition:** Absorb reviewed constraints and opportunities into the
> durable PIR, Relations, and convergence documents, then delete this page
> before `docs-next/` authority cutover.

## 1. Method

This ledger was derived before selecting a target from four independent
angles:

1. the fixed Stage 1 subject, carrier, identity, and observation decisions;
2. the fixed Stage 2 closure, authority, outcome, and checked-transition
   decisions;
3. reconstruction of current Protocol/PIR and Relations intent, implementation,
   tests, conflicts, and absences; and
4. primary-source cases from IR ecosystems, proof interfaces, protocol theory,
   Fiat--Shamir work, and compositional models.

A design force is not a current-type preservation requirement. It is a
property the target must either satisfy or explicitly reject. An opportunity
is a useful capability whose architectural cost must be visible. A falsifier
is evidence that would defeat the proposed response.

## 2. Primary semantic forces

### F1. The subject is an ordered interactive protocol

An admitted Protocol denotes one verifier-visible public-coin interaction,
not merely a constraint system, proof-system name, authoring template, or set
of events. The semantic center must therefore contain roles, values, protocol
objects, typed events, challenges, checks, claims, failures, terminals,
dependencies, and one observable total schedule.

The total schedule is semantic even when an authoring language begins with a
partial order. A later Fiat--Shamir interpretation consumes an existing
history; it cannot silently choose one of several histories.

**Target pressure:** distinguish the intrinsic interaction from its selected
challenge interpretation without making either incomplete.

**Falsifier:** two schedules that the model identifies produce distinguishable
wire, transcript, check, failure, terminal, or claim observations.

### F2. Transcript order and logical claim flow are different geometries

The same event can participate in a total transcript schedule and a distinct
claim/reduction graph. Neither graph can be reconstructed soundly from the
other. Protocol composition must close both.

**Target pressure:** give schedule positions, claim occurrences, and their
cross-references separate typed namespaces.

**Falsifier:** a legal claim-flow rewrite changes transcript behavior without
changing identity, or a transcript reorder silently changes which claim a
check consumes.

### F3. Every protected observation must survive until its refusal point

The protected observation families are at least transcript, wire/public
interface, public semantic value, checks, artifacts, claims, failures, and
terminals. Normalization may erase syntax only after every rule whose refusal
depends on a distinction has run.

**Target pressure:** publish an information-loss ledger and forbid consumers
from recovering erased meaning from labels, source locations, pass state, or
ambient registries.

**Falsifier:** two inputs become one canonical candidate before a required
consumer can distinguish a protected observation.

### F4. Protocol meaning is language-independent; canonical PIR is one exact
representation

MLIR supplies extensible structure, verification hooks, transformations, and
tooling, but its operation registry, generic canonicalizer, printer, and
bytecode do not define zkc Protocol meaning. Conversely, a separate general
production IR would duplicate authority and expand v0 compatibility scope.

**Target pressure:** define a small mathematical semantic algebra and one
closed MLIR canonical profile bijective with its Protocol encoding, modulo an
explicitly inert carrier-trivia set.

**Falsifier:** a required semantic fact exists only in MLIR behavior, or the
semantic algebra admits two legal canonical graphs that the declared trivia
relation does not identify.

### F5. Schema closure, validation, canonicality, serialization, and identity
are separate contracts

Mature IRs expose why these must not be collapsed. A closed operation set does
not imply semantic validity. Validation does not imply a unique physical form.
A canonical operation graph does not imply unique printer or bytecode bytes.
Compatibility conversion does not imply semantic identity preservation.

**Target pressure:** give each layer a named predicate and outcome, and define
semantic identity over a typed semantic encoding rather than transport bytes.

**Falsifier:** a candidate needs decoder success, generic MLIR verification,
or transport equality to stand in for a stronger predicate.

### F6. Meaning is regime-qualified

Operation meaning, protected observers, framing, sampling, dependency
interpretation, admission, and identity encoding evolve together only when
their owner says so. A tool release or carrier revision is not a semantic
regime. Equal bytes under different semantic regimes do not preserve identity.

**Target pressure:** use typed regimes per subject family and include the exact
regime in every semantic identity preimage and result input.

**Falsifier:** a normative result changes when a hidden version, profile, or
environment changes while every declared input is held fixed.

### F7. Functional closure precedes authority

Every authentication, admission, construction, correspondence, or checked
relation must be a function of named immutable subjects, regimes, and exact
dependency preimages. A broad resolver may help build a candidate but cannot
remain an ambient source of truth for admitted consumers.

**Target pressure:** distinguish a direct dependency manifest from the exact
reachable admission closure and from opaque external subject references.

**Falsifier:** varying an undeclared resolver, registry, carrier context,
theorem base, compiler, or policy changes a normative result.

### F8. Authentication and admission answer different questions

Physical canonical authentication establishes that a carrier is the unique
legal representative of its claimed semantic content and identity under an
exact regime. Whole-subject admission establishes the domain-owned semantic
predicate over that content and its authenticated dependencies. Either can
fail independently, and neither proves a cryptographic property, relation
satisfaction, or target support.

**Target pressure:** allocate every predicate once, avoid circular dependency
between the gates, and mint process-local authority only after admission.

**Falsifier:** one failure must be reported as the other, or possession of
serialized admitted-looking bytes recreates authority.

### F9. Interface and Plan variability must not contaminate Protocol meaning

One Protocol can have several external lossless packages and several prover
strategies. Interface owns external naming, containers, codecs, entry points,
and lossless bindings. Plan owns private construction choices and supplier
requirements. Neither may alter verifier-visible Protocol behavior.

**Target pressure:** make both separately identified dependent subjects;
separate Interface admission from Protocol acceptance, and Plan admission from
`PlanRealizes` structural coverage.

**Falsifier:** changing only an Interface or Plan changes a canonical value,
event schedule, transcript atom, challenge, check, claim, failure, terminal,
or accepted language.

### F10. Relation meaning is not Protocol structure

A Protocol may cite opaque statement, witness, commitment, or claim roles
without defining the mathematical predicate they are intended to represent.
Relation definition, callable interface, public instance, private witness,
artifact interpretation, Protocol-at-Interface correspondence, satisfaction,
and property judgment are different subjects or relations.

**Target pressure:** let Relations consume narrow authenticated Protocol and
Interface views post-admission; it must not participate in Protocol identity or
admission through hidden loads.

**Falsifier:** admitting or changing a relation subject changes Protocol
identity, or structural correspondence is used as witness satisfaction.

### F11. Fiat--Shamir has three non-collapsible layers

The target must distinguish:

1. deterministic construction and independent admission of an FS Protocol;
2. a theorem/model-backed `FSCompile` relation over exact source, target,
   construction, occurrence maps, prefix maps, and assumptions; and
3. property-specific transport with its own source judgment, hypotheses,
   losses, and conclusion.

Multi-round transforms make transcript prefixes, round occurrences, framing,
sampling, abort behavior, and composition context semantic inputs. A global
`FS-valid` bit cannot carry these distinctions.

**Falsifier:** removing a theorem basis invalidates the constructed Protocol,
or one structural result silently transports two properties with different
assumptions.

### F12. Semantic composition constructs one new Core

Composition is not graph union, symbol link, nesting, certificate adjacency,
or transition sequencing. It consumes tagged child occurrences and an exact
composition specification, resolves ports and faces, chooses a total schedule,
defines challenge relationships, closes dependencies and obligations, and
propagates failure and terminal behavior. The resulting Core is authenticated
and admitted independently.

**Target pressure:** keep intrinsic composite identity separate from the
identity of a checked composition derivation. Two histories may yield one Core
when history is not observed; repeated child occurrences must still have
distinct references.

**Falsifier:** a composite result is ambiguous without an ambient scheduler or
challenge policy, or inherited child admission is treated as target admission.

## 3. Relation and result forces

### F13. Every relation needs a typed signature and bounded authority

Names such as equivalence, refinement, construction, realization, and
preservation are not interchangeable annotations. Each relation must declare:

- source and target subjects and direction;
- semantic regimes and exact dependencies;
- protected observer set and assumptions;
- affirmative, negative, unsupported, cannot-answer, refusal, malformed, and
  checker-failure behavior where applicable;
- composition law or explicit absence of one;
- checking owner and trust boundary; and
- non-claims and downstream consumers.

**Falsifier:** a consumer can strengthen a result solely from a shared digest,
matching endpoints, provenance adjacency, or a generic `valid` label.

### F14. Negative truth, inability, refusal, and operational failure differ

A checker that successfully establishes non-correspondence has produced
semantic information. A checker lacking authority, inputs, support, or a
theorem has not established the negation. Malformed input and operational
checker failure are different again.

**Target pressure:** use qualified outcomes at each owned boundary without
creating one project-wide error enum.

**Falsifier:** a failed lookup or crashed checker can be consumed as a negative
judgment, or a negative result destroys otherwise admitted subjects.

### F15. Identity, authority, provenance, and evidence are orthogonal

A content identity authenticates meaning under one regime. A process-local
capability records a checked predicate in one authority lifetime. A durable
result may identify a separately meaningful relation judgment. Provenance or a
signature attributes material; it does not prove the cited predicate. Evidence
and reliance remain downstream.

**Target pressure:** make every serialization boundary discard live
capability, and require re-authentication, re-admission, or result rechecking.

**Falsifier:** copying an object, marker, digest, or signature recreates a
local authority without its checker inputs.

## 4. Extension and evolution forces

### F16. Unknown canonical meaning fails closed

Canonical PIR is a v0 closed world. Unknown operations, attributes,
dependency kinds, semantic regimes, framing profiles, or result kinds cannot
be preserved as opaque meaning-bearing extensions. An inert annotation channel
is permitted only when all normative readers are required to ignore it and it
cannot affect any protected observer.

**Falsifier:** an older consumer can safely produce an authoritative answer
while ignoring a new field that changes Protocol meaning.

### F17. Compatibility must be justified by a named consumer

StableHLO/VHLO, SPIR-V, and WebAssembly made rational but costly compatibility
choices under installed-base constraints. zkc v0 should not prepay for an
upgrade dialect, cross-version identity, extension registry, or universal
bundle without a named compatibility window and consumer.

**Target pressure:** exact-v0 semantics first; cross-regime conversion later
constructs a new candidate and requires an explicit named relation.

**Falsifier:** an already-authorized v0 consumer cannot operate without a
specific backward-reading commitment that exact-v0 rejects.

## 5. Capability opportunities

The target is evaluated for new useful behavior as well as failure resistance.

### O1. Independent semantic models without a second production IR

A small language-independent algebra plus a bijective canonical PIR profile
allows a theorem-prover model, reference checker, or another language to
interpret the same semantics. MLIR remains the production carrier and
workbench rather than becoming the sole source of meaning.

### O2. Many Interfaces and Plans over one stable Protocol

Dependent satellite identities permit application-specific packaging and
prover-strategy experimentation without invalidating Protocol-only analysis,
relation-independent reasoning, or verifier semantics.

### O3. Late relation material and explicit conflict

An admitted relation interface can exist before artifact bytes. Later
interpretation can record agreement or a successful negative conflict without
mutating or invalidating the Protocol. This supports generated, remote, or
proof-assistant relation sources without pretending their bytes define truth.

### O4. Auditable multi-round Fiat--Shamir

First-class event, challenge, occurrence, and prefix maps permit exact
multi-round transform statements, multiple security analyses, alternate
transcript constructions, and source/target replay diagnostics without a
global transformation flag.

### O5. Reusable semantic composition patterns

Tagged occurrences and explicit faces can support reusable multi-relation and
recursive protocol patterns. A later authoring module system may generate the
composition specification, while admitted Core meaning remains closed and
independent of the generator.

### O6. Narrow independent consumers

Analysis, Compiler, Relations, and OIR can consume exact owner-defined views
instead of a universal fact registry. Each view can state an adequacy boundary,
making hidden-input and duplicated-authority audits tractable.

### O7. Honest disagreement as data

Qualified negative relation and artifact results can be retained and compared
without laundering them into malformed inputs or invalid Protocols. This
supports differential checking and evidence collection later without moving
semantic truth into Evidence.

### O8. Same semantics from different construction histories

Separating intrinsic target identity from checked construction provenance
lets independent normalizers, FS constructors, or composition elaborators
converge on one subject while retaining exact derivation maps for consumers
that need them.

## 6. Opportunity costs and guardrails

| Opportunity | Cost | Guardrail |
|---|---|---|
| Independent semantic models | Specification and conformance burden | One production canonical carrier; models do not mint authority by agreement |
| Multiple Interfaces and Plans | More explicit IDs and API inputs | Dependent identity and exact consumer read sets |
| Late relation artifacts | More result states | Artifact interpretation never proves relation meaning or satisfaction |
| Exact FS maps | Larger construction results | Maps are derived and checked; target identity depends only on target meaning |
| Semantic composition | Explicit schedule and seam complexity | Authoring helpers may infer proposals, but admission accepts only a closed Core |
| Generative modules | New authoring-language complexity | Modules elaborate away; they are not needed to interpret admitted Protocols |
| Durable relation results | Storage and replay policy | Persist only for a named independent consumer; bind every input and regime |

## 7. Candidate selection criteria

Candidate evaluation is ordered by these criteria:

1. semantic completeness and clean-room interpretability;
2. functional closure and single ownership of every predicate;
3. physical canonicality without premature information loss;
4. exact identity and occurrence semantics;
5. Interface, Plan, and Relations independence without authority cycles;
6. explicit FS and composition maps;
7. fail-closed extension and regime behavior;
8. independently checkable outcomes and residual trust;
9. capability unlocked relative to the current model; and
10. complexity proportional to a named v0 consumer.

Current implementation proximity is intentionally not a selection criterion.
It appears only in the later current-to-target gap record.

## 8. Primary research basis

The external source facts and transfer limits are recorded in the
[comparative case dossiers](cases/README.md). The most direct primary sources
include:

- [MLIR Language Reference](https://mlir.llvm.org/docs/LangRef/),
  [Dialect Conversion](https://mlir.llvm.org/docs/DialectConversion/), and
  [Operation Canonicalization](https://mlir.llvm.org/docs/Canonicalization/);
- the [StableHLO specification](https://openxla.org/stablehlo/spec) and
  [VHLO dialect](https://openxla.org/stablehlo/vhlo);
- the [SPIR-V unified specification](https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html);
- the [WebAssembly Core specification](https://webassembly.github.io/spec/core/)
  and [Component Model](https://github.com/WebAssembly/component-model/blob/main/design/mvp/Explainer.md);
- the [zkInterface proposal](https://docs.zkproof.org/pages/standards/accepted-workshop3/proposal-zkinterface.pdf);
- the [interactive oracle proof model](https://eprint.iacr.org/2016/116.pdf)
  and [IOP composition](https://eprint.iacr.org/2016/324.pdf);
- the [multi-round Fiat--Shamir transform](https://eprint.iacr.org/2021/1377.pdf)
  and [duplex-sponge Fiat--Shamir transform](https://eprint.iacr.org/2025/536.pdf);
- the [Merlin transcript protocol](https://merlin.cool/use/protocol.html); and
- the [Universal Composability framework](https://eprint.iacr.org/2000/067.pdf).

These sources constrain questions and expose installed tradeoffs. They do not
prove that the selected zkc model is secure, complete, implemented, or
conformant.
