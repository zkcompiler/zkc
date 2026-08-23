# Zkc-native Protocol IR design forces

> **Document kind:** Temporary research ledger
> **Document state:** Initial reconstruction
> **Provisional owner:** `project`
> **Authority:** None. Observations reconstruct current intent and implementation;
> hypotheses and opportunities remain open design input.
> **Disposition:** Absorb selected invariants and boundaries into Protocol,
> carrier, compiler, analysis, OIR, and architecture owners after convergence,
> then delete this page.

## 1. Purpose

This ledger derives PIR design pressures from zkc before comparative cases are
allowed to influence the architecture. It prevents a successful external IR
from becoming the implicit problem statement.

The ledger distinguishes:

- **intended force:** follows from the product or semantic problem zkc has
  chosen;
- **current observation:** follows from a current normative owner or checkout;
- **hypothesis:** a plausible abstraction that research must test;
- **opportunity:** a valuable capability a candidate may enable; and
- **open choice:** cannot yet constrain the architecture.

Current mechanisms are feasibility evidence, not clean-room requirements.

## 2. Intended semantic subject

### F1. Protocols, not relations or endpoint binaries

**Intended force.** zkc's subject is an already formed zero-knowledge protocol
above relation, circuit, and AIR representations and above the eventual
machine implementation. It must neither absorb relation satisfaction into
Protocol meaning nor let a concrete endpoint backend redefine the Protocol.

**Current observation.** The current architecture keeps relation compilation
upstream, seals PIR, and projects admitted Protocols into OIR endpoint programs.

**Design consequence to test.** Relation IR, Protocol IR, endpoint IR, and
target IR need distinct semantic contracts even if they share one MLIR module
or conversion framework.

### F2. Two coupled geometries

**Intended force.** A Protocol couples an ordered transcript/effect spine with
a typed claim and reduction flow graph. Neither structure is a derived display
of the other.

```text
transcript: event_0 <= event_1 <= ... <= event_n
claims:     producers -> reductions -> terminal consumers
```

**Current observation.** PIR uses block order and threaded transcript values
for event order, while SSA claim values and consumption represent claim flow.

**Hypothesis.** An architecture optimized only for SSA/dataflow or only for an
event trace will hide a semantic dependency and make transformations difficult
to classify.

### F3. Observable order is semantic

**Intended force.** Message absorption, challenge sampling, checks, and proof
stream interactions are ordered effects. Reordering operations can preserve
types and use-def relations while changing transcript state, challenge values,
or the statement ultimately checked.

**Design consequence to test.** PIR needs an explicit effect/order model and
cannot inherit ordinary pure-DAG equivalence as its default preservation law.
Generic rewrites require an admitted scope or a proof/check of noninterference.

### F4. Fiat--Shamir structure is more than a hash call

**Intended force.** Challenge derivation depends on the ordered absorbed
history, framing, domains, sampling rules, counts, and dependencies. Structural
Fiat--Shamir admissibility and cryptographic property arguments remain
different judgments.

**Open choice.** Whether Fiat--Shamir is represented directly in canonical PIR,
as a handler/projection from an interactive form, or through a separate
protocol layer remains open.

## 3. Validity, authority, and property separation

### F5. Local IR validity is not Protocol admission

**Intended force.** Operand types, region shape, dominance, and operation-local
verification cannot establish whole-Protocol linearity, binding, dependency
closure, exact external contract resolution, or projection obligations.

**Current observation.** MLIR verification, seal, artifact decode, and exact-
environment admission are separate boundaries.

**Design consequence to test.** Every candidate must say which invariants are
local, whole-object, environment-relative, consumer-relative, or deliberately
outside admission.

### F6. Structural admission is not a security theorem

**Intended force.** A sealed Protocol carries structure and exact semantic
dependencies. Soundness, completeness, knowledge, zero knowledge, and their
bounds arise from explicit rules, bindings, assumptions, and derivations about
that exact subject.

**Current observation.** The Soundness Kernel consumes an authenticated,
MLIR-free fact view derived from admitted PIR and returns typed conditional
judgments.

**Design consequence to test.** The IR must expose sufficient authenticated
facts without embedding theorem choice or treating a successful execution as
a property proof.

### F7. Data, identity, admission, and capability are different

**Intended force.** Serialized bytes can identify a subject without carrying
process-local authority to rely on it. Loading, decoding, identity
authentication, semantic admission, and consumer authorization are distinct.

**Current observation.** `DecodedPirArtifact` and `AdmittedPirArtifact` are
separate opaque C++ capabilities; a mutable clone loses authority and must be
resealed and re-admitted.

**Design consequence to test.** A portable representation, if selected, cannot
replace admission merely because another implementation can decode it.

## 4. Identity and representation

### F8. Identity should name semantic content, not printer accidents

**Intended force.** Source location, pretty syntax, temporary symbols, and
human display names should not change Protocol identity unless they define an
external semantic interface.

**Current observation.** The canonical encoder walks typed op state and
normalizes references into semantic position spaces rather than hashing MLIR
text or bytecode.

**Open choice.** The exact quotient over authoring forms, interface names,
dependency manifests, semantic language versions, and construction plans is
reopened.

### F9. Interface data creates genuine identity pressure

**Current observation.** Current PIR identity erases some author labels while
OIR identity and relation wiring can consume endpoint-facing labels. One
`ProtocolId` can therefore participate in several label-sensitive downstream
artifacts unless the transition takes an additional authenticated input.

**Open choices.** Research must compare:

- semantic port positions derived entirely from Protocol content;
- a first-class `ProtocolInterface` committed by `ProtocolId`;
- a separately identified interface paired at projection or relation binding;
- or an authoring-to-canonical lowering that erases names only after producing
  stable semantic ports.

### F10. Semantic, dialect, carrier, and producer versions differ

**Intended force.** The interpretation of Protocol content, the layout of PIR
operations, the serialized transport, and the tool that emitted bytes can
evolve independently.

**Current observation.** v0 separates canonical content identity, MLIR dialect
version, and producer marker but intentionally has no compatibility window.

**Opportunity.** A clean design can preserve a future portable boundary without
paying ongoing compatibility cost before an external trust boundary exists.

### F11. Multiple representations are useful only with one correspondence

**Hypothesis.** A second authoring, portable, formal, or checking
representation is valuable only if its relation to the Protocol subject is
specified and mechanically enforced. A manually synchronized full shadow IR
creates two potential semantic authorities.

**Open choice.** A second MLIR dialect with full conversion, a versioned
serialization dialect, an immutable semantic package, and a lossy consumer
view have different costs and must not be grouped as “carrier independence.”

## 5. Transformation and compilation

### F12. Protocol transforms are not ordinary functional optimizations

**Intended force.** A transform may alter Protocol identity, transcript shape,
proof size, prover/verifier cost, conditional security loss, assumptions, or
available construction plans while retaining a useful relation to its source.

**Current observation.** The Compiler Core separates finite-domain search and
decision logic from a PIR provider that reopens, transforms, reseals,
re-admits, and replay-checks a successor.

**Design consequence to test.** Candidate architectures must distinguish:

```text
representation equivalence
Protocol equality
behavioral equivalence
refinement
property preservation under assumptions
checked non-preserving change
candidate generation with no accepted claim yet
```

### F13. Search, realization, and validation have different authority

**Intended force.** An optimizer may search a large or heuristic candidate
space without becoming the authority for legality or property preservation.

**Opportunity.** MLIR Transform dialects, declarative rewrites, e-graphs, or
external search may propose transformations while smaller checkers validate
the selected transition.

**Open choice.** Whether preservation is intrinsic to each transform family,
carried by a portable witness, replay-checked, translation-validated, or proven
in a formal model remains open by transition class.

### F14. Multiple abstraction levels have different optimization laws

**Intended force.** Relation construction, Protocol change, endpoint
projection, endpoint scheduling, and machine lowering are not interchangeable
passes.

```text
relation/source level
Protocol level
endpoint level
realization level
machine level
```

**Design consequence to test.** A multi-dialect architecture should make legal
states and transitions explicit. Mixed dialects are useful only where their
semantic ownership and conversion completeness are known.

## 6. Endpoints, execution, and construction

### F15. One Protocol has asymmetric endpoints

**Intended force.** Verifier and prover endpoints share transcript semantics
but differ in proof-stream direction, witness authority, construction work,
checks, and failure behavior.

**Current observation.** One admitted PIR projects to verifier or prover-
skeleton OIR, with coverage and provenance checked at projection.

**Design consequence to test.** Endpoint identity and ABI must be pure functions
of explicitly identified inputs. Hidden carrier labels or ambient resolver
lookups are not acceptable inputs.

### F16. Abstract prover obligations and concrete construction may separate

**Hypothesis.** A Protocol can define what prover messages must represent while
several construction plans or implementations realize those obligations.

**Open choice.** Research must decide which route, hole, witness, scheduling,
and randomness choices are Protocol semantics, endpoint semantics, prover-plan
semantics, or concrete realization bindings. Splitting them too early can omit
completeness-relevant behavior; binding them too early prevents reuse.

### F17. Execution is an observation, not retroactive meaning

**Intended force.** A run can accept, reject, refuse, or fail without changing
the meaning or validity of its Protocol or endpoint subject. Concrete suppliers
and deployment state must not authorize upstream semantics.

## 7. Dependencies, extensibility, and composition

### F18. External references have different semantic authority

**Intended force.** Some cited entries are interpreted during Protocol
admission; others are opaque relation/material subjects; others are endpoint or
runtime supplier bindings.

**Current observation.** Prior Stage 1 distinguished a typed seal-authority
graph from an opaque referenced-subject graph and from the broader retained
resolver environment.

**Design consequence to test.** Extension and package systems must make binding
time, unknown-content policy, closure, and identity effect explicit per
dependency class.

### F19. Extensibility must not produce permissive unknown semantics

**Intended force.** New checks, reductions, claims, codecs, and construction
roles should be addable without silently teaching an old consumer a new
meaning.

**Open choices.** Compare closed canonical opsets, digest-addressed semantic
contracts, capability/version declarations, dialect extensions lowered before
seal, and opaque custom operations refused by consumers that cannot interpret
them.

### F20. Composition changes more than graph connectivity

**Intended force.** Linking or recursively invoking protocols can affect
transcript domains, event interleaving, statement interfaces, claim routes,
assumptions, failure propagation, and property transport.

**Design consequence to test.** Function linking, module composition, graph
union, and protocol composition are distinct analogies. A useful IR must make
the extra obligations representable rather than hiding them in a linker.

## 8. Tooling, interoperability, and trust

### F21. MLIR has real value only if zkc performs real transformations

**Current observation.** MLIR currently supplies ODS structure, parser/printer,
located diagnostics, use-def tracking, tests, pass infrastructure, PIR
transformation, and PIR-to-OIR construction. The current carrier specification
also observes that much of the investment is paid in advance until synthesis
and more transform families exist.

**Decision pressure.** The ideal carrier depends on whether zkc's central
product becomes a transformation and synthesis workbench, a stable exchange
format and independent checker, or deliberately both through separate layers.

### F22. Cross-language value is boundary-specific

**Current observation.** Canonical OIR already has C++, Python, and Rust
consumers because execution and emission are useful external boundaries. PIR
does not yet have an equivalent external consumer.

**Hypothesis.** Requiring every internal Protocol representation to be
language-neutral may impose a lowest-common-denominator schema. Conversely,
waiting too long can make accidental compiler internals the permanent public
contract.

**Open choice.** The package must identify the latest responsible point and a
concrete trigger for portable PIR rather than answering “portable now” or
“internal forever” by taste.

### F23. Formalization needs a correspondence boundary

**Opportunity.** A small mathematical Protocol model or proof-assistant
datatype may support proofs of well-formedness, preservation, or selected
analyses without becoming the mutable compiler IR.

**Open choice.** Compare direct formalization of PIR semantics, extraction to a
formal core, certified checkers over a canonical encoding, and proof-carrying
transition witnesses. None automatically proves the implementation-to-model
correspondence.

## 9. Capability opportunities

The research must compare not only current behavior but what each architecture
could enable:

- protocol synthesis from relation and security constraints;
- security-parameter synthesis over explicit challenge and dependency data;
- several authoring dialects lowering into one canonical Protocol form;
- stable independent checking without importing the optimizing compiler;
- several compiler implementations sharing a portable Protocol boundary;
- formal checking of selected transforms or judgments;
- exact content-addressed caching across representation changes;
- multiple interfaces or prover plans over reusable Protocol cores;
- protocol composition with transported assumptions and obligations;
- target-specific endpoint lowering without contaminating Protocol identity;
- declarative extension contracts with fail-closed older consumers; and
- translation validation for untrusted or heuristic optimization.

An opportunity becomes a requirement only after value, prerequisites, and
latest responsible decision point are established.

## 10. Initial counterexamples

These probes are not a complete scenario suite.

### C1. SSA-preserving transcript reorder

Two operations have no SSA dependency but both affect the transcript. A generic
rewrite swaps them. Types and dominance remain valid; challenge semantics may
change.

### C2. Label erasure with endpoint ABI dependence

Two authoring artifacts normalize to one current Protocol identity after label
erasure, but their projected OIR entry signatures or relation wiring differ.

### C3. Equivalent authoring syntax, different transport bytes

Two PIR texts differ only by locations, symbol names, default spelling, or
nonsemantic order. A semantic identity should agree even if MLIR text or
bytecode differs.

### C4. Same verifier behavior, different prover plan

Two concrete prover strategies produce messages accepted by the same verifier
and satisfy the same abstract obligations but have different witness access,
randomness, cost, or completeness properties.

### C5. Unknown extension under an old consumer

A new reduction or check contract is valid under a newer environment. An older
consumer must not ignore it, reinterpret it, or accept only the visible shape.

### C6. Property-changing cost optimization

A transform reduces proof bytes but changes a soundness bound or adds an
assumption. It is useful yet is neither semantic equality nor unconditional
preservation.

### C7. Composed transcript domain collision

Two individually valid protocols are linked without an adequate composition
or domain-separation rule. Graph union is structurally possible but does not
establish a valid composed Protocol.

### C8. Old carrier, same intended semantic object

A future carrier layout or dialect revision can express the same Protocol.
The design must say whether identity remains, whether a versioned
interpretation is required, and which component validates correspondence.

## 11. Questions external cases must help answer

1. Which distinctions deserve separate dialects rather than lifecycle states,
   operation subsets, interfaces, or attributes?
2. Should canonical PIR be optimized for transformation, interchange,
   independent checking, or a deliberate combination?
3. When does an internal IR become an accidental public ABI?
4. What compatibility mechanism is necessary before and after external
   consumers exist?
5. How should unknown extensions fail without making the base language
   permanently closed?
6. Which semantic laws can MLIR traits or interfaces express, and which require
   zkc-owned whole-object judgments?
7. What is the smallest independent-checker input that does not duplicate the
   complete Protocol schema?
8. Should authoring forms lower into a canonical Protocol dialect before seal,
   or is seal itself that conversion?
9. Can identity remain stable across carrier revisions without making old
   meanings mutable?
10. Which protocol transformations can be replay-checked, locally validated,
    translation-validated, or must remain trusted?

## 12. Current state

This is an initial force ledger. It has not yet incorporated the comparative
case studies or theory track and makes no carrier recommendation. Each force
must be retained, refined, split, or rejected during synthesis with its source
and transfer logic visible.

