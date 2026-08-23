# Stage 2: transition and bridge contract research

> **Document kind:** Temporary research-package index
> **Document state:** Complete and absorbed; retained pending later package
> deletion
> **Authority:** None. This package evaluates transition architectures and
> records reconstruction evidence. It does not define a normative transition,
> mint authority, change implementation behavior, or authorize migration.
> **Started:** 2026-08-22
> **Completed:** 2026-08-22
> **Disposition:** Reviewed conclusions are promoted into their durable
> architecture and domain boundaries. Retain this package as temporary research
> evidence until later owners absorb its exact seams, then delete it before
> `docs-next/` authority cutover.

## 1. Central question

Stage 1 selected the semantic subjects and the canonical Protocol carrier.
Stage 2 asks:

> Which exact authority-bearing transitions connect those subjects and the
> neighboring domains, and what relation, identity effect, capability change,
> outcome, refusal, replay rule, and residual trust does each transition own?

The answer must cover current admitted boundaries and selected target
boundaries without pretending that every arrow is a lowering, every successful
result is a validity claim, or every similar contract needs one serialized
transition object.

The governing charter is the
[Stage 2 Transition and Bridge Charter](../stage-2-transition-and-bridge-charter.md).
The common method is the
[Design Research Method](../../project/design-research-method.md).

## 2. Fixed Stage 1 intake

Stage 2 treats the following as fixed provisional inputs:

- language-independent Protocol semantics with MLIR as the v0 structural
  carrier;
- a rich authoring/import workbench and a distinct small closed canonical PIR
  level;
- `Protocol = InteractiveCore + ChallengeInterpretation`;
- one total observable schedule owned by `InteractiveCore`;
- Fresh-public-coin and Fiat--Shamir Protocols related by `FSCompile`, not by
  representation equality;
- `ProtocolInterfaceId` as a dependent subject over `ProtocolId`;
- `ProverPlanId` as a separate dependent subject over `ProtocolId`;
- typed semantic regimes and compositional semantic identities;
- opaque process-local admission capabilities and purpose-specific views;
- fail-closed canonical extension and exact-v0 evolution;
- protected `TRANSCRIPT`, `WIRE`, `PUBLIC`, `CHECK`, `ARTIFACT`, `CLAIM`, and
  `TERMINAL` observations;
- named, noninterchangeable semantic relation families; and
- source-relative projection coverage that source-free OIR cannot establish
  by itself.

A Stage 2 result may refine a transition name, signature, or validation basis.
It may not silently move a field or effect across these boundaries. A genuine
contradiction must identify and formally reopen the affected Stage 1 decision.

## 3. Scope boundary

Stage 2 owns the cross-domain transition map and enough of each edge to make
its source, target, authority, identity, and outcome unambiguous. It does not
complete the downstream subject schemas.

| Stage 2 specifies | Later owner completes |
|---|---|
| Protocol lifecycle and admission edge contracts | Stage 3 PIR semantics and exact grammar |
| Interface consumption and ownership seams | Stage 3 Relations and Stage 4B OIR |
| ProverPlan obligation and consumption seams | Stages 3, 4A, and 4B |
| Analysis input/result category and claimed relation | Stage 4A Analysis |
| Checked-transform predecessor/successor contract | Stage 4A Compiler |
| Projection source, result, and coverage categories | Stage 4B OIR |
| Supplier, realization, deployment, and invocation categories | Stage 4B Realization |
| Observation, appraisal, and reliance separation | Stage 6 Evidence and relying consumers |

This boundary prevents both extremes: a transition stage that says only
“checked,” and a transition stage that prematurely designs every neighboring
domain.

## 4. Required research lenses

### 4.1 Reconstructive

- locate the exact current documentation owner for each transition;
- trace implementation types, functions, registries, passes, tests, and
  examples as correspondence evidence;
- enumerate declared and ambient reads;
- distinguish identity, authority, carrier, environment, configuration, and
  runtime state; and
- record conflicts and non-claims without resolving them by recency.

### 4.2 Generative

- compare domain-owned relation-specific contracts with universal transition
  records, capability-centric lifecycles, translation validation, portable
  certificates, direct recomputation, and no-artifact designs;
- ask what independent checking, replay, composition, alternative producers,
  and future consumers become possible under each model;
- study primary research and official specifications for mechanisms and
  difficult-to-reverse commitments; and
- keep alternatives alive even when the current boundary passes known tests.

### 4.3 Evaluative

- apply lifecycle, relabeling, cross-regime, checked-change, source-free
  projection, negative-judgment, realization, and evidence scenarios;
- compare authority, functional closure, identity, effect, replay,
  compositionality, independent implementability, extensibility, and cost;
- require explicit falsifiers and reversal conditions; and
- reject accidental wire formats and IDs without a named consumer.

### 4.4 Integrative

- review each bridge with both endpoint owners;
- reconcile Interface and ProverPlan fields across their consumers;
- maintain one observer/effect ledger and one semantic-regime ledger;
- ensure local edge choices compose without creating circular authority; and
- produce a Stage 3 entry contract that does not depend on current C++ names.

## 5. Candidate space kept open

The package begins with at least these architectural families:

1. domain-owned typed contracts using a shared descriptive review schema;
2. a universal transition algebra or durable transition record;
3. a capability-centric lifecycle with relation-specific semantic bridges;
4. producer proposals checked by per-edge validators or certificates; and
5. hybrid placement chosen per transition, including direct recomputation or
   no durable transition artifact.

The shared table columns in the charter are not evidence for one universal
runtime type. Conversely, mathematical relations with different meanings may
still share extracted mechanisms when their authority, lifetime, and refusal
semantics are genuinely identical.

## 6. Workstreams and working inventory

| Workstream | Working page | State |
|---|---|---|
| Current whole-system reconstruction | [Current Transition Catalog](current-transition-catalog.md) | Complete |
| Lifecycle, authentication, replay, and capabilities | [Lifecycle Spine](lifecycle-spine.md) | Complete |
| Relations, Analysis, Compiler, and checked semantic change | [Semantic Bridges](semantic-bridges.md) | Complete |
| OIR, Realization, operations, Evidence, and reliance | [Endpoint and Operational Bridges](endpoint-operational-bridges.md) | Complete |
| External transition and checking cases | [External Case Studies](cases/README.md) | Complete |
| Equal-resolution architectural candidates | [Candidate Frameworks](candidate-frameworks.md) | Complete |
| Cross-case synthesis | [Cross-Case Synthesis](cross-case-synthesis.md) | Complete |
| Target transition catalog and matrices | [Target Transition Catalog](target-transition-catalog.md) | Complete |
| Scenario evaluation and falsification | [Scenario Results](scenario-results.md) | Complete |
| Convergence and decision record | [Convergence](convergence.md) | Complete |
| Current-to-target gap map | [Current-to-Target Gap](current-to-target-gap.md) | Complete |
| Stage 3 handoff | [Stage 3 Entry Contract](stage-3-entry-contract.md) | Consumed by Stage 3.0 activation; retained as Stage 2 evidence |
| Durable absorption ledger | [Absorption Record](absorption-record.md) | Complete |

Every planned package output exists. These pages remain temporary and
non-authoritative even where they record the evidence behind a selected
durable architecture decision.

## 7. Common transition contract

Every candidate edge is described with the same review fields:

```text
name and transition family
current and target owner
source subject and required authority state
all semantic, carrier, environment, configuration, and policy inputs
binding time, snapshot, lifetime, concurrency, and side effects
result category and successful postcondition
exact named relation and explicit non-claims
identities consumed, preserved, minted, and cited as provenance
capability gained, narrowed, discarded, or reconstructed
malformed, unsupported, negative, refused, failed, and partial-effect outcomes
serialization, replay, independent checking, and supersession behavior
residual trust, checker alternative, scenarios, and reversal trigger
```

This is a research schema. Stage 2 required separate justification for every
shared runtime representation, ID, certificate, or framework; none was
selected merely from the common table shape.

## 8. Initial scenario portfolio

The initial portfolio includes:

1. authoring through canonical admission and cross-process re-admission;
2. equivalent authoring inputs and normalization refusal boundaries;
3. one Protocol with two external interfaces;
4. one Protocol with two ProverPlans;
5. Fresh-public-coin to Fiat--Shamir construction;
6. relation binding of an opaque Protocol anchor;
7. successful positive and negative Analysis judgments;
8. identity-preserving and content-changing compiler transforms;
9. projection with unsupported target events;
10. source-free OIR with unknown source coverage;
11. two supplier/deployment bindings for one OIR;
12. invocation failure after partial operational effects;
13. evidence supporting a bounded appraisal but not semantic truth; and
14. linked or composed Protocols with explicit observer and failure seams.

New candidates may add scenarios that the current design could not express.
The portfolio is a pressure source, not the definition of the design space.

## 9. Exit gate

Stage 2 closes only when:

- every current admitted and selected target boundary appears in a typed
  catalog;
- every edge is functionally closed over named inputs;
- every edge names its relation and identity effect;
- capability continuity is not laundered through bytes or copying;
- negative judgments, typed refusals, operational failures, appraisals, and
  reliance decisions remain distinct;
- Interface and ProverPlan seams are usable by their later co-design owners;
- checker placement has been compared per transition family;
- scenario and opportunity evaluation covers the selected candidate;
- reviewed conclusions are promoted without making durable pages depend on
  this temporary package; and
- a clean-room reviewer can begin Stage 3 from an explicit entry contract.

## 10. Current state

Stage 2 is complete. It selected domain-owned typed contracts under shared
invariants, a capability-centric local-authority lifecycle, direct checking for
small predicates, and proposal/validator separation only where the checker is
genuinely smaller or more stable. It did not select a universal transition
algebra, portable transition artifact, `TransitionId`, fact root, certificate,
or common capability/error type.

The durable result is the
[Transition and Bridge Architecture](../../project/transition-and-bridge-architecture.md).
The [Convergence Record](convergence.md) explains the candidate decision, the
[Absorption Record](absorption-record.md) accounts for promotion and deferral,
and the [Stage 3 Entry Contract](stage-3-entry-contract.md) defines the next
clean-room gate. The exit conditions in Section 9 are satisfied.

Stage 3 was subsequently activated through that bounded handoff and completed
on 2026-08-22. No implementation change, normative migration, or authority
cutover is authorized, and the current specifications under `docs/` remain
authoritative.
