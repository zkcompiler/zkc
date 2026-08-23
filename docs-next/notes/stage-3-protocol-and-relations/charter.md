# Stage 3 Protocol, Canonical PIR, and Relations charter

> **Document kind:** Temporary design-research charter
> **Document state:** Satisfied Stage 3 charter; retained as bounded research
> and reopening contract
> **Authority:** None. This charter bounds research. It does not define a
> normative schema, ratify a target model, report implementation conformance,
> authorize migration, or open Stage 4.
> **Activated:** 2026-08-22
> **Inputs:** Selected Stage 1 and Stage 2 target architectures and the
> accepted Stage 2-to-Stage 3 entry contract.
> **Disposition:** Absorb reviewed semantic conclusions into `pir/`,
> `relations/`, and the exact cross-domain owner; retain only bounded handoffs
> and durable rationale; delete this temporary charter before cutover.

## 1. Activation decision

Stage 3 was activated through this charter on 2026-08-22. At activation, only
Stage 3.0 was complete: inherited decisions were reconciled, the package was
bounded, and the research and exit contracts were fixed. Stages 3.1--3.5 have
since completed under those bounds.

Activation does not imply agreement with a particular Protocol grammar,
relation ontology, canonical PIR operation set, composition algebra, or
Fiat--Shamir construction. It establishes the process by which those decisions
can later become reviewable.

## 2. Central question

How should zkc define one complete language-independent Protocol semantic
model, encode it without semantic loss in a small closed canonical PIR, and
relate it to independently owned relation subjects while preserving explicit
identity, authority, observation, outcome, composition, and later-stage
boundaries?

The answer must be native to interactive and non-interactive zero-knowledge
protocols. It must account for typed events, causal and transcript order,
challenge interpretation, abstract prover obligations, committed objects,
relation ingress, repeated occurrences, Fiat--Shamir construction, and
multi-Protocol composition. General-purpose IR precedent is evidence, not the
objective.

## 3. Fixed intake

Later Stage 3 work consumes these decisions unless a reopening record satisfies
Section 12.

### 3.1 Subject and carrier architecture

1. Normative Protocol meaning is language-independent. MLIR is the primary v0
   structural carrier and transformation workbench, not semantic authority.
2. Rich authoring, import, and synthesis forms precede one distinct small,
   closed, physically canonical PIR level in MLIR.
3. `InteractiveCore` owns roles, canonical semantic ports, typed events,
   causal constraints, one identity-bearing total observable schedule, fresh
   public challenges, claims, reductions, checks, terminals, exact failure
   classes, and abstract prover obligations.
4. A Protocol is one Core plus exactly one challenge interpretation:

   ```text
   ChallengeInterpretation =
       FreshPublicCoins
     | FiatShamir(TranscriptConstructionId)

   Protocol = InteractiveCore + ChallengeInterpretation
   ```

5. Fresh-public-coin and Fiat--Shamir Protocols over one Core are distinct
   subjects connected by an explicit construction and later theorem- or
   model-backed relation, never by representation equality.
6. `ProtocolInterface` and `ProverPlan` are separate identity-bearing subjects
   dependent on the exact `ProtocolId`; one Protocol may have several of each.
7. Semantic identity commits to the typed semantic regime and canonical
   semantic content. Carrier bytes, transport, tool release, and process-local
   authority are separate axes.
8. Protected observations include `TRANSCRIPT`, `WIRE`, `PUBLIC`, `CHECK`,
   `ARTIFACT`, `CLAIM`, and `TERMINAL`.
9. Exact-v0 admission is fail-closed. Decoder success and byte equality do not
   establish semantic preservation across regimes.

### 3.2 Lifecycle and transition architecture

1. The canonical lifecycle remains:

   ```text
   AuthoringUnit
     -> ResolvedAuthoringUnit
     -> CanonicalProtocolCandidate
     -> AuthenticatedCanonicalProtocol
     -> AdmittedProtocol
   ```

2. Physical canonical authentication and whole-Protocol admission are
   separate judgments with separate qualified outcomes.
3. Authority is process-local and minted only by the owning boundary. Bytes,
   digests, signatures, provenance, or a serialized admitted marker do not
   transport live authority.
4. Stage 2 selected domain-owned typed contracts under Project-owned shared
   closure, authority, outcome, replay, composition, and persistence
   invariants. It rejected a universal transition runtime, algebra, record,
   checker registry, certificate envelope, and fact root.
5. A target's admission is distinct from the checked relation between a
   predecessor and successor.
6. Direct recomputation is preferred for a small stable predicate. A proposal
   plus validator is used only when the validator is meaningfully smaller,
   more stable, independently useful, or required at a boundary. Otherwise
   residual trust remains explicit.
7. Plan admission is distinct from `PlanRealizes`. Artifact interpretation is
   distinct from relation correspondence. `LocalOirValid` is distinct from
   `ProjectionCorrect`.
8. Observation, evidence record, claim appraisal, and use-specific reliance
   are one-way, non-interchangeable results.

### 3.3 Relations that must remain named

Stage 3 must preserve rather than collapse at least these relations:

- representation equivalence;
- Core equivalence;
- Protocol equivalence;
- observer-indexed trace equivalence and refinement;
- distributional equality or bounded closeness;
- Fresh-to-Fiat--Shamir construction and `FSCompile`;
- projection correctness;
- `PlanRealizes`;
- property-specific transport;
- intentional semantic change; and
- cost relation.

Each selected relation later needs a direction, signature, assumptions,
observer set, outcomes, composition rule or non-rule, checking owner, and
residual-trust statement.

## 4. Ownership and seams

Stage 3 jointly owns:

- complete Protocol semantics and the canonical PIR contract;
- Protocol-to-canonical-PIR correspondence and permitted carrier trivia;
- canonical identity, authentication, admission, occurrence references, and
  immutable capability seams;
- the Stage 3 portion of `ProtocolInterface` and `ProverPlan` semantics;
- relation definition, interface, instance, witness, committed-object,
  ingress, optional artifact interpretation, and Protocol-at-Interface
  correspondence;
- exact Fresh-to-Fiat--Shamir subject construction and the bounded seam handed
  to later Analysis for `FSCompile` and property transport; and
- semantic Protocol composition, distinct from authoring link and transition
  adjacency.

`pir/` will own Protocol and canonical PIR meaning. `relations/` will own
relation subjects and relation-local ingress. Cross-domain correspondence must
name both exact subjects and cannot change either owner's meaning. Project
governance owns only shared invariants and the decision program.

Stage 3 must export narrow, mutually consistent inputs to both later branches.
It does not let Analysis, Compiler, OIR, or Realization create a duplicate
Protocol model.

## 5. Explicit non-goals

Stage 3 does not:

- migrate, refactor, or implement the target architecture;
- design around current migration cost;
- choose concrete C++, Rust, MLIR, JSON, file, package, or API spellings merely
  to match the checkout;
- select a theorem prover, proof system, cryptographic primitive, backend,
  build system, or deployment topology;
- prove relation satisfaction, soundness, knowledge, completeness, zero
  knowledge, Fiat--Shamir security, compiler correctness, projection
  correctness, realization correspondence, or evidence sufficiency;
- complete Analysis, Compiler, OIR, Realization, deployment, invocation,
  Evidence, appraisal, or reliance schemas;
- decide exact `ProverPlan` field placement between projection and realization;
  it owns only the semantic classes, constraints, obligations, and consumer
  requirements needed for Stage 4B to decide placement; or
- introduce a universal fact root, transition record, certificate envelope,
  capability type, error enum, or proof object.

## 6. Research sequence

### Stage 3.0: activate and bound

Reconcile the Stage 2 entry contract with selected durable architecture,
publish this charter and package index, mark the program active, and state
precisely what has not begun.

**State:** Complete.

### Stage 3.1: reconstruct

Trace the current owning specifications, architecture, implementation, tests,
and examples for Protocol grammar, PIR carriers, relation ingress, committed
objects, linking, Interface-like labels, Plan-like routes, Fiat--Shamir
behavior, and composition. Separate intended semantics from implementation
correspondence, retained history, gaps, conflicts, and unknowns.

**State:** Complete.

### Stage 3.2: expand the design space

Derive zkc-native forces and capability opportunities independently of current
types. Study primary research and mature IR, protocol, proof-system,
Fiat--Shamir, relation, and composition designs. Record both successful design
choices and path-dependent limitations. Produce at least four materially
different candidate architectures at equal resolution.

**State:** Complete.

### Stage 3.3: instantiate and falsify

Instantiate every viable candidate deeply enough to expose semantic subjects,
identities, regimes, closure, observations, authority, outcomes, composition,
checker placement, and later consumers. Apply current cases, new capability
opportunities, counterexamples, required scenarios, and producer/consumer seam
reviews.

**State:** Complete.

### Stage 3.4: integrate and converge

Converge Protocol/PIR and Relations as one model. Select, reject, or defer
candidates with evidence, falsifiers, reversal triggers, non-claims, and exact
owners. Record the gap from current reality without turning it into a migration
plan.

**State:** Complete.

### Stage 3.5: promote and hand off

Promote complete conclusions into durable owners, record temporary-note
absorption, and publish separate but compatible Stage 4A Analysis/Compiler and
Stage 4B OIR/Realization entry contracts.

**State:** Complete.

## 7. Required work products

Stage 3 cannot exit without independently reviewable coverage of:

1. current Protocol/PIR-and-Relations reconstruction and correspondence;
2. native design forces, opportunities, primary-source cases, and at least
   four equal-resolution architectures;
3. complete Protocol semantics and a closed canonical PIR contract;
4. Protocol-to-canonical-PIR correspondence and information-loss ledger;
5. identity, regime, dependency, occurrence, authentication, admission,
   outcome, capability, replay, checker, and residual-trust matrices;
6. complete `ProtocolInterface` boundaries and field ownership;
7. bounded `ProverPlan`, admission, `PlanRealizes`, obligation, semantic-class,
   placement-constraint, and Stage 4B reader requirements;
8. Relations ontology, ingress, optional artifact interpretation, and exact
   Protocol-at-Interface correspondence;
9. Fresh-to-Fiat--Shamir construction, occurrence and prefix maps, and a
   bounded `FSCompile` handoff;
10. Protocol composition and its distinction from authoring link;
11. the named-relation, protected-observation, effect, closure/read-set,
    refusal, and consumer matrices;
12. scenario, opportunity, and candidate-falsification results;
13. current-to-target gaps, convergence, promotion, and absorption records;
    and
14. separate Stage 4A and Stage 4B entry contracts.

Files are created when their work starts, not as empty placeholders. A later
package may split or combine pages if every role remains traceable and
independently reviewable.

## 8. Candidate and evidence discipline

Research must apply four lenses together:

1. current normative intent;
2. implementation and test correspondence;
3. theory and external precedent; and
4. clean-sheet opportunity and future capability.

At least one candidate must preserve the current conceptual model, one must
complete or align it, one must structurally redesign it, and one must expand
capability. A candidate is not equal-resolution until its ownership,
identities, regime behavior, closure, observations, outcomes, composition,
checking, refusals, and consumers are concrete enough for the same scenarios.

External examples are dossiers, not votes. Prefer primary specifications,
papers, and source repositories; distinguish designed guarantees from observed
implementation behavior; and record which inherited constraints made a
system's difficult-to-reverse choices rational.

Code and tests can confirm correspondence, feasibility, and current behavior.
They cannot silently establish intended semantics. A prototype is allowed
only when specifications, theory, and existing evidence cannot decide a
bounded feasibility question; it remains non-authoritative.

## 9. Required scenario families

The candidate portfolio must cover:

- normalization, protected observations, regimes, physical canonicality, and
  whole-Protocol admission;
- multiple Interfaces for one Protocol and Interface attempts to change
  semantics;
- relation ingress without bytes, later artifact agreement or conflict,
  negative correspondence, and committed-object grounding;
- multiple Plans and supplier strategies without verifier-visible semantic
  change;
- Fiat--Shamir Protocol admission with unavailable theorem/model basis, plus
  multiple property transports with different assumptions;
- repeated child occurrences, alternative interleavings, and attempts to
  replace composition with graph union, static link, or transition adjacency;
- structural relation success without a property-transport rule;
- serialization and process boundaries that cannot carry live capability; and
- target-local OIR validity without source-relative coverage.

Every scenario records declared inputs, subject and authority states, exact
result relation, qualified outcomes, identity and capability effects, and a
falsifier. Cross-cutting probes vary hidden resolvers, carriers, theorem bases,
compilers, registries, and policies; distinguish all negative and failure
outcomes; attempt laundering across relation, identity, capability,
composition, and property boundaries; and search for capability unlocked by a
non-current architecture.

## 10. Stage 3.0 exit gate

Stage 3.0 is complete only because:

- Stage 2 has a reviewed convergence record, current-to-target gaps, durable
  destinations, and absorption record;
- the entry contract was reconciled with selected Stage 1 and Stage 2 durable
  architecture;
- this charter and the package index publish one bounded research sequence;
- the program and relevant navigation identify Stage 3 as active at this exact
  boundary; and
- no reconstruction, case selection, target schema, implementation work,
  migration planning, proof claim, or Stage 4 decision was started.

## 11. Whole-Stage exit gate

Stage 3 exits only when a clean-room reader can reconstruct the selected
Protocol, canonical PIR, Interface, Plan, relation, Fiat--Shamir, and
composition meanings without current class names or ambient registries; every
identity and predicate has one owner and closed immutable inputs; carrier and
semantic correspondence is explicit; every named relation and qualified
outcome has bounded authority; all required scenarios pass; and both Stage 4
branches receive stable, mutually consistent narrow views.

A grammar draft alone is insufficient. Protocol/PIR and Relations, including
Interface and Plan seams, pass one convergence review. Reviewed conclusions
must be promoted, deferrals and rejections must retain reversal triggers, and
documentation validation must succeed.

This gate is satisfied. The completed package records reconstruction,
primary-source research, five equal-resolution candidates, a frozen target,
independent audits, convergence, current-to-target correspondence, durable
promotion, and mutually consistent Stage 4A/4B handoffs. The package index,
absorption record, and exit audit provide the closing accounting. Closure does
not activate Stage 4 or authorize implementation, migration, or cutover.

## 12. Reopening and change control

An inherited decision may be reopened only by an exact counterexample,
ownership or identity contradiction, impossible clean-room interpretation,
materially better capability with explicit costs, or later consumer evidence
that the inherited seam cannot represent a semantic input owned upstream.

Every reopening record names:

```text
contradicted decision and falsifying evidence
affected subjects and semantic regimes
authority and identity consequences
relation, observer, capability, and outcome consequences
at least one equal-resolution alternative
affected producers and consumers
new compatibility or wire commitment, if any
downstream contracts requiring re-review
```

Reopening cannot be hidden in generic metadata, an unchecked exception, a
widened success result, a carrier spelling, or a downstream schema. It pauses
only the affected conclusion and its dependents; it does not erase the
historical decision or broaden this charter automatically.
