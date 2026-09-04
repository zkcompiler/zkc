# Stage 3 Protocol-and-Relations entry contract

> **Document kind:** Temporary Stage 2-to-Stage 3 entry gate
> **Document state:** Consumed by Stage 3.0 activation; retained as Stage 2
> handoff evidence
> **Authority:** None. This contract bounded a future design-research package.
> It does not define a normative schema, change current
> specifications, authorize implementation work, or authorize migration.
> **Inputs:** The selected Stage 1
> [Protocol IR architecture](../../project/protocol-ir-architecture.md), the
> selected Stage 2
> [Transition and Bridge Architecture](../../project/transition-and-bridge-architecture.md),
> and this package's target catalog, gap map, convergence, and absorption
> records as temporary handoff evidence.
> **Disposition:** Stage 3.0 reconciled this handoff and absorbed its operating
> boundary into the active
> [Stage 3 package](../stage-3-protocol-and-relations/README.md). Retain this
> file as Stage 2 evidence until its deletion gate; durable pages must not
> depend on it at authority cutover.

> **Completion notice — 2026-08-22:** Stage 3 subsequently completed this
> contract, selected and promoted its target, and produced separate unactivated
> Stage 4A and Stage 4B handoffs. Historical gate wording below is retained as
> the intake that Stage 3 received.

## 1. Gate purpose and status

Stage 3 is the joint design package in which the selected Protocol
factorization becomes an exact semantic contract and is co-designed with the
relation subjects that meet it. It is not a PIR-only grammar exercise and it
is not an independent Relations exercise. Neither side may complete by
inventing facts, identifiers, or authority that the other side did not expose.

This page fixes:

- the decisions Stage 3 must consume rather than silently reopen;
- the questions Stage 3 owns;
- the artifacts and validation required before Stage 4 can begin;
- the exact seams exported to later owners; and
- the evidence required to reopen an inherited decision.

It intentionally does not answer the schema questions it assigns. Terms such
as `InteractiveCore`, `ProtocolInterface`, `ProverPlan`, and relation-domain
interface identify semantic roles selected upstream, not final type, API,
dialect, file, or wire spellings.

Stage 3 was activated on 2026-08-22 at the bounded Stage 3.0 charter and intake
gate. Stage 2 had selected the durable Transition and Bridge Architecture and
incorporated all target-catalog rectifications recorded in convergence Section
4, including the separation of Plan admission from `PlanRealizes`. At that
activation instant, Stage 3.1 and semantic design had not started; the complete
Stage 3 package has since satisfied this entry contract.

## 2. Fixed intake

### 2.1 Semantic subjects and representation

Stage 3 consumes the following Stage 1 decisions as fixed inputs:

1. Normative Protocol meaning is language-independent. MLIR is the primary v0
   structural carrier and transformation infrastructure; it is not semantic
   authority.
2. Rich authoring, import, and synthesis languages precede one distinct small,
   closed, physically canonical PIR level in MLIR.
3. `InteractiveCore` owns roles, canonical semantic ports, typed events, fresh
   public challenges, mandatory causal dependencies, one identity-bearing
   total observable schedule, claim/reduction/check/terminal structure,
   abstract prover obligations, semantic dependencies, and exact failure
   classes.
4. A Protocol selects exactly one challenge interpretation:

   ```text
   ChallengeInterpretation =
       FreshPublicCoins
     | FiatShamir(TranscriptConstructionId)

   Protocol = InteractiveCore + ChallengeInterpretation
   ```

5. Fresh-public-coin and Fiat--Shamir Protocols over one Core are different
   Protocol subjects. Their connection is not representation equality.
6. `ProtocolInterface` and `ProverPlan` are separately identified subjects
   dependent on the exact `ProtocolId`. One Protocol may have several of each.
7. Semantic identities commit to the typed semantic regime and canonical
   semantic content. Carrier bytes, printer output, transport schema, tool
   release, and process-local authority are separate axes.
8. The protected observation classes include `TRANSCRIPT`, `WIRE`, `PUBLIC`,
   `CHECK`, `ARTIFACT`, `CLAIM`, and `TERMINAL`. Pure SSA independence does not
   authorize a rewrite observable by any protected class.
9. Canonical Protocol admission is obligation-complete at the abstract source
   level. A target-specific endpoint may still refuse unsupported events.
10. A source-free OIR may establish target-local validity but cannot establish
    omitted-source coverage without admitted source authority or sufficient
    source-bound checked evidence.
11. Exact-v0 handling is fail-closed. A semantic-regime change cannot silently
    preserve semantic identity; decoder success is not a migration judgment.

These inputs may be reopened only under Section 11, never by choosing a
convenient grammar production or copying a current implementation field.

### 2.2 Lifecycle and authority

Stage 3 consumes this capability-centric lifecycle:

```text
AuthoringUnit
  -> ResolvedAuthoringUnit
  -> CanonicalProtocolCandidate
  -> AuthenticatedCanonicalProtocol
  -> AdmittedProtocol
```

The arrows are domain-owned contracts, not one universal transition type.

- Authoring and import produce unauthoritative proposals.
- Resolution closes actual environmental reads against an immutable snapshot.
- Normalization produces one canonical candidate and may extract separately
  typed Interface, Plan, provenance, or source-map candidates.
- Authentication recomputes semantic identities and establishes canonical
  profile, representation, and dependency-preimage integrity.
- Admission establishes whole-Protocol semantics under the exact regime and
  immutable dependency closure, then mints a narrow process-local capability.
- Authentication and admission are logically distinct result categories even
  if an implementation fuses their traversals.
- Official Protocol persistence consumes `AdmittedProtocol`; workbench caches
  use a distinct unauthoritative envelope. Neither serializes local authority,
  and decoding is followed by fresh authentication and admission.
- Reopening or mutation produces an unauthoritative authoring branch without
  revoking the still-immutable source capability.
- Authoring link, semantic composition, and checked Protocol change are
  different operations. A checked change orders its steps as proposal, target
  authentication, target admission, and only then an exact predecessor/target
  relation check. Refuting that relation does not revoke the independently
  admitted target. Each newly constructed semantic subject crosses
  authentication and admission again.
- Purpose-specific views attenuate authority. They do not become a second
  complete Protocol model.

Stage 3 must assign every exact canonical-formation and whole-semantic
predicate to authentication, admission, or a separately named later judgment.
It may refine the transition signatures, but it may not erase the logical
boundary or let a decoded marker mint authority.

### 2.3 Transition architecture

Stage 3 consumes the following selected Stage 2 architectural discipline:

1. Domain-owned typed contracts are the semantic ownership baseline.
2. Shared project machinery is limited to a descriptive contract schema,
   typed references, closure and regime checks, outcome vocabulary, and
   catalog validation whose meaning is truly common.
3. Process-local capabilities protect admission boundaries. Serialized data
   remains capability-neutral.
4. Direct recomputation is preferred for small closed predicates. A
   producer/validator split is selected only per edge when the validator is
   meaningfully smaller or more stable for a named consumer.
5. A portable witness, certificate, receipt, or compatibility promise requires
   a concrete independent consumer, exact proposition, checker, retention
   contract, and residual-trust statement.
6. There is no global `TransitionId`, universal transition artifact,
   universal fact root, or generic validity relation in v0.
7. Every relied-on result is extensionally closed over declared immutable
   subjects, dependency preimages, semantic regimes, configurations, policies,
   and binding-time snapshots. Ambient resolver, compiler, carrier, registry,
   or realization reads are prohibited.
8. Producer, source owner, target owner, bridge/checker, and relying consumer
   are distinct authority roles even when one implementation initially
   performs several roles.
9. Formation, authentication, admission, mathematical relation, logical
   judgment, effectful occurrence, evidence appraisal, and reliance use
   qualified outcomes rather than one Boolean `valid` result.
10. Negative judgments, unsupportedness, cannot-answer, refusal, operational
    failure, and partial-effect failure remain different outcomes.
11. Identity preservation, identity reconstruction, new-subject construction,
    relation-result identity, and occurrence identity remain distinct effects.
12. Composition is relation-specific. Certificate adjacency, transition-chain
    adjacency, and graph union do not imply semantic transitivity.

### 2.4 Named relations that remain distinct

Stage 3 inherits the following noninterchangeable relation families:

```text
RepresentationEq
CoreEq
ProtocolEq
TraceEq[observer set]
TraceRefines[direction, observer set]
DistributionEq or DistributionClose[metric, bound]
FSCompile
ProjectionCorrect
PlanRealizes
PropertyTransport[property, direction, assumptions]
IntentionalChange
CostRelation
```

Stage 3 must define the Protocol-, Interface-, Plan-, relation-, and
composition-facing signatures and laws at sufficient resolution to prevent an
unqualified `equivalent`, `preserved`, `corresponds`, or `valid` claim. Later
owners retain their proof languages, derivations, quantitative theorems, and
domain-specific result schemas.

## 3. Stage 3 central question and ownership

The central question is:

> What exact Protocol, canonical PIR, Interface, Plan, relation, and
> composition contracts make all owned meanings, identities, observations,
> dependencies, and bridges explicit without using one subject in incompatible
> authority roles?

Stage 3 jointly owns five design surfaces:

1. Protocol semantics and their closed canonical PIR correspondence;
2. authentication, admission, identity, dependency, and capability predicates
   at the Protocol boundary;
3. the complete `ProtocolInterface` boundary and the necessary
   `ProverPlan` boundary over Protocol-owned obligations;
4. Relations ontology, ingress, optional artifact interpretation, and
   Protocol-at-Interface correspondence; and
5. Fresh-to-Fiat--Shamir construction and Protocol composition at their
   semantic boundaries.

Protocol/PIR and Relations must converge together. Interface fields shared by
Relations and endpoint projection are joint seams; they cannot be finalized
by either consumer alone. Plan fields shared by Protocol obligations, later
Analysis, projection, and realization must receive one explicit owner and one
declared read boundary.

## 4. Questions Stage 3 must resolve

### 4.1 Protocol and canonical PIR

Stage 3 must determine:

1. the exact closed grammar and static semantics of `InteractiveCore`,
   `ChallengeInterpretation`, `Protocol`, and canonical PIR;
2. canonical roles, semantic ports, event and occurrence namespaces, value
   kinds, checks, claims, reductions, terminals, routes, segments, policies,
   profiles, dependency references, and failure outcomes;
3. the representation of mandatory causal dependencies and the selected total
   observable schedule, including which order differences change identity;
4. the exact abstract endpoint and prover obligation vocabulary and total
   source-level obligation-closure predicate;
5. protected intrinsic effects and the conditions under which a named trace or
   independence relation permits reordering, deletion, duplication, or
   replacement;
6. the canonical semantic encoding preimages for Core, transcript
   construction, Protocol, Interface, and Plan identities, while keeping
   transport identities separate;
7. the physical canonical-form contract, allowed carrier trivia, and complete
   Protocol-to-canonical-PIR correspondence;
8. the information-loss frontier: which rejection-relevant distinctions must
   be checked before normalization and which nonsemantic source details may be
   erased; and
9. the minimal typed dependency closure and regime references retained by
   `AuthenticatedCanonicalProtocol` and `AdmittedProtocol`.

The package must compare plausible factorizations before selecting final
grammar structure. Current MLIR operations and C++ types are evidence and
feasibility constraints, not default semantic productions.

### 4.2 Authentication and admission

Stage 3 must allocate every predicate to exactly one boundary:

- canonical carrier/profile legality;
- semantic identity recomputation;
- dependency-preimage authentication and closure;
- whole-Core and whole-Protocol well-formedness;
- schedule, effect, challenge, claim-flow, terminal, and obligation closure;
- Interface formation and admission; and
- Plan formation and admission, plus the separate structural
  `PlanRealizes` relation.

For each predicate the package must state inputs, owner, outcome classes,
identity effect, capability effect, replay rule, residual trust, and whether
direct recomputation or a smaller checker is justified. A fused implementation
is allowed only if its public result preserves the logical distinctions.

### 4.3 `ProtocolInterface`

Stage 3 must define the complete Interface subject at the shared resolution
required by Relations and OIR, including:

1. its canonical identity preimage and exact dependency on `ProtocolId` and
   the Interface semantic regime;
2. stable references to canonical semantic ports, values, proof-event
   occurrences, checks, terminals, and role entry points;
3. external names, positions, containers, statement/proof packaging, and
   malformed-input or interface-refusal behavior;
4. the decoding/preservation condition for external value and proof encodings;
5. relation/application binding fields and their ownership split with
   Relations;
6. its admission predicate and narrow immutable exports for Relations and
   Stage 4B OIR; and
7. the exact rule that rejects any Interface field that changes semantic
   values, transcript-visible framing, proof-event order, challenge behavior,
   checks, claim routing, accepted language, or terminal behavior.

The result must permit several Interfaces over one Protocol while making
Interface-sensitive substitution impossible without the exact
`ProtocolInterfaceId`.

### 4.4 `ProverPlan`

Stage 3 must complete the Plan subject only to the resolution required to close
Protocol-owned abstract prover obligations and later consumer seams. It must
determine:

1. canonical obligation and occurrence references;
2. the Plan identity preimage and exact dependency on `ProtocolId` and the
   Plan semantic regime;
3. construction or witness DAGs, explicit private dependencies, typed holes,
   supplier requirements, and plan-local algorithmic choices;
4. Plan formation and admission as Plan-owned predicates, followed by a
   separate total structural `PlanRealizes` coverage judgment over the exact
   admitted Protocol and Plan;
5. the semantic classes and constraints by which Stage 4B can decide which Plan
   facts change canonical prover OIR and therefore enter projection explicitly,
   and which belong only below OIR in realization, without Stage 3 prematurely
   fixing every field's placement;
6. the narrow exports required by later Analysis, OIR, and Realization; and
7. rejection of every purported Plan whose substitution changes a
   verifier-visible message, distribution, transcript action, proof ABI,
   check, accepted language, or terminal outcome.

Honest-prover completeness and cost remain later qualified judgments; Plan
admission must not claim either.

### 4.5 Relations

Stage 3 must establish an ontology and contract set for:

- relation definition and semantic identity;
- relation-domain interface and its final name;
- public instance, private witness, and relation instance;
- committed-object declarations, opaque Protocol anchors, and grounding;
- pre-canonical authoring ingress;
- optional relation-artifact identity and byte interpretation; and
- post-admission Protocol-at-Interface correspondence.

The package must answer:

1. which declaration dependencies and regimes enter each identity and
   admission basis;
2. whether relation semantic identity, relation-interface identity, and
   relation-artifact identity are separate dependent identities or another
   explicit factorization;
3. which facts a narrow admitted Protocol/Interface view exports to Relations;
4. how public-instance and witness mappings bind canonical ports and
   occurrences without letting Relations redefine Protocol meaning;
5. whether `RelationArtifactObservation` remains process-local or becomes an
   identified durable observation, justified by a named consumer;
6. the exact inputs and outcomes of
   `RelationCorrespondsAtInterface`: the admitted Protocol, exact admitted
   Protocol Interface, admitted relation-domain interface, optional
   `RelationArtifactObservation`, and correspondence regime, including
   affirmative, negative, unsupported, and cannot-answer results; and
7. the difference between interface correspondence, relation satisfaction,
   witness validity, and any later property judgment.

### 4.6 Fresh-to-Fiat--Shamir boundary

Stage 3 must define:

1. deterministic construction of a new Fiat--Shamir Protocol from an admitted
   fresh-coin Protocol and an exact transcript construction;
2. the source/target Core, Protocol, event-occurrence, challenge-occurrence,
   and transcript-prefix maps;
3. typed framing, codecs, domain separation, absorb/squeeze behavior, sampling,
   aborts, and composition-context binding owned by the construction;
4. the subjects, direction, theorem/model-basis boundary, and non-claims of
   `FSCompile`; and
5. the exact export that later Analysis needs for property-specific
   `PropertyTransport` judgments.

Construction and target admission must remain available when the theorem basis
is absent. In that case `FSCompile` or a property transport may be unsupported
or cannot-answer; the target Protocol does not become malformed by backflow.
Stage 3 does not prove cryptographic properties or select their quantitative
bounds.

### 4.7 Protocol composition and link

Stage 3 must define semantic composition as construction of one new Core. Its
contract must settle:

- tagged child-occurrence namespaces, including repeated use of one child;
- child-to-composite port, event, obligation, and claim face maps;
- causal seams and one selected total interleaving;
- independent, shared, or derived challenge policy;
- transcript and construction domain separation;
- check, failure, refusal, and terminal propagation;
- dependency and obligation closure;
- whether canonical identity commits to inlined child semantics, explicit
  child references, or another complete nonambient encoding; and
- the exact distinction between authoring link and admitted semantic
  composition.

Composition is not textual concatenation, MLIR graph union, current static
link behavior by inheritance, or chaining of transition/certificate records.
Endpoint descent, recursion, IVC, and property transport over composites remain
explicit later relations.

### 4.8 Relation laws and checking placement

For every Stage 3-owned relation, the package must state:

```text
source and target subjects
all immutable read inputs and semantic regimes
direction and quantification
protected observers and effect domain
assumptions and dependency preimages
identity and capability effects
affirmative, negative, unsupported, cannot-answer, and refusal behavior
composition law or explicit absence of one
replay and serialization behavior
owner, checker authority, residual trust, and relying consumer
```

Stage 3 must decide which checks use direct recomputation, which genuinely
benefit from a smaller relation-specific validator, which remain trusted, and
which have no durable independent consumer. It must not introduce a common
certificate envelope for table symmetry.

## 5. Required research method

Stage 3 must apply the common design-research method, not jump directly from
current types to a target schema:

1. **Bounded intake:** verify this gate against the accepted Stage 1 and Stage
   2 convergence records. Record a formal reopening before changing an
   inherited decision.
2. **Reconstruction:** trace current normative specifications, architecture,
   implementation, tests, and examples for Protocol grammar, relation ingress,
   committed objects, linking, Interface-like labels, Plan-like routes,
   Fiat--Shamir behavior, and composition. Code remains correspondence
   evidence, not semantic authority.
3. **Generative research:** derive zkc-specific design forces; study primary
   protocol-semantics, IR, proof-system, relation, Fiat--Shamir, and composition
   work; and instantiate multiple materially different architectures at equal
   resolution.
4. **Evaluation:** test each viable architecture against current admitted
   cases, future capability opportunities, counterexamples, and the scenarios
   in Section 8. Passing existing cases does not end the search.
5. **Integration:** review every shared Interface and Plan field from both its
   producer and consumer sides, audit closure and authority cycles, and make
   Protocol/PIR and Relations converge as one package.
6. **Convergence:** select, reject, or defer candidates with explicit evidence,
   falsifiers, reversal triggers, and non-claims. Promote only reviewed results
   into durable owners.

Feasibility prototypes are allowed only when a design question cannot be
answered from specifications, theory, or existing correspondence evidence.
They are non-authoritative, isolated from production behavior, and reported as
experiments rather than implementation.

## 6. Required deliverables

Stage 3 must produce all of the following before it can exit:

1. a bounded Stage 3 charter and research-package index;
2. a current Protocol/PIR-and-Relations reconstruction with exact normative
   owners and implementation-correspondence evidence;
3. a design-force and opportunity ledger derived independently of current
   representation choices;
4. primary-source external case studies and at least four equal-resolution
   target architecture candidates;
5. a selected complete Protocol semantic model and closed canonical PIR
   contract;
6. a Protocol-to-canonical-PIR correspondence and information-loss ledger;
7. a canonical identity, regime, dependency, and occurrence-reference ledger;
8. an authentication-versus-admission predicate matrix with outcome,
   capability, replay, checker, and residual-trust columns;
9. a complete `ProtocolInterface` boundary, identity, admission contract, and
   field-ownership/export ledger;
10. a bounded `ProverPlan` boundary, identity, admission and `PlanRealizes`
    contract, obligation ledger, and projection-versus-realization semantic
    classes, constraints, and reader-requirement ledger for Stage 4B;
11. a Relations ontology, identity/dependency ledger, ingress contract,
    optional artifact-interpretation contract, and exact
    Protocol-at-Interface correspondence contract;
12. an exact Fresh-to-Fiat--Shamir construction contract, occurrence/prefix
    maps, and bounded `FSCompile` handoff;
13. a Protocol composition algebra and authoring-link distinction;
14. a named-relation matrix covering signatures, observers, assumptions,
    outcomes, composition, checking, and non-claims at the Stage 3 boundary;
15. protected-observation, effect, closure/read-set, semantic-regime, identity,
    capability, and refusal matrices across the selected design;
16. scenario, opportunity, adversarial, and candidate-falsification results;
17. a current-to-target correspondence and gap inventory that does not become
    an implementation migration plan;
18. a convergence record with accepted decisions, rejected alternatives,
    deliberate deferrals, exact owners, and reopening conditions;
19. durable promotion and temporary-note absorption records; and
20. separate bounded entry contracts for Stage 4A Analysis/Compiler and Stage
    4B OIR/Realization, plus any updated seam ledger shared by both branches.

Names in this list describe semantic content. The package may organize the
working documents differently if every deliverable remains independently
reviewable and traceable.

## 7. Exit criteria and later-stage seams

### 7.1 Stage 3 exit criteria

Stage 3 exits only when all of the following are true:

1. A clean-room reader can reconstruct Protocol, canonical PIR, Interface,
   Plan, relation, and composition meanings without current C++ class names,
   retained carrier labels, or broad registry objects.
2. Every identity-bearing field has exactly one semantic owner, typed regime,
   canonical preimage, and substitution rule.
3. Every Stage 3 result is functionally closed over named immutable inputs;
   substitution tests reveal no carrier, resolver, compiler, theorem,
   registry, or policy ambient read.
4. Physical canonical authentication and whole-Protocol admission have
   complete, noncircular predicate assignments and distinct outcomes.
5. The canonical PIR graph is bijective with the selected Protocol semantic
   encoding modulo explicitly allowed carrier trivia, and every irreversible
   erasure is preceded by the check whose refusal depends on it.
6. Core owns one total observable schedule, protected effects, exact failure
   classes, and complete abstract endpoint and prover obligations.
7. Interface admission proves only preservation of already-fixed Protocol
   meaning, and every Interface-sensitive consumer cites the exact Interface.
8. Plan admission proves only the Plan-owned predicate, while the separate
   `PlanRealizes` judgment proves only structural obligation coverage. Stage 3
   exports Plan semantic classes, placement constraints, and reader
   requirements sufficient for Stage 4B to assign each field to projection or
   realization; no Plan changes verifier-visible semantics.
9. Relation ingress, optional artifact interpretation, correspondence,
   satisfaction, and property judgments have distinct subjects, authorities,
   outcomes, and non-claims.
10. Fresh-to-Fiat--Shamir subject construction, `FSCompile`, and each later
    property transport are noncollapsible, with complete occurrence and
    transcript-prefix maps at their shared seam.
11. Protocol composition constructs and admits one new Core with explicit
    occurrence, schedule, challenge, dependency, obligation, and failure
    closure; no result relies on graph union or transition adjacency.
12. Every named relation used by a later stage has a direction, observer set,
    assumptions, outcome space, composition rule or non-rule, checker owner,
    and residual-trust statement.
13. All required scenarios pass without weakening a fixed Stage 1 or Stage 2
    boundary, and every unresolved falsifier has either been closed or assigned
    to a later owner without hiding a Stage 3 semantic dependency.
14. Stage 4A and Stage 4B receive stable, mutually consistent entry contracts
    and narrow views rather than duplicate Protocol models.
15. Reviewed conclusions are promoted to durable owners, rejected and deferred
    alternatives retain durable reversal triggers, temporary routes are
    accounted for, and documentation validation succeeds.

Stage 4 does not begin merely because a grammar draft exists. Both the
Protocol/PIR and Relations sides, including their Interface and Plan seams,
must satisfy the same exit review.

### 7.2 Stage 4A Analysis and Compiler seam

Stage 3 exports to Stage 4A:

- authenticated narrow Protocol, Interface, Plan, relation, occurrence,
  obligation, and composition facts with exact adequacy claims;
- the semantic subject selection rule for Protocol-only, Interface-sensitive,
  and Plan-sensitive questions;
- named relation signatures, protected observer sets, directions, assumptions,
  and composition requirements;
- the checked-successor lifecycle skeleton—proposal, target authentication,
  target admission, then exact predecessor/target relation checking—and the
  distinction between independent target admission, relation validation,
  property constraints, selection, and consumer decision;
- the Fresh-to-Fiat--Shamir construction maps and bounded `FSCompile` theorem
  interface; and
- the rule that `PropertyTransport` is property-specific and Analysis-owned.

Stage 3 does not define Analysis question, derivation, judgment, theorem,
solver, quantitative-bound, property-transport, compiler-search, comparison-
domain, objective, score, selection, or decision schemas. It does not claim
that structural correspondence preserves soundness, knowledge, completeness,
zero knowledge, or cost.

### 7.3 Stage 4B OIR and Realization seam

Stage 3 exports to Stage 4B:

- exact admitted Protocol and Interface views for endpoint projection;
- canonical event, occurrence, port, failure, and source-obligation references;
- the tagged `InterfaceOnly` versus `InterfaceAndPlan` input distinction;
- Plan semantic classes, placement constraints, and reader requirements from
  which Stage 4B decides which exact facts are projection-visible or
  realization-only;
- the rule that `LocalOirValid` and source-relative `ProjectionCorrect` are
  distinct and that source-free coverage is unknown;
- the rule that target-specific refusal does not invalidate admitted Protocol;
  and
- the identity, capability, outcome, and no-ambient-read constraints inherited
  from Stage 2.

Stage 3 does not define OIR grammar, OIR identity bytes, projection algorithms,
source maps, supplier schemas, realization relations, backend grades,
deployment, invocation, runtime effects, or observation records.

### 7.4 Stage 5, Stage 6, Foundation, and Project seams

- Stage 5 may synthesize capability and composition mechanisms only after the
  two Stage 4 branches demonstrate genuine commonality. It may not replace
  Stage 3 semantic ownership with a universal framework retroactively.
- Stage 6 receives typed semantic subjects, occurrence/result references, and
  exact non-claims. Evidence, appraisal, and reliance may cite them but never
  redefine or strengthen their semantic meaning.
- `foundation/` may receive only mechanisms demonstrated identical across
  owners. `project/` may own descriptive schemas, authority maps, and program
  gates, not domain relation truth.

## 8. Required scenarios and validation

The selected design must pass at least the following integrated scenarios.
Each scenario must record declared inputs, expected subject and authority
states, exact result relation, qualified outcomes, identity and capability
effects, and a falsifier.

| ID | Scenario | Required result |
|---|---|---|
| `P1` | Two distinct authoring inputs normalize to one semantic Protocol; a third differs only in a protected observation | The first two authenticate to the same semantic identity; the third is refused or receives a different identity before erasure |
| `P2` | Canonical bytes decode under the same and then a different semantic regime | Same-regime authentication may reconstruct identity; regime substitution never preserves identity by byte equality |
| `P3` | Authentication succeeds while a whole-Protocol closure predicate fails, and another candidate fails physical canonicality before admission | The failures remain assigned to distinct boundaries; neither result mints admission authority |
| `I1` | One Protocol has two Interfaces differing in external names or lossless packaging | Protocol-only results are reusable; correspondence and projection consume the exact respective Interface IDs |
| `I2` | An Interface decoder restricts semantic values, injects a semantic default, or changes transcript-visible proof bytes | The candidate is rejected as an Interface and is routed to a policy, adapter, wrapper Protocol, or new Protocol subject |
| `L1` | A relation interface is admitted without artifact bytes; matching and conflicting bytes arrive later | Artifact interpretation is separate; agreement does not prove relation meaning, while conflict yields a successful negative correspondence rather than malformed Protocol |
| `L2` | A well-formed Protocol/Interface and relation subject fail one correspondence field | The bridge returns the exact negative result and preserves unaffected facts; refusal and cannot-answer remain distinct |
| `L3` | Opaque committed objects are declared and later grounded through relation material | Grounding cites exact declarations, regimes, Interface bindings, and adapter authority without changing Protocol identity or proving witness satisfaction |
| `R1` | One Protocol has two Plans and two supplier strategies | Verifier-level meaning is unchanged; every Plan-sensitive result cites the exact Plan; each field appears at projection or realization, never ambiently both |
| `F1` | Construct and admit a Fiat--Shamir Protocol, then remove the theorem/model basis | The target remains admitted; `FSCompile` and property transport are unavailable at their own boundaries |
| `F2` | Request two property transports over one FS construction with different assumptions or losses | No global `FS-valid` result discharges both; each later judgment retains its exact property and basis |
| `C1` | Compose two children, including two occurrences of the same child, under two candidate interleavings | Tagged occurrences remain distinct; the chosen schedule, challenge policy, seams, failures, dependencies, and obligations determine a new Core identity |
| `C2` | Attempt to use static linking, graph union, or certificate adjacency as semantic composition | The attempt is refused or remains an authoring proposal until the complete Core-construction contract is checked |
| `T1` | Validate a structural Protocol relation without a property-transport rule | The structural result succeeds within scope; no property conclusion is inferred |
| `S1` | Serialize Protocol, Interface, Plan, and relation-result material into another process | Semantic subjects are re-authenticated/re-admitted and durable results rechecked; no local capability crosses by assertion |
| `O1` | Give a later endpoint consumer OIR but no source or source-bound projection evidence | Target-local validity may succeed; source coverage is `CannotAnswer` or unknown |

The package must also run these cross-cutting probes:

- hold declared inputs fixed and vary every suspected hidden resolver, carrier,
  theorem, compiler, registry, and policy input;
- vary transport while preserving semantics, then vary semantic regime while
  preserving transport;
- test successful negative, unsupported, cannot-answer, refusal, malformed,
  and checker-failure outcomes independently;
- copy, reopen, mutate, serialize, and cross an FFI or process boundary with
  each capability family;
- attempt relation, identity, capability, composition, and property laundering;
- test unknown future canonical operations and dependency kinds for fail-closed
  behavior; and
- search for at least one capability unlocked by a non-current architecture,
  not only failures of the current one.

Validation must include:

1. authority-map and normative-owner review;
2. current implementation and test correspondence tracing, clearly labeled as
   correspondence rather than semantic proof;
3. field-level closure, regime, identity, observer/effect, outcome, capability,
   checker, and consumer matrices;
4. independent candidate comparison and adversarial falsification;
5. explicit review from every producer and consumer at shared Interface and
   Plan seams;
6. documentation route, link, heading, code-fence, and whitespace validation;
   and
7. test or model execution only when the package actually creates a bounded
   feasibility artifact, with the result reported at its true evidence grade.

## 9. Forbidden collapses

Stage 3 fails its gate if it makes any of these collapses:

```text
Protocol semantics              == MLIR syntax, bytes, or tool behavior
authoring proposal               == canonical Protocol
canonical authentication        == whole-Protocol admission
semantic identity               == transport digest or process authority
serialized admitted marker      == live admission capability
Protocol                         == ProtocolInterface
Protocol                         == ProverPlan
Interface decoding              == permission to change Protocol meaning
Plan structural coverage        == honest-prover completeness or cost
relation definition             == relation artifact bytes
artifact interpretation         == relation truth or witness satisfaction
relation correspondence         == Protocol admission or property judgment
Fresh-to-FS construction        == FSCompile
FSCompile                       == property-specific PropertyTransport
target admission                == checked predecessor/successor relation
structural correspondence       == security-property preservation
Protocol composition            == graph union, link, or transition chaining
negative judgment               == checker failure or refusal
unsupported or cannot-answer    == semantic refutation
source-free target validity     == source-relative coverage
provenance, signature, or digest == proof of the cited semantic predicate
producer success                == independent checking
evidence or appraisal           == semantic truth or use authorization
```

Shared data structures or implementation helpers are permitted only when the
semantic owners, result types, authority, and lifetimes remain explicit.

## 10. Explicit non-goals

Stage 3 does not:

- migrate, refactor, or implement the target architecture;
- select final C++, Rust, MLIR, JSON, filesystem, package, or API names merely
  to mirror the current checkout;
- define a second complete carrier-neutral Protocol package, compatibility
  dialect, historical upgrade system, or retention promise without reopening
  the Stage 1 product boundary;
- introduce a universal transition record, fact root, certificate envelope,
  capability type, global error enum, or general proof object;
- complete Analysis, Compiler, OIR, Realization, deployment, invocation,
  Evidence, appraisal, reliance, or roadmap schemas;
- select a theorem prover, solver, cryptographic proof system, hash function,
  signature scheme, backend, build system, or deployment topology;
- prove relation satisfaction, witness validity, soundness, knowledge,
  completeness, zero knowledge, Fiat--Shamir security, compiler correctness,
  projection correctness, realization correspondence, or evidence sufficiency;
- infer implementation conformance, production readiness, portability, or
  independent verification from static inspection or existing tests; or
- design around current migration cost. Current implementation constraints
  matter only as feasibility evidence after the ideal semantic alternatives
  have been compared.

## 11. Reopening conditions and procedure

### 11.1 Reopen a Stage 1 input only when

- normalization must decide general behavioral equivalence rather than a finite
  declared authoring quotient;
- rejection-relevant authoring distinctions cannot be checked before canonical
  normalization erases them;
- the supposedly closed canonical PIR grows into another optimizing workbench,
  or its admission checker imports most compiler or plugin machinery;
- the rich workbench and canonical form prove semantically identical and no
  named consumer benefits from their separation;
- a complete Protocol cannot be expressed without moving verifier-visible
  behavior into Interface or Plan;
- the closed canonical PIR level cannot represent a required semantic field
  without retaining arbitrary authoring form, or is not meaningfully smaller
  or more independently admissible than the workbench;
- total schedule ownership in Core contradicts a credible required protocol
  class rather than an upstream scheduling convenience;
- a named independent full-Protocol consumer requires a carrier-neutral
  semantic package under a concrete trust, release, and retention contract;
- multiple committed full-Protocol consumers, independent release cycles, a
  non-MLIR deployment constraint, a formal extraction boundary, or long-lived
  artifacts require the compatibility contract deferred by Stage 1;
- purpose-specific views collectively recreate a complete second Protocol
  schema;
- an Interface or Plan substitution changes a result classified as
  Protocol-only; or
- the selected identity factorization cannot satisfy its own substitution and
  cross-regime laws.

### 11.2 Reopen a Stage 2 input only when

- a declared contract remains nonfunctional because of an unavoidable hidden
  read;
- two or more relation families demonstrate identical semantics, authority,
  lifetime, composition, and consumer needs sufficient to justify shared
  executable machinery;
- a named heterogeneous cross-process consumer requires a portable transition
  graph or result that domain adapters cannot serve;
- a supposedly smaller validator duplicates its producer, needs unavailable
  private state, or has no relying consumer;
- bounded re-admission or direct checking is unavailable or uneconomic for a
  named consumer with a smaller stable claim checker;
- process-local capability mechanics cannot enforce the promised boundary or
  a legitimate consumer cannot reconstruct authority;
- no exact placement of an Interface or Plan field closes both its producer
  and consumer contracts; or
- an inherited pure relation has observable effects or an effectful operation
  lacks a meaningful completion and partial-failure frontier.

### 11.3 Reopen a Stage 3 decision when

- a new credible protocol, relation, committed-object, composition, or
  Fiat--Shamir case defeats the selected grammar or relation laws;
- two legal canonical representations under one regime denote the same
  identity without an explicitly allowed carrier equivalence;
- a required rejection distinction is lost before the check that depends on
  it;
- relation correspondence cannot be stated over the exported Protocol and
  Interface views without importing hidden carrier authority;
- composition cannot close schedule, challenge, dependency, obligation,
  terminal, or failure semantics; or
- a later Stage 4 consumer demonstrates that the exported seam omits a
  semantic input that Stage 3 owns.

Every reopening record must name:

```text
the contradicted decision and exact falsifying evidence
the affected semantic subjects and regimes
the authority and identity consequences
the relation, observer, capability, and outcome consequences
at least one equal-resolution alternative
the affected producers and consumers
the new compatibility or wire commitment, if any
the downstream contracts that must be invalidated or re-reviewed
```

No reopening may be implemented as an ambient field, generic metadata,
unchecked exception, widened `valid` result, or silent edit to a downstream
schema.

## 12. Activation record

The explicitly authorized Stage 3.0 activation completed these requirements:

1. verify that Stage 2 has a reviewed convergence record, current-to-target
   gap inventory, durable decision destinations, and completed absorption
   record;
2. reconcile this file against the selected durable Stage 2 architecture and
   the complete temporary handoff evidence;
3. publish a Stage 3 charter and working inventory using the research sequence
   in Section 5;
4. mark Stage 3 active in the single design program and relevant navigation;
   and
5. begin with bounded intake, leaving reconstruction and final schema drafting
   unopened.

The completed [Stage 3 charter](../stage-3-protocol-and-relations/charter.md) and
[package index](../stage-3-protocol-and-relations/README.md) record the
resulting boundary and subsequent closure. No section of this contract is a
normative design decision, implementation request, migration instruction, or
independent claim that a later deliverable exists.
