# Stage 2 candidate transition frameworks

> **Document kind:** Temporary architecture research note
> **Document state:** Divergent-phase candidate portfolio
> **Authority:** None. This note instantiates hypotheses for Stage 2 comparison.
> It does not define a transition, introduce a runtime artifact, select a
> checker model, or alter any Stage 1 subject or identity decision.
> **Disposition:** Re-evaluate every candidate against the reconstructed
> current transition catalog, scenario results, and cross-domain owner review;
> absorb only reviewed conclusions into durable owners and then delete this
> note.

## 1. Purpose

Stage 1 selected the semantic subjects and the canonical Protocol boundary.
Stage 2 must now decide how zkc describes, implements, checks, composes, and—
only where justified—persists the transitions between those subjects.

The shared field list in the
[Stage 2 charter](../stage-2-transition-and-bridge-charter.md) does not answer
that architectural question. Similar fields can support several substantially
different designs:

1. domain-owned typed contracts documented through one descriptive schema;
2. a universal typed transition algebra with an optional common artifact;
3. a capability-centric lifecycle with separately owned semantic bridges; or
4. producer proposals checked by edge-specific validators and, where needed,
   certificates.

This note develops the strongest coherent version of each family at equal
resolution. It deliberately does **not** choose a winner. Stage 2 has not yet
reconstructed the complete current transition catalog, implementation read
sets, existing replay consumers, effect boundaries, or validator cost. A
selection made before that evidence would turn architectural taste into a
false conclusion.

The candidates are centers of gravity, not necessarily four indivisible
products. Ownership, capability, validation, and persistence are partially
orthogonal choices. A later synthesis may use different mechanisms for
different transition families, but it must do so under explicit selection
rules rather than accidental inconsistency.

## 2. Fixed inputs and comparison boundary

Every candidate inherits the selected
[Protocol IR architecture](../../project/protocol-ir-architecture.md). The
portfolio does not reopen:

- language-independent Protocol semantics with MLIR as the v0 structural
  carrier;
- the rich authoring workbench and distinct closed canonical PIR level;
- `InteractiveCore`, `ChallengeInterpretation`, `Protocol`,
  `ProtocolInterface`, and `ProverPlan` as distinct semantic subjects;
- regime-qualified `CoreId`, `ConstructionId`, `ProtocolId`,
  `ProtocolInterfaceId`, and `ProverPlanId` dependencies;
- the total observable schedule in `InteractiveCore`;
- immutable process-local `AdmittedProtocol` authority;
- serialization ending process-local capability continuity;
- protected `TRANSCRIPT`, `WIRE`, `PUBLIC`, `CHECK`, `ARTIFACT`, `CLAIM`, and
  `TERMINAL` observations;
- named relations such as `RepresentationEq`, `ProtocolEq`, `TraceRefines`,
  `FSCompile`, `ProjectionCorrect`, `PlanRealizes`, and `PropertyTransport`;
- target-specific projection refusal and the information limit on source-free
  OIR coverage; or
- the absence of a complete portable Protocol package and universal fact root
  in v0.

A candidate that needs to move an interface field into `ProtocolId`, serialize
an admission capability, treat `FSCompile` as equality, or infer source
coverage from an OIR alone contradicts the entry contract. That is a hard
failure, not a tradeoff.

This portfolio compares the architecture of transitions and bridges. It does
not yet choose:

- the exact transition catalog or public names;
- concrete C++ or MLIR APIs;
- an identity encoding or wire grammar for transition evidence;
- the complete relation, analysis, compiler, OIR, realization, or evidence
  schemas;
- a theorem prover or certificate system;
- implementation migration order; or
- whether any particular transition deserves a durable artifact.

## 3. Common comparison model

### 3.1 A descriptive contract, not yet a universal type

All candidates are described with the same review tuple:

```text
TransitionContract =
  stable name and family
  source subjects and authority state
  identified auxiliary inputs
  complete read and dependency closure
  binding time and semantic regime
  proposer or procedure authority
  checker or bridge authority
  result category and target owner
  exact claimed relation
  identity effects
  capability effects
  protected observations and operational effects
  success, negative result, refusal, and failure variants
  replay and serialization behavior
  relying consumer and policy
  residual trust and reversal conditions
```

This tuple is a comparison instrument. Its existence does not imply that zkc
should implement or serialize a `TransitionContract` sum type. Candidate A
keeps it descriptive; Candidate B promotes a typed form of it into shared
architecture; Candidates C and D share only selected mechanisms.

### 3.2 Four things that must remain distinct

Every framework must keep these layers separate:

1. **Semantic subjects.** Protocol, Interface, ProverPlan, OIR, relation,
   analysis judgment, realization, evidence, and relying decision retain their
   own definitions and identities.
2. **Attempts or procedures.** A normalizer, compiler search, projector,
   endpoint invocation, or evidence appraiser is an action. Running it does
   not make its claim true by definition.
3. **Checked relations.** Admission, preservation, correspondence, coverage,
   realization, and appraisal each establish a specifically named result over
   exact inputs.
4. **Authority to use a result.** An in-process capability or relying policy
   can authorize an operation without becoming part of semantic identity or a
   portable theorem.

A common framework that collapses any two of these is not strengthened by
uniformity; it has erased an authority boundary.

### 3.3 Outcome categories

The candidates must express at least:

```text
Success with a subject, capability, checked relation, judgment, or observation
Success with a negative judgment
Malformed representation
Semantic inadmissibility
Unsupported construct, regime, target, or analysis
Claim or identity mismatch
Illegal transformation candidate
Missing authority or dependency preimage
Target or supplier refusal
Operational failure before effects
Operational failure after partial effects
Appraisal rejection
Reliance denial
```

`false` returned by a successful analysis is not a refused analysis. A target
that cannot project one admitted Protocol does not invalidate that Protocol.
An invocation failure cannot flow backward into Protocol or OIR meaning.

### 3.4 Replay classes

“Replay” is not one property. The comparison distinguishes:

- **deterministic recomputation:** repeat the procedure from exact inputs;
- **independent validation:** check a proposed result without repeating its
  search or construction strategy;
- **certificate verification:** check a durable, claim-scoped witness under a
  named checker regime;
- **re-authentication:** decode serialized subjects and reconstruct a new
  process-local capability;
- **observational reproduction:** attempt another execution under a named
  environment without asserting identical effects; and
- **non-replayable attribution:** authenticate that an effect occurred without
  claiming it can be reproduced.

Any candidate that advertises “replay” must state which of these it supports.

### 3.5 Composition classes

The comparison also separates:

- procedural sequencing, where the output authority of one step satisfies the
  input precondition of another;
- mathematical relation composition, which requires an explicit law for the
  two named relations;
- certificate chaining, which preserves only the conjunction or composed
  claim actually checked;
- semantic Protocol composition, which constructs a new `InteractiveCore` and
  is not transition chaining; and
- operational sequencing, which needs causal, effect, retry, and partial-
  failure semantics rather than pure arrow composition.

No framework receives compositionality credit merely because it can draw two
arrows next to each other.

## 4. Candidate A — domain-owned typed contracts with a shared schema

### 4.1 Thesis

Each domain owns concrete typed operations and results for the transitions it
defines or bridges. The project layer owns only the descriptive schema,
catalog, cross-domain ownership rules, and global invariants. There is no
universal runtime transition value, transition identity, or serialized
transition record.

```text
shared descriptive schema and catalog
        |
        +--> PIR lifecycle contracts owned by PIR
        +--> relation correspondence contracts owned by Relations
        +--> analysis derivations owned by Analysis
        +--> checked successor contracts owned by Compiler
        +--> projection contracts owned jointly at the PIR/OIR seam
        +--> binding and execution contracts owned by Realization
        `--> appraisal and reliance contracts owned by Evidence/consumer
```

“Typed” means that a concrete contract names exact source, auxiliary inputs,
result, relation, and outcomes. It does not mean every contract implements one
generic interface.

### 4.2 Lifecycle and bridge shape

The lifecycle may expose distinct operations such as:

```text
authenticate(candidate, regime, dependency_closure)
  -> AuthenticatedCanonicalProtocol | AuthenticationRefusal

admit(authenticated, admission_policy)
  -> AdmittedProtocol | AdmissionRefusal

project(admitted_protocol, protocol_interface, endpoint_role, config)
  -> ProjectedEndpointAndCoverage | ProjectionRefusal

derive_property(admitted_protocol, question, assumptions)
  -> PositiveJudgment | NegativeJudgment | Unsupported | Refusal
```

These signatures are illustrative, not selected Stage 2 contracts. The
important property is that each result vocabulary remains owned by the domain
that knows its semantics. A shared catalog can render or lint the contracts,
but it cannot execute them or infer one relation from another.

### 4.3 Authority

- The source owner defines source formation and exported facts.
- The concrete bridge owner defines the named relation and checker.
- The target owner defines target meaning and identity.
- A consumer separately decides whether the checked result is sufficient.
- The project-owned schema can require that these roles be named, but it has no
  authority to replace them.

This model makes authority localization explicit. Its main risk is procedural:
domain owners can fill the same descriptive fields with subtly incompatible
meanings unless cross-domain review enforces shared invariants.

### 4.4 Identity

Semantic identity remains entirely domain-owned. A transition contract can
state which identities it consumes, preserves, cites, or mints, but there is
normally no `TransitionId`.

Durable outputs such as a property judgment or OIR receive identities only if
their owning domain and actual consumers require them. Procedure version,
compiler configuration, and checker regime are typed inputs where they affect
the result; they are not silently folded into a universal provenance key.

### 4.5 Composition and replay

Procedural sequencing is expressed by matching concrete input and result
types. Mathematical composition is defined per relation family. For example,
`RepresentationEq` may have transitivity, while `FSCompile` followed by
`ProjectionCorrect` needs a separately stated theorem and cannot inherit a
generic transitivity rule.

Replay is also per edge. Cheap deterministic checks may be recomputed; a
complex bridge may define a local certificate; a process-local paired
capability may deliberately have no serialized replay form. Cross-process
uniform replay tooling requires adapters over the domain contracts.

### 4.6 Extensibility and diagnostics

New domains and relation families can add contracts without changing a central
runtime schema. They can expose exact domain-specific diagnostic trees,
counterexample paths, unsatisfied obligations, or partial-effect reports.

The cost is weaker automatic tooling. Catalog consistency, pipeline
visualization, provenance queries, and generic orchestration require a common
metadata projection or hand-written adapters. Repeated concepts such as
dependency closures, regimes, and refusal categories can drift if extraction
and linting remain purely editorial.

### 4.7 Wire commitment

This candidate has the lowest inherent wire-format pressure. The shared schema
can remain Markdown, generated documentation, or an internal registry. A
durable artifact is introduced only by the domain whose consumer requires it.

Its failure mode is fragmented wire surfaces rather than one premature common
surface: several domains may independently invent incompatible certificate
headers, provenance conventions, or version rules.

### 4.8 What it makes possible

- exact domain language without a universal lowest common denominator;
- independent evolution of analysis, projection, realization, and evidence;
- selective use of recomputation, paired capability, certificate, or trusted
  procedure per edge; and
- postponement of public transition serialization until a real consumer
  exists.

### 4.9 Primary costs and candidate falsifiers

This candidate is weakened or falsified if reconstruction shows that:

- multiple independent consumers need a uniform, portable transition DAG and
  per-domain adapters merely recreate a hidden universal model;
- the same mathematical relation is duplicated with incompatible composition,
  regime, or refusal semantics across owners;
- end-to-end replay cannot be specified without interpreting undocumented
  domain-local state;
- shared diagnostics lose the exact point at which authority or identity
  changed; or
- enforcing catalog completeness requires a central executable type system in
  practice.

## 5. Candidate B — universal typed transition algebra and artifact

### 5.1 Thesis

zkc defines one typed algebra whose objects reference domain-owned subjects and
whose arrows represent proposed or checked transitions. Relation families,
effects, and outcome kinds remain indexed and domain-defined, but the common
architecture supplies construction, validation state, composition
registration, provenance, and replay structure.

The strongest coherent form is not an untyped `source -> target` log. It is
closer to:

```text
SubjectRef<SubjectKind, SemanticRegime, SubjectId>

TransitionClaim<SourceKinds, InputKinds, TargetKinds, RelationKind,
                EffectKind, CheckerRegime>

TransitionArtifact =
  exact typed subject references
  + identified auxiliary-input closure
  + relation-specific payload or witness
  + proposal and validator identities
  + qualified outcome
  + capability-neutral provenance
```

The universal layer imports subject and relation definitions; it does not own
their semantics. Unknown relation kinds fail closed.

### 5.2 Lifecycle and bridge shape

Every major boundary is represented as an indexed arrow or event:

```text
Authenticate : Candidate -> AuthenticatedCanonicalProtocol
Admit        : AuthenticatedCanonicalProtocol -> AdmittedProtocolAuthority
Transform    : AdmittedProtocol -> SuccessorProtocol
Project      : (AdmittedProtocol, ProtocolInterface, Role) -> OIR
Analyze      : (AdmittedProtocol, Question) -> Judgment
Invoke       : (RealizedEndpoint, InvocationInput) ~> Observation
Appraise     : (EvidenceSet, Policy) -> Assessment
```

The notation must distinguish pure claims from authority minting and effectful
events. `AdmittedProtocolAuthority` cannot be serialized inside an artifact;
the portable record can only cite the successful admission claim and inputs.
A new process still re-authenticates and re-admits before receiving authority.

### 5.3 Authority

The universal system records separate source-owner, target-owner,
proposer, validator, and relying-consumer roles. Validation dispatches to a
relation-specific checker registered by the relation owner. The algebra itself
may check type compatibility and composition eligibility, but cannot establish
`ProjectionCorrect`, `FSCompile`, or `PlanRealizes` generically.

This separation is a hard condition. If registration in the universal schema
implicitly grants semantic authority, the candidate becomes a central oracle
and violates the Stage 1 ownership model.

### 5.4 Identity

The candidate may introduce a transition-claim or artifact identity such as:

```text
TransitionArtifactId = H(
  transition-schema regime,
  exact source and auxiliary subject references,
  relation kind and claim parameters,
  exact result references,
  checker regime,
  relation-specific witness or receipt payload)
```

This identity authenticates the transition artifact only. It does not replace
`ProtocolId`, prove the claim by hashing it, preserve a capability, or make
different semantic regimes comparable.

Whether unsuccessful attempts receive identities is a separate observability
decision. Including search history or diagnostics in a claim identity would
make semantic cache keys unstable; excluding them requires a separate attempt
or trace identity.

### 5.5 Composition and replay

The algebra can provide generic composition only when relation owners register
an exact law:

```text
compose<R1, R2, R3>(a : R1(S, M), b : R2(M, T), law : R1 ; R2 => R3)
  -> R3(S, T)
```

Matching the intermediate ID is necessary but not sufficient. Some chains
yield only conjunction, provenance, or procedural sequencing. Operational
events need an effect trace and cannot use the pure-arrow unit and
associativity laws without additional semantics.

A portable artifact offers the strongest uniform replay surface: fetch exact
inputs, select the checker regime, validate the relation-specific payload, and
reconstruct local authority where allowed. A lighter subvariant keeps the
algebra in process and does not serialize artifacts. The two subvariants must
be evaluated separately because the durable form creates a compatibility and
retention promise that the in-process form does not.

### 5.6 Extensibility and diagnostics

Generic tooling can visualize provenance DAGs, query identity changes, enforce
declared read closures, and route validation by relation kind. Common outcome
and diagnostic envelopes can make pipelines easier to inspect.

However, adding a new relation, arity, effect kind, source family, or refusal
semantics may require changing the central schema or algebra. An escape hatch
with opaque payloads preserves syntactic extensibility at the cost of moving
semantic interoperability back into domain adapters. Universal diagnostics
can also collapse a useful proof obligation, unsupported feature, and target
refusal into one generic error path.

### 5.7 Wire commitment

This candidate has the highest premature wire-format risk in its portable
form. It creates a new durable product surface covering subject references,
relation discriminants, checker regimes, witnesses, outcomes, provenance, and
possibly effects before Stage 2 has established an independent consumer.

The in-process algebra has lower compatibility risk, but some of its strongest
claimed benefits—cross-process replay, independent validation, and portable
provenance—then disappear. The evaluation must not credit the lighter form
with benefits available only after the wire commitment.

### 5.8 What it makes possible

- uniform provenance and transition-graph inspection;
- generic orchestration and declared-read-set enforcement;
- explicit, typed composition registration;
- one replay protocol across independently implemented checkers; and
- possible caching or exchange of checked transition claims.

### 5.9 Primary costs and candidate falsifiers

This candidate is weakened or falsified if reconstruction shows that:

- most relation pairs have no useful common composition law beyond “ran after”;
- effectful, policy-qualified, and negative-judgment transitions require so
  many special cases that the algebra is only a tagged union;
- a new domain routinely requires central schema changes or opaque payloads;
- no concrete independent consumer needs portable transition artifacts;
- artifact verification needs essentially the complete producer or target
  implementation, defeating the bounded-checker claim;
- consumers begin treating an artifact ID or validator signature as semantic
  truth or process-local authority; or
- versioning the universal layer freezes unresolved Stage 3–6 semantics.

## 6. Candidate C — capability-centric lifecycle and relation-specific bridges

### 6.1 Thesis

The core lifecycle is modeled as a state-and-authority machine. Successful
checks mint narrow, unforgeable, immutable in-process capabilities. Possession
of a capability authorizes only the operations exposed by its type. Semantic
bridges remain separate, relation-specific checkers and paired result
capabilities rather than instances of one transition abstraction.

```text
AuthoringUnit
  -> CanonicalProtocolCandidate
  -> AuthenticatedCanonicalProtocol capability
  -> AdmittedProtocol capability
       +--> Analysis result capability
       +--> checked-successor pair capability
       +--> Protocol/OIR projection pair capability
       `--> Protocol/Plan realization capability

serialization
  -> subject bytes and references only
  -> re-authenticate and re-admit in the receiving process
```

The lifecycle spine is uniform because it has a shared authority pattern.
Cross-domain relations are not forced into that pattern merely because their
inputs are capabilities.

### 6.2 Lifecycle and bridge shape

Authentication and admission consume unauthoritative candidates and return
narrow authority objects. Reopening or mutation discards the capability.
Projection can return a paired capability that binds exact
`(ProtocolId, ProtocolInterfaceId, role, OirId, projection basis)`. Analysis
returns a typed judgment, including successful negative judgments. Compiler
transformation returns a newly authenticated and admitted successor plus an
edge-specific relation capability.

The capability may retain the immutable resolver closure or checker basis
needed for safe in-process consumption. That retained authority must remain an
explicit typed axis and read set; hiding ambient mutable registries behind an
opaque handle would make the model unauditable.

### 6.3 Authority

Authority is represented directly by construction control and narrow APIs:

- only the canonical authenticator can mint authenticated-candidate authority;
- only admission can mint `AdmittedProtocol`;
- only the projection checker can mint a paired source/OIR capability;
- a bridge capability authorizes consumers to rely on exactly its checked
  relation; and
- no raw carrier flag, copied object, or deserialized token can mint these
  capabilities.

This makes accidental misuse difficult in one address space. The residual
trust moves to capability constructors, type integrity, aliasing rules, and
the exact immutable environment captured by each object.

### 6.4 Identity

Capabilities do not normally receive semantic IDs. They carry or cite domain
subject IDs plus an admission basis, checker regime, retained environment, and
lifetime. Two capabilities over the same `ProtocolId` may be incomparable if
they were admitted under incompatible regimes or policies.

Persistent semantic results retain their owning-domain IDs. Ephemeral paired
capabilities need no durable bridge ID unless a cross-process consumer is
identified. This avoids contaminating semantic identity with process address,
constructor instance, or capability lifetime.

### 6.5 Composition and replay

Procedural composition follows capability types: a consumer cannot invoke
projection without an admitted source, and cannot realize an endpoint without
the required paired OIR and plan authority. Capability narrowing makes
authorized sequences explicit.

This does not prove mathematical composition. Two bridge capabilities compose
only when an edge-specific procedure checks the resulting relation and mints a
new capability. Protocol composition still constructs and admits a new Core.

Cross-process replay intentionally starts from serialized subjects and exact
dependencies, not from a serialized capability. The receiver reruns
authentication, admission, and any required bridge checker. Portable
certificates can be added exceptionally, but they are not the architecture's
default unit.

### 6.6 Extensibility and diagnostics

New capabilities and bridges can be added beside existing ones without a
central wire-schema revision. Narrow types make illegal consumer calls
difficult and permit domain-specific diagnostics at construction time.

The cost is capability proliferation. Many paired or narrowed handles can
become difficult to name, store, compare, and route. Diagnostics may disappear
after construction unless the capability retains a structured report, and
generic tools cannot inspect an opaque capability graph without a safe
descriptive projection. Language, FFI, plugin, and process boundaries also
need explicit degradation rules.

### 6.7 Wire commitment

This candidate has low default wire risk because authority is deliberately not
serializable. Persistent subjects use their domain formats, and the receiving
process checks them again.

Its corresponding risk is under-serving legitimate independent consumers. If
rechecking is expensive, requires unavailable private inputs, or depends on a
producer-only environment, refusing portable evidence may make reproducible
builds, remote checking, or artifact exchange impossible.

### 6.8 What it makes possible

- strong least-authority APIs for the in-process compiler pipeline;
- an explicit loss of authority at mutation, serialization, FFI, and process
  boundaries;
- small consumer surfaces over immutable admitted subjects;
- relation-specific semantics and diagnostics without a central transition
  language; and
- deferred persistence decisions until a concrete consumer appears.

### 6.9 Primary costs and candidate falsifiers

This candidate is weakened or falsified if reconstruction shows that:

- capability constructors consult undeclared mutable or ambient state;
- aliasing, concurrency, or retained resolver lifetime makes authority depend
  on process accident rather than exact immutable inputs;
- independent consumers need claims that cannot be economically rechecked;
- bridge results must cross process boundaries so frequently that ad hoc
  receipts recreate an undocumented certificate system;
- the number of pairwise capabilities makes orchestration and diagnostics less
  precise rather than more precise; or
- an FFI or serialized handle can accidentally preserve or counterfeit local
  admission authority.

## 7. Candidate D — producer proposal with per-edge validation and certificates

### 7.1 Thesis

Every nontrivial transition is split into a potentially complex producer and a
smaller, independently specified validator for that exact edge. The producer
may search, optimize, synthesize, or use heuristics. The validator consumes
the exact source, auxiliary inputs, proposed result, and relation-specific
witness, then emits a checked edge result. A durable certificate is produced
only when a named consumer needs independent replay or exchange.

```text
propose_E(source, inputs, producer_config)
  -> candidate_target + edge_witness + producer_trace

validate_E(source, inputs, candidate_target, edge_witness, checker_regime)
  -> checked edge capability | typed refusal

export_E(checked edge capability, certificate_profile)
  -> edge-specific certificate       # optional, never capability-preserving
```

The validator establishes relation `E`; it does not define source or target
semantics and does not authorize a relying use by itself.

### 7.2 Lifecycle and bridge shape

Authentication naturally fits this model: a carrier proposes canonical
content and declared IDs; the authenticator recomputes them. Compiler search
proposes a successor; a translation validator checks a named preservation,
refinement, or intentional-change contract. Projection proposes OIR plus a
coverage map; a checker validates `ProjectionCorrect` against Protocol,
Interface, role, and obligations. Prover planning proposes a construction DAG;
a validator checks `PlanRealizes`.

Not every edge is naturally a producer/validator pair. A cheap deterministic
analysis may simply be recomputed. An endpoint invocation is an effectful
occurrence: preflight validation can check readiness, while an observation
receipt can attribute effects, but neither independently validates that the
same execution can be replayed. The strongest coherent candidate therefore
allows a declared degenerate form—direct recomputation or trusted effectful
execution—rather than pretending every arrow has a compact witness.

### 7.3 Authority

- Producers have proposal authority only.
- Validators own only one named relation over exact inputs.
- Source and target owners remain authoritative for subject meaning.
- Certificate verifiers reproduce the validator claim under a named checker
  regime; a signature alone attests an issuer, not semantic correctness.
- Relying consumers separately select acceptable validators, regimes,
  assumptions, and claim strength.

This split reduces trust in complex search and synthesis code only when the
validator is genuinely smaller, independently specified, and closed over its
declared inputs.

### 7.4 Identity

The target's domain identity is computed independently of the proposal and
certificate. Producer search history, heuristic seed, and optimization trace
do not enter `ProtocolId` unless they change canonical Protocol meaning.

An edge-specific certificate may have its own identity over:

```text
certificate profile and regime
exact source, auxiliary input, and target identities
named relation and protected observers
validator identity or checker semantics
relation-specific witness
```

Certificate identity is provenance and replay identity, not target semantic
identity. Several certificates may support the same edge, and one target may
be related to one source under several incomparable claims.

### 7.5 Composition and replay

Validated edges form a provenance chain, but chain validity does not imply an
end-to-end semantic claim. A separate composition checker must establish the
desired relation or explicitly return only the conjunction of local claims.
Assumptions, quantitative deltas, protected observers, and intentional changes
must be transported rather than dropped.

This candidate can provide strong independent replay where the witness is
portable and the validator is available under the same semantic regime. It
cannot replay missing private inputs, unavailable dependency preimages, or
non-repeatable operational effects. Certificate expiry, supersession, checker
bugs, and regime migration require explicit policy.

### 7.6 Extensibility and diagnostics

Each new edge can define the witness and checker best suited to its
mathematics. Validators can produce precise counterexamples: unmatched
events, uncovered obligations, identity mismatches, invalid rewrites, failed
assumptions, or supplier incompatibilities.

The cost is a validator and potentially a certificate profile per edge.
Shared infrastructure may be extracted for subject references, dependency
bundles, and checker invocation, but a universal witness format would merely
recreate Candidate B. Too many validators can duplicate semantic logic,
version rules, diagnostics, and trust assumptions.

### 7.7 Wire commitment

The candidate's wire risk is selective rather than globally low. It avoids one
universal record, but every exported edge certificate is a durable contract.
Introducing certificates speculatively can freeze transition-specific witness
schemas before their consumers and relations stabilize.

A “certificate” retained only inside one process should normally remain a
checked capability or report. Durability is justified only by independent
replay, caching, exchange, trust separation, or retention requirements.

### 7.8 What it makes possible

- untrusted or heuristic search with a smaller semantic acceptance boundary;
- independent checking of compilation, projection, plan realization, and
  selected correspondence claims;
- precise source/target provenance without a universal transition IR;
- relation-specific counterexamples and proof obligations; and
- optional proof-carrying exchange at concrete consumer boundaries.

### 7.9 Primary costs and candidate falsifiers

This candidate is weakened or falsified if reconstruction shows that:

- the validator must duplicate the producer, optimizer, backend, or complete
  runtime and is not a smaller trust boundary;
- witnesses require hidden producer state or unavailable private inputs;
- local certificates compose only by rerunning every producer or importing an
  unbounded theorem environment;
- no independent consumer reads a proposed durable certificate;
- certificate schemas churn whenever Stage 3–6 domain semantics evolve;
- validation success is mistaken for target admission, capability continuity,
  soundness, endpoint validity, or relying approval; or
- effectful transitions are mislabeled as independently replayable pure
  transformations.

## 8. Equal-resolution comparison

| Axis | Candidate A: domain contracts | Candidate B: universal algebra/artifact | Candidate C: capability lifecycle | Candidate D: proposal/validation |
|---|---|---|---|---|
| Architectural center | Domain-owned operation and result types | Shared typed arrows, validation state, and optional portable record | In-process authority states and narrow handles | Separation of construction from edge-specific checking |
| Shared layer | Descriptive schema, catalog, invariants | Executable algebra; possibly a wire schema | Capability construction and degradation rules | Validator protocol and optional certificate envelope |
| Relation ownership | Fully local to bridge owners | Local semantics registered into central algebra | Fully relation-specific outside lifecycle | Fully per edge, owned by validator contract |
| Authority strength | Clear by convention and typed APIs; depends on owner discipline | Explicit roles are inspectable, but central registration can become an oracle | Strongest in-process least-authority enforcement | Strong proposal/check split when validator is genuinely independent |
| Semantic identity | Domain IDs only | Domain IDs plus optional transition-artifact ID | Domain IDs; capabilities usually un-identified and process-local | Domain IDs plus optional edge-certificate ID |
| Composition | Explicit per pair or relation family | Generic only through registered typed composition laws | Procedural capability chaining; semantic composition remains explicit | Certificate/provenance chains plus separate end-to-end checker |
| Cross-process replay | Edge-specific and uneven | Strongest uniform surface in portable subvariant | Re-authenticate and recompute; no capability replay | Strong for selected edges with portable witnesses |
| Effectful operations | Domain-specific effect contracts | Requires a separate effectful arrow/event fragment | Natural authority gate, but observation semantics remain domain-owned | Preflight plus attribution; not ordinary validation replay |
| Extensibility | Local additions; risk of drift | Uniform discovery; risk of central-schema churn or opaque extensions | Local capability additions; risk of handle proliferation | Local validator additions; risk of checker proliferation |
| Diagnostics | Richest domain vocabulary, weakest uniform aggregation | Uniform envelope, possible loss of domain meaning | Precise at minting boundary, potentially opaque afterward | Precise relation counterexamples when validator supports them |
| Generic tooling | Requires projections or adapters | Strongest catalog, provenance, orchestration, and query potential | Requires safe introspection views | Moderate through validator/certificate registries |
| Wire-format pressure | Lowest by default; fragmented local formats remain possible | Highest if portable; lower but less capable if process-local | Low; authority deliberately degrades at serialization | Per-edge and demand-driven, but may proliferate |
| Primary permanent risk | Inconsistency and integration tax | Universal lowest common denominator and compatibility burden | Process-local opacity and authority ecology | Validator/certificate duplication and false proof-carrying claims |
| Strongest fit if reconstruction finds | Few durable consumers and genuinely different relations | A real uniform transition-graph consumer and common compositional laws | Most consumers are in-process and authority misuse is the dominant pressure | Complex producers with materially smaller independent checkers |

No scalar score should be derived from this table. In particular, generic
tooling cannot compensate for an authority or identity failure, and low wire
risk cannot compensate for the absence of a required independent consumer
surface.

## 9. Orthogonal decisions and admissible synthesis

The four candidates expose four questions that Stage 2 may ultimately answer
at different granularities:

| Decision | Alternatives |
|---|---|
| Contract ownership | domain-owned; bridge-owned; centrally indexed |
| Runtime authority | raw checked facts; narrow capabilities; trusted procedure |
| Checking strategy | direct recomputation; paired check; translation validation; accepted trusted boundary |
| Persistence | none; domain result; edge certificate; universal artifact |
| Composition | procedural sequencing; relation-specific theorem; registered algebra; no supported composition |

A possible later synthesis could use domain-owned contracts, capability-based
admission, relation-specific validators for compiler and projection edges, and
no universal persisted transition artifact. Another could justify a common
algebra only for pure checked semantic relations while leaving operational and
reliance transitions outside it. These are examples of the design space, not
recommendations.

The synthesis rule must be positive: each shared mechanism needs at least two
transitions with the same semantics, authority, lifetime, outcome structure,
and consumer need. Similar table columns alone do not justify extraction.

## 10. Provisional scenario portfolio

These scenarios are discriminators, not a specification of all supported
transitions and not evidence that a candidate is correct.

| Scenario | Required setup | Architectural pressure and observation |
|---|---|---|
| Minimal lifecycle across processes | Author, normalize, authenticate, admit, persist, decode in a fresh process, and admit again | Distinguish identity preservation from authority reconstruction; reveal whether replay needs a common artifact or exact domain checks |
| Equivalent authoring histories | Two workbench proposals normalize to one canonical Protocol | Target identity must ignore proposal history while diagnostics and provenance may differ |
| One Protocol, two Interfaces | Same `ProtocolId`, two distinct `ProtocolInterfaceId`s, same endpoint role | Projection must be closed over both IDs; no carrier-label lookup or interface laundering |
| One Protocol, two ProverPlans | Same verifier-visible Protocol with two plan IDs and supplier choices | Separate `PlanRealizes`, projection, supplier binding, and realization; compare paired capability with portable certificate |
| Fresh coins to Fiat--Shamir | One Core, one fresh-coin Protocol, one FS Protocol and construction | Exercise different Protocol IDs, theorem-bearing `FSCompile`, assumptions, and nontrivial relation composition |
| Search-heavy checked successor | Compiler explores many candidates and proposes one cheaper successor | Test producer/checker split, config closure, protected observers, intentional changes, and target re-admission |
| Successful negative analysis | A well-formed supported question yields `false` with a derivation | Ensure the framework does not encode negative truth as refusal or failed transition |
| Unsupported projection | Admitted source contains an obligation unsupported by one endpoint target | Required typed refusal without invalidating source admission or minting incomplete coverage |
| Source-free OIR | A valid OIR is supplied without Protocol or source-bound coverage evidence | Local OIR admission may succeed; source coverage must remain unknown or refuse |
| Composed Protocol | Two child occurrences are composed with a causal seam and new schedule | Distinguish semantic Core composition from chaining lifecycle or bridge records; test occurrence namespaces and property transport |
| Carrier and regime evolution | Same transport payload is decoded under two carrier versions and two semantic regimes | Separate decoder success, `RepresentationEq`, semantic comparability, identity, and re-admission |
| Independent replay with missing closure | Certificate or receipt is present, but one cited declaration preimage is absent | Digest or signature must not substitute for required semantic input; expose validator closure requirements |
| Partial operational effect | Invocation emits one externally visible action and then fails | Require causal effect report, retry boundary, and non-backflow into OIR or Protocol meaning |
| Evidence and reliance split | An observation supports an appraisal that one consumer accepts and another rejects | Prevent evidence, assessment, and policy-qualified reliance from collapsing into one universal validity edge |
| Unknown future relation kind | An older consumer sees a new meaning-bearing bridge or certificate payload | Fail closed without treating opaque bytes as a checked transition; measure extension and versioning cost |

## 11. Cross-candidate falsification probes

The following probes apply to every candidate:

1. **Hidden-read substitution.** Change an uncited resolver, compiler,
   interface, supplier, theorem, or policy input while keeping every declared
   input fixed. Any changed normative result falsifies closure.
2. **Identity laundering.** Substitute a different Interface, Plan, semantic
   regime, or checker regime behind an equal `ProtocolId`. No result may retain
   authority by subject-ID coincidence alone.
3. **Capability laundering.** Serialize, copy, reopen, mutate, or cross an FFI
   boundary with a supposedly admitted object. A raw flag or record must not
   preserve process-local authority.
4. **Relation inflation.** Ask a checker for a stronger conclusion than its
   named relation—for example, soundness from structural admission or complete
   coverage from local OIR validity. The correct behavior is refusal or an
   explicitly weaker result.
5. **Composition laundering.** Chain two individually valid edges whose
   assumptions, protected observers, quantitative losses, or policies are
   incompatible. No framework may infer an end-to-end claim from adjacency.
6. **Negative-result confusion.** Compare a supported false analysis,
   unsupported analysis, malformed question, missing theorem, and checker
   failure. They must remain distinguishable.
7. **Effect erasure.** Fail after an externally visible action. A pure
   transition abstraction must not erase the effect or promise rollback it did
   not perform.
8. **Authority cycle.** Feed observation, certificate, appraisal, or relying
   approval backward as authority to redefine Protocol, Interface, OIR, or
   relation meaning.
9. **Wire-without-consumer.** Require the proponent of each durable transition
   object to identify the independent producer/consumer boundary, retention
   window, release relationship, and cheaper alternative. Absence of these is
   evidence of premature commitment.
10. **Diagnostic collapse.** Force an identity mismatch, uncovered endpoint
    obligation, illegal rewrite, and unavailable supplier. A common framework
    must preserve the semantically relevant distinction rather than return
    generic invalidity.

## 12. Evidence required before convergence

The current reconstruction must supply, for every existing and selected target
edge:

```text
exact current normative owner and section
concrete source and result categories
implementation entry points and constructed types
all explicit and ambient reads
semantic regime and version inputs
identity computations and cache keys
capabilities minted, retained, narrowed, copied, or discarded
current process, FFI, persistence, and replay boundaries
proposal/search complexity versus checker complexity
success, negative result, refusal, and partial-failure behavior
diagnostic consumers and required granularity
existing durable artifacts and actual readers
composition uses and assumed laws
current tests, examples, and non-claims
```

The reconstruction must include at least the lifecycle spine, static linking,
analysis, checked Protocol transformation, relation correspondence, OIR
projection, ProverPlan checking, supplier binding, endpoint realization,
deployment, invocation, observation, appraisal, and reliance.

The following observations are especially discriminating:

- whether consumers already need transition history or only current admitted
  subjects;
- whether rechecking cost is small relative to producing and maintaining a
  certificate;
- whether a validator can be materially smaller and more stable than its
  producer;
- whether any result must cross an independent release or trust boundary;
- whether two relation families possess a real shared composition law;
- whether current capability objects retain undeclared mutable environments;
- whether diagnostics are consumed by humans, automation, or independent
  checkers; and
- whether operational effects can be isolated from pure semantic transitions.

## 13. Convergence procedure after reconstruction

Once the evidence above exists, Stage 2 should:

1. instantiate all four candidates over the same complete transition catalog;
2. choose representative edges from lifecycle, checked change, semantic
   bridge, operational effect, and appraisal/reliance families;
3. specify each edge at identical resolution under every candidate;
4. run the scenario and falsification portfolio;
5. measure where a purportedly shared mechanism has identical semantics and
   where it only has similar fields;
6. identify actual in-process, cross-process, independent-checker, cache, and
   retention consumers;
7. compare the strongest coherent global bundles and disciplined hybrids;
8. select per-edge mechanisms only under a stable architectural rule;
9. state residual trust, wire promises, deferred alternatives, and reversal
   triggers; and
10. promote the chosen contracts into their exact domain owners.

## 14. Current conclusion and non-conclusion

All four candidates are coherent enough to survive the divergent phase when
interpreted in their strongest form:

- Candidate A maximizes domain ownership and delays common runtime or wire
  commitments.
- Candidate B maximizes uniform introspection, algebraic composition
  opportunities, and portable replay, at the largest central-schema risk.
- Candidate C makes process-local authority and serialization loss the primary
  organizing principle.
- Candidate D makes proposal/check separation and independent per-edge
  validation the primary organizing principle.

These statements are capability and cost hypotheses. They are not verdicts.
The current evidence is insufficient to know whether zkc has a genuine
universal transition consumer, whether most important edges admit small
validators, whether capability retention closes or hides read sets, or whether
domain-owned contracts would drift in practice.

No final framework, hybrid, transition artifact, certificate format, or
composition algebra is selected by this note.
