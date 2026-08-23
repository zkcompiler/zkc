# Stage 3 Protocol-and-Relations convergence record

> **Document kind:** Temporary Stage 3 integrated convergence and promotion
> record
> **Document state:** Stage 3.4 selection and Stage 3.5 durable promotion,
> absorption accounting, downstream handoffs, and documentation exit CLEAN and
> CLOSED on the exact snapshots recorded in Section 2; the whole bounded Stage
> 3 design-research program is complete
> **Authority:** None. This record explains a research decision. It does not
> change the current specification, admit a subject, mint authority, authorize
> implementation or migration, or establish a cryptographic claim.
> **Scope:** Protocol semantics, canonical PIR, Interface, Plan, Relations,
> Fresh-to-Fiat--Shamir construction, semantic Core composition, authority,
> outcomes, persistence, and later-owner seams.
> **Disposition:** Retain as bounded handoff and deletion-accounting evidence
> until every still-needed rationale has a durable owner; remove this temporary
> record before documentation authority cutover.

Candidate labels on this page are local to the Stage 3 portfolio. In
particular, **Stage 3 Candidate C** is not the candidate called C in Stage 1 or
Stage 2.

## 1. Integrated decision

Select the corrected **Candidate C: a small language-independent semantic
kernel, one physically canonical bijective MLIR Protocol carrier that embeds
Core, and independently identified typed satellites**.

Adopt Candidate D's useful technique inside that architecture: Core interaction
is a finite, closed algebra of typed effect occurrences with explicit inputs,
guards, actors, causal predecessors, protected observations, failures, and one
total schedule. No v0 event has an ambient ordinary-value result; every value
origin has a named Core constructor. Do **not** make a universal event calculus,
handler runtime, or generic simulation framework the semantic center.

Defer Candidate E to optional authoring research. A future module language may
generate a closed Candidate-C Core, Protocol, Interface, Plan, and exact
construction maps, but neither the module nor its elaborator is required to
interpret or admit the generated subjects.

Reject Candidates A and B as v0 architecture centers without reopening the
fixed Stage 1 or Stage 2 decisions:

- Candidate A remains a useful current-preserving control, but its semantic
  quotient conflicts with the selected physical-canonical-carrier boundary and
  creates permanent representative-read and pre-erasure obligations.
- Candidate B remains a possible non-authoritative transport package, but a
  canonical multi-subject bundle is not a semantic root and bundle admission
  cannot grant authority to its members.

The selected topology is:

```text
language-independent InteractiveCore
  + exactly one ChallengeInterpretation
  = Protocol
       <-> exactly one closed canonical MLIR PIR graph

Protocol
  +--> ProtocolInterface[ProtocolId]
  +--> ProverPlan[ProtocolId]
  +--> Relations-owned bindings and correspondence
  +--> FSConstruction[source ProtocolId, target ProtocolId]
  `--> CoreComposition[child occurrences, target CoreId]

admitted subjects + exact model/theorem/assumptions
  -> later Analysis results

admitted Protocol/Interface/role/Plan basis
  -> later OIR and Realization results
```

The language-independent algebra is the selected target mathematical meaning,
intended to become normative only through explicit consolidation and cutover;
it is not a second serialized production format. MLIR remains the only
canonical v0 production carrier in that target. An independent checker or
formal model may interpret the same algebra, but agreement with such a model
does not create a second source of authority.

## 2. Decision, promotion, and exit status

Stage 3.4 is closed on one exact reconciled snapshot set. Each clean notice was
independent of the document it audited; later candidate repairs were rechecked
before closure rather than grandfathered from an earlier hash. Stage 3.5 has
since promoted the selected result into self-contained durable target owners,
accounted for every temporary input, and closed two separate downstream entry
contracts without activating either branch.

| Gate | Definitive record | Closure evidence |
|---|---|---|
| Integrated architecture selection | **CLEAN / decided:** corrected Candidate C, with D's typed-event technique and E deferred to authoring research | The integrated decision, target, candidate portfolio, scenarios, and matrices agree on the selected topology, alternative dispositions, and non-claims |
| Target type, operation, and authority closure | **CLEAN** on target SHA-256 `107255938efa6af7802030b93bdbc9dcb4d5535335866cffa304df33083a7f5b` | Full target-only audit found no unresolved carrier, type, operation, identity, dependency, lifecycle, or authority contradiction |
| Equal-resolution candidate and IR-transfer audit | **CLEAN** on target `107255938efa6af7802030b93bdbc9dcb4d5535335866cffa304df33083a7f5b` and candidate SHA-256 `ce4f71e88741f71d126c81ce8afeb2cb29da83f856bb13fdf032a702756b9923` | A--E independently answer the same twelve axes; A remains an explicit admitted rich-quotient-carrier reopening control, B excludes occurrence-local inputs from its authoritative bundle, C is gate-eligible, D remains conditional, and E remains an authoring overlay |
| Integrated scenario and falsification audit | **CLEAN** on scenario SHA-256 `ba630d5d860c7f590eb375fe88b23ab30270d7385686e02b86da2adee268819a` against the same target and candidate snapshots | Every named scenario and hidden-input, authority-laundering, outcome-separation, unknown-extension, and opportunity probe has an exact result or bounded later-owner handoff |
| Cross-cutting matrix audit | **CLEAN** on matrix SHA-256 `947d963c0d5c926e6901415cc78701404ae9e8d42db3052b285daad29a695b7a` against the same target and candidate snapshots | Identity, dependency, authority, outcome, read-set, producer/consumer, persistence, and equal-resolution tables contain no unresolved contradiction |
| Stage 3.4 exit | **CLOSED** | All independent findings were repaired, reconciled across the affected documents, and re-audited at the exact hashes above |
| Stage 3.5 durable promotion and absorption | **CLEAN and COMPLETE** | The integrated decision and exact target semantics are self-contained under the durable `project/`, `pir/`, and `relations/` owners; the absorption record accounts for every temporary input and retained rationale |
| Stage 4A and Stage 4B handoffs | **CLEAN and COMPLETE; neither branch activated:** Stage 4A SHA-256 `f92a5ffc8d583d603b1e15aac6f73b1d147636c3fc1a13bf6fbdfb840942b7d8`; Stage 4B SHA-256 `062efbd41caa9d6dfaa933816204027b2803ea3896abe886a1fb48285fc2fd12` | Separate bounded entry contracts fix Analysis-to-Compiler and OIR-to-Realization intake, authority, noninterference, reopening, and cross-branch reconciliation requirements |
| Downstream durable route reconciliation | **CLEAN:** Analysis index SHA-256 `6b720daf004497b7b780f08325219d12e6f8907232a961d1b90b674997be6a4c`; Compiler index SHA-256 `386ec771564964dabbb71618e9c728141aeecf569c881e6ee71db9cf15081ac1`; OIR index SHA-256 `92fa3bf238baf85eee122cbbb947c326ffdbf364e53bd9741e88a79cb7363bdf`; Realization index SHA-256 `16f26325689e65ab5b2aca52185f7a1af55e8806e263fa270067fb7dfdaf0d70` | The four downstream indexes route the completed handoffs, preserve their authority and noninterference boundaries, and do not activate either Stage 4 branch |
| Final Stage 3 documentation exit | **CLEAN and CLOSED** | The independent [exit audit](exit-audit.md) found no remaining blocker after the stable matrix, handoff, downstream-index, durable-page, package-accounting, route, link, and mechanical checks were reconciled |
| Stage 4 activation | **Not claimed** | An explicit later activation decision remains required for either branch |

The closed whole-Stage 3 result is a bounded design-research result, not a
normative, proof, implementation, migration, or property result. A new
substantive contradiction or reversal trigger requires an explicit reopening
and another cross-document audit; it cannot be patched as an ambient exception.

## 3. Research basis

This decision is the result of six evidence layers, none of which voted by
precedent alone.

1. The [design-force and opportunity ledger](design-forces-and-opportunities.md)
   fixed the hard requirements: ordered interactive meaning, protected
   observations, functional closure, physical/semantic separation, independent
   Interface and Plan variation, noncollapsible Relations and Fiat--Shamir
   judgments, explicit composition, qualified outcomes, and fail-closed
   evolution.
2. The [IR carrier and schema dossier](cases/ir-carrier-and-schema.md) showed
   that MLIR provides valuable structure, conversion, verification hooks, and
   tooling, but does not itself provide zkc semantic denotation, unique physical
   form, content identity, admission, or compatibility. StableHLO/VHLO,
   SPIR-V, and WebAssembly further show that schema closure, validation,
   canonical form, stable serialization, and compatibility are separate
   product contracts.
3. The [ZK-system dossier](cases/zk-systems.md) found recurring separation
   among relation meaning, protocol meaning, prover construction, and carrier;
   showed that transcript inputs and order affect challenges; and showed that
   batching, compilation, recursion, folding, and IVC are not one graph-union
   operation.
4. The [protocol-theory dossier](cases/protocol-theory.md) separated relation
   satisfaction from interactive execution, Fresh-to-Fiat--Shamir construction
   from theorem-backed `FSCompile`, and structural composition from property
   composition. It also required exact occurrences, framing, challenge
   prefixes, repeated-child tags, and challenge-sharing policy.
5. The [formal-protocol and composition dossier](cases/formal-protocols-and-composition.md)
   supplied the typed-event technique: typed syntax and explicit handlers are
   strong tools for denotation and mechanization. The same cases warn against
   replacing domain-owned claims, relation judgments, and theorem premises with
   one generic effect or validity interface.
6. The [integrated target model](target-semantic-model.md),
   [current-to-target inventory](current-to-target-gap.md),
   [candidate portfolio](candidate-models.md),
   [integrated scenarios](scenario-results.md), and
   [validation matrices](validation-matrices.md) tested whether the clean-sheet
   target preserves useful current invariants, removes known contradictions,
   answers every candidate at equal resolution, and remains closed at all
   producer/consumer seams.

The resulting selection is not an average of surveyed systems. It transfers
mechanisms whose assumptions fit zkc, rejects path-dependent installed-base
costs that zkc does not yet have, and adds Protocol-specific structure where no
surveyed IR supplies it.

## 4. Selected semantic decisions

### 4.1 Core and Protocol

`InteractiveCore` owns one finite verifier-visible public-coin interaction. Its
closed content includes:

- exactly one Prover and one Verifier, plus zero or one PublicEnvironment,
  which is required if anything references it;
- occurrence-indexed typed ports whose direction fixes `InputSource` or an
  exact `OutputValues(CanonicalSeq<ValueRef>)` binding, pure values with
  occurrence-exact origins and selected-branch guarded merges, protocol
  objects, private and public randomness, and explicit correlation contracts;
- typed event occurrences, causal edges, activation guards, and one
  identity-bearing total potential-event schedule;
- challenges, claims, reductions, checks, verifier-visible failures,
  terminals, endpoint obligations, prover obligations, and a unique declared
  prover-obligation failure for every exact obligation/cause pair; and
- exact semantic dependencies and complete admission closure.

One `ChallengeInterpretation` completes that Core into a Protocol. Fresh public
coins and Fiat--Shamir are distinct Protocol meanings and therefore distinct
`ProtocolId`s even when they share a `CoreId`.

`CoreId` is a semantic subidentity, not a second official artifact root. The
official canonical PIR artifact has one `pir.protocol` root containing the Core
and the selected challenge interpretation.

`PortValue` may read input occurrences only. An output declaration instead
groups one exact canonical value sequence. It creates no value occurrence,
exposure, path-availability fact, event, or intra-Core role-knowledge transfer.
Interface changes external containers and names; it cannot invent either
binding or convert output grouping into exposure.

### 4.2 Typed events without a universal event calculus

The Core event algebra directly names public-value observations, messages,
fresh challenges, checks, explicit `RaiseFailure`, artifact emissions, and
terminal reachability. Every kind is wrapped in one closed `EventDecl`
occurrence envelope carrying its exact actor, inputs, protected observations,
activation guard, and `EventObligationBasis`; causal and schedule position
remain separate Core structure. Inputs, observations, actor, kind-matched
endpoint contract, and the optional Prover construction basis are derived
exactly from the event kind. Admission also checks the kind-specific actor laws:
`Message.actor == from`, `FreshChallenge` belongs to the unique
PublicEnvironment, checks/failures/terminals are verifier actions, and public
observations or artifact emissions name the role that performs them. It does
not infer an actor from schedule position.

No v0 event kind produces an otherwise unaccounted ordinary value. The closed
fourteen-form `ValueNode` sum uses exact constructors for ports, constants,
private randomness, challenges, prover outputs, check/failure values, tuples,
projections, variants, pure application, canonical `GuardDecision`, and
selected-branch `GuardedMerge`. `GuardDecision` stores the canonical finite
reduced ordered decision diagram over the closed Boolean atoms; every stored
activation, merge, suppression, and terminal-route guard is a `GuardValueRef`.
`InjectVariant(sum, ordinal, value)` remains the canonical injective
constructor for a typed closed sum and has no user-selected implementation. A
future value-producing effect requires a named constructor and new Protocol
regime.

This is the accepted contribution from Candidate D. It makes interaction,
branching, transcript effects, and failures explicit enough for independent
semantics and later formalization. It stops before the Candidate-D architecture:

- claims and linear resources remain first-class Core structures, not generic
  effects interpreted by an ambient handler;
- Interface, Plan, Relations, transcript construction, and composition remain
  domain-owned typed subjects or checked relations;
- handler adequacy cannot replace subject admission or correspondence; and
- the admitted grammar is finite, first-order, acyclic, and closed rather than
  a general effect language.

Bounded branching scans the total schedule, skips inactive events without
producing their observations, and commits the first reached terminal only
after exact consumption, action, and failure resolution. The last scheduled
event is the unique canonical-true fallback terminal under the derived
execution-still-live guard. Missing, duplicate, early, unexpected, or
private-sampling-failed Prover output follows the frozen deterministic
precedence and yields the exact Core-owned `ProverDidNotProduce` outcome and
partial state; it is not a verifier-visible failure or terminal.

Each verifier-visible `FailureDecl` has exactly one `FailureSourceRef` from the
closed `CheckFalse`, `ChallengeSampling`, or `ExplicitAbort` sum. Every source
and failure are occurrence-exact: a false check, failed challenge sample, or
active `RaiseFailure` names exactly one matching failure. The effect either
terminates at a declared terminal or continues with
`FailureStatusValue(this failure)`.
That runtime value is the fixed `FailureStatusToken { failure, class }`, with
no ambient payload. A total `FailureOccurred` Boolean supports compound
decisions without fabricating a terminal, and exhaustive one-hot
`GuardedMerge` is the only phi-like value. `InjectVariant` first gives
heterogeneous typed status values a declared common sum domain; it does not
weaken their variant or payload identity. These verifier failures remain
distinct from Interface errors, prover nonproduction, and checker failure.

### 4.3 Semantic identity and the canonical MLIR carrier

Meaning is defined by the language-independent algebra under an exact typed
semantic regime. Identity is a domain-separated digest of the regime and an
injective canonical semantic encoding. Printer spelling, MLIR bytecode,
locations, source names, producer metadata, process objects, and tool releases
do not define semantic identity.

Canonical PIR is a closed MLIR profile bijective with the Core/Protocol
encoding modulo only declared carrier trivia: in-memory operation identity and
required SSA alpha-renaming. Unknown meaning-bearing operations, attributes,
dependency kinds, or regimes fail closed. Generic MLIR parsing, verification,
canonicalization, conversion legality, and bytecode decoding do not by
themselves establish physical canonicality, semantic identity, or admission.

This graph is the unique physically canonical v0 carrier of Protocol; Core is
an embedded subidentity, not a second serialized artifact root. Interface,
Plan, Relations, transcript construction, composition, and checked results are
canonical algebraic satellite values. They may have JSON, binary, MLIR, or API
transport profiles only when each profile has a total tagged lossless decode to
the exact value. Profile validation and value reconstruction precede dependency
authentication, identity recomputation, and domain admission; transport choice
cannot add meaning or create another Protocol carrier.

Authoring normalization may search, infer, and erase source syntax only when it
produces a capability-neutral `NormalizationAudit` that classifies every erased
distinction as retained, extracted to a typed satellite, proved inside the
finite declared quotient, or rejected before erasure. The normalizer's output
is still only a candidate.

Every semantic field that denotes a codec, encoder, decoder, framing rule,
sampler, or pure function is a `CanonicalAlgorithmSpec<K>` and therefore
canonical identity-bearing data: either a closed finite typed total term or a
content-addressed contract reference with exact ABI and dependency IDs. A live
implementation, function pointer, or checker capability is never the
algorithm's semantic identity and remains outside the preimage.

### 4.4 Authentication, admission, and local authority

Every identity-bearing Stage 3 subject follows:

```text
candidate
  -> physical authentication
  -> domain admission
  -> opaque immutable process-local capability
```

For canonical PIR, authentication is ordered: decode and parse; check the one
root, closed allowlist, physical fields, blocks, references, defaults, and
ordering; form only an unauthoritative diagnostic `ReadUnchecked_R`; authenticate
the exact Core and optional transcript dependency preimages under their exact
closed authentication-capability records; recompute `CoreId`, construction ID
when present, and `ProtocolId`; establish `IdConsistentCanonicalPirGraph_R`;
and only then expose authoritative bijective `Read_R`. Protocol admission
separately consumes retained dependency views, exact
`CompositionContextAuthority`, and the Fresh/FS-keyed
`ExactProtocolAdmissionCheckerCapabilities`. Construction adds independent
target authentication and admission before a checked source-to-target result.

Protocol admission authenticates and sub-admits Core first and retains only a
transaction-scoped `CoreAdmissionWitness`. The Fresh branch proves that no
transcript dependency exists. The FS branch authenticates and admits the exact
referenced `TranscriptConstruction` against the cold Core witness and its exact
dependency/law capabilities before admitting the enclosing Protocol. The
witness is discarded after success or failure; Core never becomes a separately
persistent official authority root. A composed FS branch additionally needs
the exact same-invocation scoped formation authority or a freshly reconstructed
affirmative composition result.

No raw bytes, semantic ID, stored marker, signature, provenance record,
package membership, or copied object recreates authority. Serialization,
mutation, reopen, unmediated FFI, or process reset ends capability continuity;
the receiving side begins again from raw material.

### 4.5 Interface and Plan satellites

`ProtocolInterface[ProtocolId]` owns external names and ports, statement and
proof containers, total codecs, role entry points, proof-event occurrence
mapping, terminal outcomes, and application bindings. Its identity includes
the exact kind/regime/ID/ABI-qualified least Interface-algorithm dependency
closure. Admission requires exact dependency preimages and authentication
capabilities, retained views, the admitted Protocol view, and identity-matched
law-checker capabilities. A restriction, default, semantic reordering,
transcript rewrite, challenge change, or accepted-language change is not an
Interface-only change.

Its component schema is closed. `StatementContainerMember` is legal exactly
for public Statement input occurrences; every other external port uses an
independent value codec. The sole statement binding owns its encoder/decoder
and returns the dependent total no-extra `ProtocolPublicAssignment` over every
and only matching Protocol occurrence. The sole proof binding covers every and
only Proof-channel message, and its three presence constructors name exact
`ProofEventOccurrencePredicateRef`s—restricted
`EventActionOccurrenceRef`s—rather than activation guards. Decoding is
pure and reconstructs a guarded potential trace without executing Protocol;
the tagged result is only `Decoded` or `Malformed`. External outcomes are in
total bijection with terminals and carry exactly each terminal's public-output
sequence. Continuing failures and `ProverDidNotProduce` have no outcome tag,
and output grouping grants no exposure.

`ProverPlan[ProtocolId]` owns typed private-input descriptions, Protocol values
and objects, a construction DAG, typed holes, the least private dependency
closure, supplier requirements, and proposed routes for exact prover
obligations. Runtime secret values, credentials, supplier handles, mutable
state, live capabilities, and invocation occurrences are excluded from its
semantic preimage.

The Plan component grammar is closed. A private Prover port occurrence has one
ingress through its unique `ProtocolPrivatePortOccurrence` Plan input; raw
private `PortValue` is excluded elsewhere. Raw Core `PrivateRandomnessValue`
is excluded from ordinary and transitive operands and enters only through the
owner-matched ordered `UsesProtocolRandomness` effect. Basis inputs may use the
unique private-port Plan input or exact available Protocol values/objects,
never `ExternalSecret`. Derived route deadlines check every transitive Protocol
operand at `PreAttempt`; each obligation route has one producer, total basis
map, bijective output map, singleton randomness owner, and exact ordered
randomness-ingress sequence.

Plan authentication and admission establish only dependency, typing,
occurrence, DAG, deadline, hole, and supplier closure. `PlanRealizes` is a
separate A/N checked relation establishing exact private-port and obligation
coverage, basis/output maps, randomness routing, confinement, and declared
reads. It proves no value correctness, distributional fidelity, supplier
correctness, execution success, honest-prover completeness, cost, or
cryptographic property. Stage 4B computes `PlanSemanticClass` and the exact
reader set; no Plan field may self-assert placement.

### 4.6 Relations and artifact ingress

Relations owns separate roles for:

```text
externally owned RelationDefinitionRef
RelationInterface
RelationInstance(public assignment)
PrivateWitnessAssignment(local confidential occurrence)
RelationBinding
RelationArtifactProfile
RelationAdapterContract
RelationArtifactObservation
```

A Protocol may cite opaque semantic roles but does not define relation truth.
Relation ingress consumes narrow admitted Protocol and Interface views only
after their admission; it never participates in Protocol identity through an
ambient registry or name lookup.

Relation interfaces, instances, bindings, profiles, adapters, and observations
have occurrence-indexed schemas, exact least dependency closures, and separate
authentication/admission/execution-capability lifecycles. Public and witness
binding maps are total and injective over relation occurrences but need not
exhaust Protocol occurrences; each entry owns exact bidirectional value-domain
bridges and round-trip laws. Committed-object grounding is total over relation
object occurrences, permits independently checked aliasing to one Protocol
object, and claims neither inverse injectivity nor Protocol-object coverage.

Artifact interpretation is expectation-free. Exact bytes under one admitted
profile and adapter may yield an observation candidate on the exact `Completed`
interpretation outcome, containing facts and unread fields. A separately
authenticated exact-field comparison may then
establish agreement or a fact-retaining negative disagreement with a relation
interface. Interpretation failure is not disagreement, and an observation
cannot substitute for comparison.

Committed-object grounding, structural Protocol-at-Interface correspondence,
public-instance correspondence, and later relation satisfaction are distinct
questions. `CorrespondenceQuestion` selects any subset of the four base clauses
`PublicPorts`, `WitnessPorts`, `ResultBindingReferenceShape`, and
`CommittedObjectGrounding`, plus at most one separate optional artifact
question. The base subset may be empty only when the artifact question is
present. Result binding checks only the exact claim/check/Accept-terminal
constructor and reference shape; it gives no relation-result behavioral
interpretation. Missing requested bases produce `CannotAnswer`; they do not
become a negative correspondence result. Instance correspondence consumes an
affirmative public-port capability, admitted bridge views and exact bridge
execution authority, and the dependent `ProtocolPublicAssignment` before
applying `to_protocol`.

Private witness bytes receive no mandatory global content identity. Equality-
revealing public identifiers and unsafe persistence are not prerequisites for a
later `RelationSatisfies` judgment.

### 4.7 Fresh-to-Fiat--Shamir construction

`TranscriptConstruction` is a separately authenticated subject scoped to one
Core and the exact Protocol semantic regime. Its identity includes the exact
kind/regime/ID/ABI/edge-qualified least algorithm-dependency closure. It owns
total initialization and public context-occurrence initialization, injective
framing, sampling and abort behavior, one total action for every Core event,
and one action-occurrence prefix descriptor for every challenge:

```text
Absorb(every and only same-event input ordinal in canonical order)
DeriveChallenge(exact squeeze, intended distribution, and linked failure)
NoTranscriptAction
```

Initialization, context binding, framing, and absorption are total and
infallible; only challenge squeezing may produce the declared typed failure.
Every Absorb covers every and only same-event `ExactEventInputOccurrenceRef`
once, and no event output or cross-event atom is legal. Derivation occurs on
challenge attempt; only success publishes the value. The `abort_map` is total
over exact challenge occurrences and equals each challenge's linked
`ChallengeSampling` failure. Independent and joint annotations are intended
distribution contracts checked structurally, not claims about the induced
Fiat--Shamir distribution.

The context-authority sum is closed: standalone formation uses
`NoCompositionContext`, while in-transaction composed formation uses the exact
fresh same-invocation `ScopedCompositionFormationAuthority`. Cold replay does
not bootstrap admission from a serialized or previously checked result: it
reruns Core construction/subadmission, mints and consumes a new scoped
formation authority, admits the Protocol, and only then finalizes the A/N
composition check. Only that final affirmative `CheckedCoreComposition` may
supply checked-composition context authority to a later consumer. Context
initialization is total over exact public `ContextPortOccurrenceRef`s and
cannot read private ports or infer composition history from ambient state.

`ConstructFS` produces only a target Protocol candidate and exact
`FSConstructionMaps`, including source/target Protocol IDs, shared Core ID,
interpretation change, total Protocol-scoped event/challenge bijections, and
potential/action/runtime prefix descriptors. The target is independently
authenticated and admitted. `FinalizeFSConstruction` then returns a qualified
A/N `CheckedFSConstruction`; only an affirmative result may feed later
`FSCompile`. `FSCompile` is a separate theorem- or model-backed judgment, and
every property transport is a third property-specific judgment with its own
assumptions and losses.

When semantic composition selects an FS target, context adequacy is checked at
the only noncircular time: after `ConstructAndSubadmitCore` has formed the
target Core, `FormAndAdmitProtocol` consumes the exact closed
`FiatShamirFormationInput`, validates construction context and context-port
mapping, and authenticates/admits the construction and enclosing Protocol in
the same transaction. Child FS status and ambient composition history supply
nothing.

### 4.8 Semantic Core composition

Semantic composition consumes admitted child Core views and an independently
authenticated and admitted `CoreCompositionSpec`. Local child slots prevent
identity self-reference and distinguish repeated occurrences of the same
`CoreId`; durable child-occurrence references form only after spec
authentication. v0 admission requires every child Core semantic regime to
equal the target Protocol regime.

The spec commits to the target regime, ordered child slots, sequence-valued
occurrence face maps, ordinary and terminal origin maps, restricted local
additions, mapped-child/seam/derived/local causal-edge provenance, one complete
target-event permutation, total challenge/private-randomness/failure/reach
policies, an exact terminal combiner, and the complete local target fragment.
It has no dependency- or obligation-merge policy field. Dependencies are the
deterministic least target-required reachable closure selected from exact child
views plus disjoint authenticated local supplies; unused child history is
dropped. All obligations and prover-obligation failures are recomputed after
event, randomness, and construction-basis rewrites and must equal the target
fragment. The target challenge interpretation is an explicit later
transaction input, never inherited from a child.

`CoreCompositionSpecId` commits to the composition regime, target Protocol
regime, ordered child IDs and local slots, every occurrence face, ordinary and
terminal origin disposition, restricted local declaration, causal seam and
local edge, target permutation, challenge/private/failure/reach policy,
terminal combiner, target fragment, and every identity-bearing algorithm or
dependency they cite. It does not commit to a caller-proposed resolved map or
the resulting target identity. Local target references avoid self-reference;
the deterministic comparison forms durable target-scoped maps only after the
target has been independently admitted.

Role faces map deterministically to the unique target role of the same class.
Port faces are occurrence-indexed and sequence-valued, preserve direction,
visibility, domain, multiplicity, purpose, and exact output sequences, and add
every internal feed dependency to the acyclic target graph. `InternalInputs`
cannot replace a claim-producing input occurrence. Faces create no ambient
availability or exposure and cannot independently erase, invent, rename, or
merge an obligation.

Challenge policy is total and distinguishes `IndependentChallenge`,
`JointChallengeMember`, `SharedChallenge`, `DerivedChallenge`, and
`ImportedChallenge`. Independent and joint members preserve exact intended
distribution, index, marginal, failure, owner, and observation equations;
joint groups derive one noncircular common base plus ordered conditional steps.
Shared members have exactly equal post-suppression coactivation and map to one
complete target challenge bundle at one schedule position; identifier aliasing
alone has no distribution or prefix meaning.

Derived and imported child challenges map to explicit target values rather
than inventing fresh target challenge declarations. Their public availability
is represented by exact target `ObservePublicValue` occurrences, and their
fresh randomness, public-sampling obligation, sampling failure, coin index,
and old event ownership are removed or rewritten exactly. Imported values use
an exact public context-port occurrence and a PublicEnvironment-owned endpoint
obligation, never a prover obligation. Failure/source/effect/observation
backlinks agree exactly with either the preserved target bundle or the named
substitution removal.

Private-randomness policy is likewise total and distinguishes preserve, joint,
derived, and external supply. A preserved or joint member maps to an exact
target randomness/value/owner-obligation/failure bundle with matching group,
index, marginal, conditional transition, and first-failure behavior. A derived
or externally supplied value removes the child randomness declaration, its
exact occurrence in the owner's private-randomness sequence, and the matching
`PrivateSamplingFailed` declaration exactly once, and names the exact
`ProverConstructionBasisRewrite`; recomputed target obligations cannot retain
stale sampling structure.

`FailurePolicy` is total over verifier failures and `ReachExitPolicy` is
independently total over `ReachTerminal` occurrences. The terminal-origin
account partitions every child terminal source into propagation, capture, or
the exact derived/imported terminating-sampling-failure removal; ordinary and
local origin
maps cover all remaining declarations. `PreserveContinue` keeps the same
source, class, status token, observations, and continuing effect.
`PropagateFailure` and `PropagateReach` preserve exact terminal result, payload,
public outputs, action envelope, and source-before-final ordering. A terminating
failure must follow the frozen result table, no terminating failure may accept,
and intrinsic `ExplicitProtocolAbort` cannot be captured.

Failure or reach capture is an `IntentionalChange`, requires symbolic
claim-quiescence, and applies total suffix suppression. Failure capture records
the exact target failure-status token, child terminal result, and mapped public
outputs; reach capture records the terminal result and mapped public outputs.
The enclosing sum variant identifies the exact child occurrence, so neither
tuple duplicates an occurrence label. For failure capture,
the taken guard is exact `FailureOccurred(mapped failure)`; for reach capture it
is the final mapped action-occurrence guard. Every later mapped child guard is
its post-policy contribution conjoined with the negation of every earlier
captured exit.

There is exactly one terminal-combiner input for each child slot with a
captured source on a combiner-reaching path and none for any other slot. Its
status is one exhaustive one-hot `GuardedMerge`; every capture contributes one
exact `ExitStatusInjection` branch with a unique payload-typed variant and its
exact mapped-reach or `FailureOccurred` guard. Every combiner-reaching path
completes all child slots at captured sources before the first final; a slot
without an input must instead propagate on every path, making all finals
unreachable. Captured and propagated sources precede every final in the causal
graph and target permutation, and finals occur in exact route order.

The combiner's authenticated finite result-value domain contains exactly the
canonical terminal-result values in `result_domain`. Its result is the exact
`Apply` of the merged inputs; non-last routes use canonical finite-equality
`GuardDecision`s; the unique last `UnguardedFallback` materializes as canonical
true and is gated operationally by `ExecutionStillLiveBefore`. Every route's
public-output tuple is an exact `Apply`, its values are the canonical ordered
projections, and its static terminal result and `ReachTerminal` event agree
exactly. Final-attempt readiness proves no final reads an absent or unresolved
child status.

Formation is a three-phase transaction. `ConstructAndSubadmitCore` receives
exact Core admission authority and creates only a transaction-scoped witness.
`FormAndAdmitProtocol` consumes an explicit Fresh input or the closed composed
FS formation record and independently authenticates/admits the one target
Protocol. `FinalizeCoreComposition` then runs total deterministic
`ResolveCoreCompositionMaps` against exact child and admitted target views. No
caller-supplied provisional map record is transported. The checked payload is
either `Affirmative(ResolvedCoreCompositionMaps)` or a negative result with
nonempty typed mismatches and unaffected agreements; only affirmative retains
maps or grants composition-context authority. Cold replay reconstructs the
spec, children, target-required dependencies, target Core, branch-specific
Protocol authority, full body/regime/ID equality, and A/N comparison. The
result proves the named structural construction, not associativity,
commutativity, trace equivalence, Fiat--Shamir commutation, or cryptographic
property composition.

### 4.9 Views, checking, outcomes, and persistence

Later domains receive narrow purpose-specific views with explicit adequacy
predicates. A view does not become a second complete Protocol representation
and does not mint broader authority than the admitted source.

Small closed predicates use direct recomputation. A producer/validator split is
allowed only when it yields a meaningfully smaller or more stable checker for a
named edge. Theorem/model-backed questions remain with Analysis. There is no
universal checker registry, transition artifact, fact root, or generic `valid`
result.

Each owner selects from these semantically distinct outcome classes:

```text
Affirmative
Negative(reason, retained facts)
Unsupported(exact construct or question)
CannotAnswer(missing named semantic input or basis)
Refused(missing authority or prohibited invocation)
Malformed(exact framing or structural defect)
CheckerFailure(operational failure; no semantic conclusion)
```

The seven Stage 3 checked families are `CheckedPlanRealizes`,
`CheckedArtifactInterfaceComparison`, `CheckedCommittedObjectGrounding`,
`CheckedRelationCorrespondenceJudgment`,
`CheckedInstanceCorrespondenceJudgment`, `CheckedFSConstruction`, and
`CheckedCoreComposition`. Only a completed affirmative or fact-retaining
negative semantic check mints its exact capability; unsupported,
cannot-answer, refused, malformed, and checker-failure exits mint none. Every
capability binds its exact subject, regime, input, checker, read/dependency
closure, outcome, retained facts, and replay basis. Affirmative-only consumers
must receive the affirmative variant. Serialization never preserves the live
capability.

## 5. Why this architecture is selected

Candidate C is the only candidate that simultaneously satisfies all of the
following without making its main risk another architecture's permanent
problem:

- The admitted center is small enough for clean-room checking but complete
  enough to contain every verifier-visible interaction and refusal-sensitive
  distinction.
- MLIR remains the production transformation substrate, while the written
  semantic contract—not an MLIR registry, pass pipeline, printer, or Rust/C++
  class—defines meaning.
- Physical canonicality has one owner and one carrier instead of becoming a
  lifetime-wide quotient discipline or a two-format correspondence burden.
- Interface, Plan, relation, transcript, and construction variability can
  evolve independently without contaminating Protocol identity or granting
  bundle-wide authority.
- Structural results retain the exact maps later formal reasoning needs while
  security, satisfaction, and property conclusions remain unavailable until
  their own bases are supplied.
- The architecture supports several formal interpretations and authoring
  languages without requiring either to become an admitted production format.
- Its complexity is explicit in subject IDs, dependency assembly, and boundary
  checks rather than hidden in ambient handler semantics, representative read
  sets, or package conventions.

The decisive point is not that satellites are always smaller than a bundle.
It is that each satellite has a different semantic owner, substitution law,
authority, evolution pressure, and consumer. Packaging may combine transport;
it does not create a sound shared semantic root.

## 6. Capabilities enabled

The selected model enables these concrete capabilities without strengthening
their claims:

1. **Independent semantic interpretations.** A theorem prover, executable
   reference model, or checker in another language can interpret the specified
   Core algebra while canonical MLIR remains the sole production carrier.
2. **Multiple external and prover views.** Several Interfaces and Plans can be
   compared over one stable Protocol without changing verifier semantics.
3. **Several transcript constructions over one Core.** Each Fresh or FS
   Protocol receives its own identity and exact occurrence/prefix maps; an FS
   target can exist even when no supported security theorem is available.
4. **Late relation material and honest conflict.** Relation subjects can exist
   before bytes arrive. Later interpretation and exact negative disagreement
   can be recorded without invalidating either subject or claiming
   satisfaction.
5. **Occurrence-native composition.** Repeated children, independent/shared/
   derived/imported challenge policies, private randomness, bounded branching,
   early exits, and terminal combination can be expressed without graph-union
   ambiguity.
6. **Same intrinsic result from different histories.** Distinct normalization,
   Fiat--Shamir, or composition derivations may converge on one intrinsic target
   identity while their checked maps and provenance remain separate.
7. **Narrow later consumers.** Analysis, Compiler, Relations, and OIR can name
   exact read sets and refuse omitted bases rather than recreating a shadow
   Protocol or broad environment.
8. **Optional generative authoring.** Reusable modules and composition helpers
   can be researched later because they elaborate away before admission.

## 7. Costs and disciplines accepted

The selection deliberately accepts these costs:

| Cost | Required discipline |
|---|---|
| More subject, regime, and result IDs at APIs | Typed references, exact dependency manifests, and owner-specific admission make the added distinctions inspectable |
| More package assembly | Packages remain transport-only; every member is independently authenticated and admitted |
| A demanding authoring-to-canonical boundary | Lowering must produce exact typed side outputs and an audited information-loss account; diagnostics must explain refusals before erasure |
| A specification and conformance burden for the semantic algebra | Keep one production carrier and require independent models to state correspondence rather than gain authority by agreement |
| Larger FS and composition maps | Derive and directly check maps; exclude derivation history from intrinsic identity unless observable |
| Multiple domain checkers | Keep predicates with their semantic owners and share only genuinely common closure, regime, reference, and outcome machinery |
| Re-authentication after process boundaries | Treat serialized data as capability-neutral and optimize only with independently checkable, consumer-justified results |
| Exact-v0 evolution limits | Introduce cross-regime conversion or compatibility only for a named consumer and as an explicit relation between subjects |

These are architecture costs, not an implementation estimate. No claim is made
here about their concrete runtime, memory, engineering schedule, or migration
burden.

## 8. Alternative dispositions

### 8.1 Candidate A — rich representative plus semantic quotient

**Decision:** Reject as the v0 center. Retain only as the current-preserving
control for gap analysis.

Its strongest form can express many target scenarios, but every normative
consumer must be proved congruent with one projection and must never recover a
refusal-relevant distinction after erasure. It also fails the fixed Stage 1
physical-canonical-carrier gate unless that decision is formally reopened. A
closed representative with enough independent typed satellites converges toward
Candidate C while retaining quotient debt.

**Reconsider only if** physical canonicality is formally reopened and a finite,
reviewable quotient plus complete consumer read-set proof is materially simpler
than the closed carrier for all named consumers.

### 8.2 Candidate B — canonical multi-subject bundle

**Decision:** Reject as the v0 center. Permit ordinary transport packaging with
no semantic or authority effect.

A bundle is convenient for archival assembly, but Interface, Plan, Relations,
artifact observations, and checked results have independent identities,
lifecycles, and consumers. Bundle identity creates irrelevant churn; bundle
admission invites authority transitivity; and bundle evolution prepays a
compatibility surface without a named whole-package consumer.

In the strongest audited B control, only reusable non-occurrence subjects are
members. Occurrence-local private witnesses, artifact bytes, and artifact
observations remain outside the authoritative bundle; a transport envelope may
carry them without changing that boundary.

**Reconsider only if** a concrete independent consumer requires one retained
package, member identities remain independent, member admission cannot become
transitive, replay remains owner-specific, and measured benefit exceeds the
versioning and compatibility commitment.

### 8.3 Candidate D — typed event calculus as the center

**Decision:** Reject as the standalone v0 center; adopt its typed-event
technique inside Core.

Typed syntax, handlers, and simulations are valuable denotational tools, and
the equal-resolution D instantiation can reproduce the required domain schemas.
Its rejection is therefore a cost and authority decision, not an
expressiveness claim. Making D canonical would require zkc to standardize and
implement a calculus, total decidable normalizer, normal-form equality,
handler semantics, and executable simulation/adequacy layer in addition to the
domain-owned relation, Plan, outcome, and composition contracts. Those domain
contracts remain first-class in a sound D, so the generic center recreates C's
typed satellites while adding calculus and normalizer authority. No named v0
consumer justifies that burden. Generic handler adequacy still cannot
substitute for the exact domain predicates later consumers rely on.

**Reconsider only if** a finite first-order calculus gives simpler exact
schemas for all selected domain subjects, has total decidable normalization,
retains direct reviewability, and yields a named mechanization or consumer
benefit without moving authority into ambient handlers.

### 8.4 Candidate E — parameterized protocol modules

**Decision:** Defer to optional authoring research over Candidate C.

Generative modules could provide reusable protocol families, lifting,
composition templates, and typed parameter constraints. Making them semantic
authority in v0 would also require a new language, elaboration semantics,
termination and normalization rules, variance laws, reproducibility, and
diagnostics before the closed Protocol vocabulary is stable.

**Research trigger:** repeated real authoring patterns demonstrate that direct
workbench construction is error-prone or duplicative and a bounded module
language can elaborate deterministically to complete C-style outputs and maps.
That trigger starts authoring research; it does not by itself reopen the
admitted semantic center.

## 9. Contradictions resolved by the selected model

| Prior tension or conflict | Integrated resolution |
|---|---|
| Language-independent meaning versus MLIR leverage | The specification defines one abstract algebra; one closed bijective MLIR graph is the sole production carrier |
| Canonical semantics versus generic MLIR canonicalization or bytecode | zkc owns canonical semantic encoding and physical-graph authentication; generic MLIR mechanisms are tools, not the result predicate |
| Semantic codecs or functions identified by live implementations | Every algorithm-valued field is a closed finite term or content-addressed exact-ABI contract; executable/checker capabilities remain outside identity |
| One official Protocol artifact versus useful Core reuse | Canonical PIR has one `pir.protocol` root; `CoreId` is an authenticated embedded subidentity and later Core access is an attenuated view |
| Port direction present but the semantic input source or output sequence implicit | Each input occurrence is exactly `InputSource`; each output declaration names one canonical `OutputValues` sequence but creates no exposure or path-availability fact; Interface cannot repair either Core fact |
| Author labels erased from Protocol identity but later read by projection or relation code | External names and packaging move to an admitted `ProtocolInterface`; Protocol-only consumers cannot read representative labels |
| Embedded routes treated as both Protocol structure and prover strategy | Protocol owns abstract prover obligations; Plan owns construction routes; `PlanRealizes` checks coverage separately |
| Plan identity carrying runtime witness or supplier state | Plan identity includes only immutable semantic descriptions and requirements; live secrets, handles, credentials, capabilities, and occurrences remain runtime-local |
| One `RelationContract` acting as definition, interface, instance, artifact parser, binding, and authority | Relations splits these roles into independently owned subjects and named checks; no registry name supplies semantic authority |
| Artifact observations treated as agreement, and any failure treated as disagreement | Interpretation is expectation-free; comparison is a separate check; negative disagreement retains facts while malformed/refused/failed interpretation makes no observation |
| Structural correspondence confused with witness satisfaction or a cryptographic property | Structural and public-instance correspondence, `RelationSatisfies`, and property judgments have different inputs, owners, and outcome spaces |
| Core challenge meaning depending on a later FS construction | Core owns a construction-neutral potential action-occurrence prefix template for each challenge; a construction directly checks its action-wise image and runtime subsequence without changing Core meaning |
| Fiat--Shamir construction blocked on theorem availability | The target Protocol is constructed and admitted independently; `FSCompile` and property transport remain later judgments |
| `link`, graph union, and semantic composition used interchangeably | Authoring link may assemble proposals; semantic composition requires a complete local target fragment and independently admitted target plus exact maps |
| Composition-spec identity referring circularly to its own global occurrence IDs | The preimage uses local child slots and local target references; durable occurrence references are formed only after spec authentication |
| Derived or imported challenges represented as fresh target challenges | They map to explicit target values and exact `ObservePublicValue` events; no false fresh randomness or squeeze is invented |
| Dependency or obligation merge treated as an open composition policy | Dependencies use the deterministic least target-required reachable closure from exact child views plus disjoint authenticated local supplies; all obligation families are recomputed from the formed target and checked for exact equality |
| Child failure or early terminal behavior left to an executor | Total failure and reach-exit policies, exact suffix suppression, distinct `ExitStatusInjection`s into one common per-child sum, one-hot guarded merges, and one result-routed terminal combiner fix every behavior |
| Every verifier failure forced to terminate, or a continuation carrying an ambient payload | A closed occurrence-exact failure source selects terminating or status-continuing behavior; the only status payload is `{failure, class}` and exact values feed later guards/merges |
| Endpoint participation and prover value production sharing one obligation class | Endpoint obligations and prover obligations are distinct; only prover obligations originate values and carry a complete unique cause-indexed nonproduction family |
| Missing prover output represented as verifier rejection, Plan failure, or checker failure | Core execution yields exact `ProverDidNotProduce` with partial state; Protocol admission and verifier-terminal semantics remain unchanged |
| A negative semantic result, missing basis, refusal, malformed input, and checker crash treated as one error | Owner-specific qualified outcomes keep fact-bearing negatives separate from every absence-of-conclusion state |
| Stored IDs, signatures, bundles, or reports treated as portable authority | Authority is process-local and admission-gated; persistence stores claims and preimages for rechecking, never a live capability |
| FS composition context checked before a target Core exists or inherited from children | Composition first forms/sub-admits Core, then validates the exact construction context and context-port map inside target Protocol admission |

## 10. Stage 1 and Stage 2 compatibility

No inherited Stage 1 or Stage 2 decision is reopened by this convergence.

| Inherited decision | Stage 3 result | Reopening result |
|---|---|---|
| Protocol meaning is language-independent; MLIR is the primary v0 structural carrier, not semantic authority | Candidate C defines the algebra independently and keeps one canonical MLIR PIR representation | **Compatible; no reopening** |
| Rich authoring precedes a small closed physically canonical PIR level | C keeps authoring open and proposals unauthoritative while canonical PIR is finite, closed, normalized, and bijective | **Compatible; no reopening** |
| Core plus one challenge interpretation forms Protocol; Interface and Plan are dependent subjects | Stage 3 completes the fields, identities, and admission contracts without moving their meaning across boundaries | **Compatible; no reopening** |
| One total observable schedule and protected observations belong upstream | The typed-event model retains both causal structure and one total schedule and expands exact failure/terminal closure | **Compatible; no reopening** |
| Exact-v0 semantics fail closed and regimes qualify identity | Every target subject has an owner regime; unknown meaning and silent upgrade fail closed | **Compatible; no reopening** |
| Domain-owned typed contracts are the semantic baseline | PIR, Relations, Analysis, OIR, and later owners retain their predicates; shared machinery is descriptive and structural only | **Compatible; no reopening** |
| Capabilities are local, opaque, attenuated authority and do not serialize | Every Stage 3 subject and checked relation follows the same lifecycle and reset rule | **Compatible; no reopening** |
| Direct recomputation is preferred; producer/validator and persistence require named consumers | Identity, admission, FS maps, and composition maps are direct; theorem/model relations and durable results remain conditional on exact consumers | **Compatible; no reopening** |
| No global transition ID, universal fact root, universal checker, or bundle authority | C uses typed satellites and owner-specific results; neither maps nor packaging become a universal authority layer | **Compatible; no reopening** |
| Outcomes distinguish negative truth from unsupportedness, missing basis, refusal, malformed input, and operational failure | The Stage 3 owner-specific outcome algebra preserves all distinctions | **Compatible; no reopening** |

Candidate A would require reopening Stage 1 physical canonicality. Candidate B
as an official semantic bundle would require reopening the selected Protocol
root and Stage 2's no-universal-bundle and consumer-justified-persistence
discipline. Candidate D as the universal center would require evidence strong
enough to reopen domain-owned contract placement. Candidate E as admitted
meaning would reopen the authoring/canonical boundary. No such evidence was
found; therefore none of those reopenings is recorded.

## 11. Reversal triggers

The decision must be reconsidered if concrete evidence establishes any of the
following:

1. A credible bounded interactive protocol cannot be expressed without an
   ambient semantic read or without moving verifier-visible behavior into
   Interface, Plan, Relations, or host-language handlers.
2. The Core grows into a general optimizing language, or its admission checker
   must import most authoring, compiler, plugin, or backend machinery.
3. Two legal canonical PIR graphs under one regime denote the same semantic
   encoding beyond the explicitly allowed carrier trivia, or a required
   refusal-sensitive distinction must be erased before it can be checked.
4. A named independent full-Protocol consumer requires a non-MLIR production
   package under a concrete trust, release, retention, and compatibility
   contract that purpose-specific views cannot satisfy.
5. Interface or Plan substitution changes a result classified as depending
   only on `ProtocolId`, or no field placement can close both its producer and
   consumer read sets.
6. Relation correspondence cannot be stated over admitted Protocol and
   Interface views without redefining a Protocol-owned fact or importing hidden
   carrier, registry, or relation-owner authority.
7. The typed-satellite dependency graph creates an unavoidable authority cycle
   or forces one subject's admission to depend on a result that itself requires
   that subject's authority.
8. Composition cannot close every target Core family, total schedule,
   challenge and private-randomness policy, dependency, obligation, failure,
   terminal, or challenge-interpretation input for a credible required case.
9. A finite typed event calculus demonstrates an exact, materially smaller and
   more reviewable account of all selected domain subjects and outcomes without
   ambient handler authority or normalization ambiguity.
10. A named whole-package consumer demonstrates that independent member
    identities and admissions inside a canonical bundle have lower total cost
    and no authority transitivity or compatibility debt.
11. Purpose-specific views collectively recreate a complete second Protocol
    schema, showing that the one-carrier boundary no longer reduces authority
    or synchronization burden.
12. A later Stage 4 consumer supplies an exact counterexample showing that its
    narrow view omits a semantic input owned by Stage 3.

A trigger is evidence for a formal reopening review, not permission for an
ambient exception, generic metadata field, widened `valid` result, or silent
compatibility promise.

## 12. Deliberate deferrals and later-owner seams

The architecture fixes these seams while leaving the conclusions downstream:

| Deferred question | Exact Stage 3 export | Later owner |
|---|---|---|
| Semantic equivalence, refinement, distribution, and intentional change | Admitted Protocol/Core views, observer sets, exact regimes, maps, and qualified result signatures | Analysis |
| `FSCompile` and property-specific transport | Admitted source/target Protocols, transcript construction, event/challenge/prefix maps, model/theorem/assumption inputs | Analysis |
| Relation satisfaction and witness validity | Admitted definition/interface/instance plus occurrence-local private witness and explicit model/assumptions | Relations or Analysis under the exact future ownership decision |
| Property composition | Independently admitted child/target subjects, exact structural composition result, model, assumptions, and property question | Analysis |
| Compiler legality, optimization, and selection | Narrow admitted views and exact candidate relation inputs | Compiler and Analysis |
| OIR grammar, identity, local validity, and source-relative projection | Protocol, Interface, role, tagged Plan basis, and explicit `LocalOirValid`/`ProjectionCorrect` seam | OIR |
| Concrete Plan-field placement and provider binding | Plan semantic-class constraints and exact OIR/realization reader requirements | OIR and Realization |
| Endpoint support, deployment, invocation, and runtime occurrence | Admitted source/target subjects and separately owned live capabilities/configurations | OIR and Realization |
| Evidence, appraisal, retention, and reliance | Qualified domain results with exact inputs and residual-trust statements | Evidence and named relying consumers |
| Concrete semantic byte grammar, hash primitive, and test vectors | The selected injective preimage structure and domain separation | PIR carrier owner during Stage 7 normative consolidation; Stage 8 implementation conformance where applicable |
| Generative protocol modules | Closed C-style elaboration target, exact maps, and independent output admission | Optional future PIR authoring research |

Deferral means that Stage 3 has fixed the noncollapsible input boundary. It does
not preload an affirmative later result or permit the later owner to recover an
omitted Stage 3 input from ambient state.

## 13. Exact non-claims

This convergence does **not** establish or promise:

- activation of Stage 4A or Stage 4B, or permission to skip their separate
  activation decisions and entry contracts;
- normative authority for any temporary page;
- implementation correspondence, feasibility, completeness, or current code
  support for the selected target;
- an implementation sequence, migration plan, cost estimate, backward-
  compatibility window, or retained identity across semantic regimes;
- concrete MLIR operation spelling, byte grammar, hash primitive, serializer,
  checker API, or identity test vector;
- that every existing or future proof protocol can be represented in v0;
- relation truth, satisfiability, witness validity, or correspondence merely
  from a relation reference, artifact, binding, or admitted Protocol;
- soundness, knowledge soundness, completeness, zero knowledge,
  non-malleability, Fiat--Shamir security, or any quantitative bound;
- that structural composition preserves a property, is associative or
  commutative, or commutes with Fiat--Shamir;
- compiler preservation, optimality, backend correctness, OIR projection
  correctness, endpoint support, provider correctness, deployment success, or
  runtime availability;
- prover termination, honest-prover success, performance, cost, or secrecy
  merely from Plan admission or `PlanRealizes`;
- adequacy of any formal denotation, proof assistant, external theorem,
  transcript implementation, or cited system for the selected model;
- portable local authority, reliance, or truth from a persisted result,
  signature, provenance record, evidence item, package, or matching digest; or
- selection of a universal transition language, compatibility dialect,
  authoring module system, checker registry, fact root, certificate envelope,
  or canonical multi-subject bundle.

## 14. Completed durable promotion and handoff map

Stage 3.5 promoted the reviewed result into the self-contained target owners
below. “Promoted” means selected non-normative target design; it does not mean
normative cutover, implementation support, migration, proof, or runtime
authority. The [absorption record](absorption-record.md) accounts for every
temporary input and retained rationale at section resolution.

| Selected content | Completed destination | State |
|---|---|---|
| Integrated Protocol/Relations topology, architecture alternatives, costs, capabilities, non-claims, Stage 4 split, and reversal triggers | [Protocol and Relations Architecture](../../project/protocol-and-relations-architecture.md) | Promoted as the durable high-level Stage 3 decision |
| Shared construction ordering, local capabilities, qualified outcomes, persistence, and no-universal-transition rules | [Transition and Bridge Architecture](../../project/transition-and-bridge-architecture.md) | Existing durable cross-domain decision retained and referenced rather than duplicated |
| Exact Protocol candidate/authentication/admission/view/reset/replay lifecycle | [Protocol Semantic Model](../../pir/protocol-model.md) and [Canonical PIR](../../pir/canonical-pir.md) | Promoted into the new exact semantic and carrier owners; the superseded lifecycle sketch is not a Stage 3 destination |
| `InteractiveCore`, Protocol, ports and values, objects, randomness, events, claims, failures, terminals, obligations, execution, and admitted views | [Protocol Semantic Model](../../pir/protocol-model.md) | Promoted as a self-contained target semantic specification |
| Canonical MLIR PIR, one-root topology, semantic/carrier bijection, algorithms, ordered authentication, admission, information-loss frontier, and replay | [Canonical PIR](../../pir/canonical-pir.md) | Promoted as a self-contained target carrier specification |
| `ProtocolInterface`, `ProverPlan`, codecs, identities, admission, `PlanRealizes`, private ingress, exports, and placement constraints | [Protocol Interfaces and Prover Plans](../../pir/interfaces-and-plans.md) | Promoted as a self-contained target satellite specification |
| Transcript construction, Fresh-to-FS construction, contexts, prefix maps, semantic Core composition, total A/N checking, laws, and replay | [Fiat--Shamir Construction and Semantic Core Composition](../../pir/fiat-shamir-and-composition.md) | Promoted as a self-contained target construction specification |
| Relation ontology, dependencies, authoring ingress, binding, artifact interpretation/comparison, grounding, and satisfaction boundary | [Relation Model](../../relations/relation-model.md) | Promoted as a self-contained target Relations specification |
| Structural and instance correspondence questions, prerequisites, results, capabilities, replay, and downstream views | [Protocol Correspondence](../../relations/protocol-correspondence.md) | Promoted as a self-contained target correspondence specification |
| Domain navigation, authority routing, program state, and documentation inventory | [`docs-next/` index](../../README.md), [PIR index](../../pir/README.md), [Relations index](../../relations/README.md), [v0 Semantic Design Program](../../project/v0-design-program.md), and [Documentation Manifest](../../project/documentation-manifest.md) | Updated for the completed Stage 3 package and retained non-normative boundary |
| Analysis/Compiler inputs, exact deferred judgment signatures, property non-claims, and reopening rules | [Stage 4A entry contract](stage-4a-entry-contract.md) | Closed handoff; Stage 4A not activated |
| OIR/Realization inputs, Plan reader requirements, projection/local-validity split, endpoint non-claims, and reopening rules | [Stage 4B entry contract](stage-4b-entry-contract.md) | Closed handoff; Stage 4B not activated |

The promotion deliberately preserves separately reviewable owners. No summary
page, package, navigation index, or absorption record becomes a semantic root
or grants transitive authority to the promoted subjects.

## 15. Convergence conclusion

The integrated design decision is Candidate C: one small language-independent
Protocol algebra, one canonical bijective MLIR production carrier for Protocol
with embedded Core, and separately owned typed satellites. Candidate D
contributes the typed-event method without becoming the universal semantic
center. Candidate E
is reserved for an optional elaborating authoring layer. Candidates A and B do
not define the v0 center and no inherited decision is reopened.

The exact independent target, candidate/IR-transfer, scenario, matrix,
promotion, handoff, downstream-route, and documentation-exit gates in Section
2 are CLEAN. This closes the architectural choice, Stage 3.4 convergence, Stage
3.5 durable promotion and absorption, and the whole bounded Stage 3
design-research program on the recorded snapshots.

This closure does not make any promoted page normative, authorize
implementation or migration, activate Stage 4A or Stage 4B, or establish a
relation, security, compiler, endpoint, OIR, realization, or property claim.
Each such transition or result still requires its independently owned later
decision, operation, admission, or judgment.
