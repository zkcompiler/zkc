# K2 Protocol and Fiat--Shamir Research and Selection

> **Document kind:** Temporary research and selection record
> **Document state:** Integrated candidate preserved and narrowly reclosed;
> final gate evidence is owned by [`validation.md`](validation.md)
> **Provisional owner:** `pir`, coordinated by `project`
> **Authority:** None. Current normative Protocol and Fiat--Shamir rules remain
> under [`docs/`](../../../../docs/README.md).
> **Selection date:** 2026-08-26
> **Disposition:** Absorb the accepted semantics and necessary rationale into
> durable PIR owners, preserve exact executable nonclaims, then delete this page
> before cutover.

## 1. Verdict

Retain the central factorization:

```text
Protocol = InteractiveCore + ChallengeInterpretation
```

but replace most of the pre-K2 operational detail around it.

The selected Core is one finite, totally ordered declaration of verifier-
observable interaction. It has two protocol parties, Prover and Verifier;
public invocation values and public coins are typed external sources rather
than a third party. The Core fixes typed values, explicit Statement scopes,
prover decision points, verifier computations, challenges, standard effects,
claims, reductions, checks, and terminal closure. Its references point only to
earlier occurrences.

A prover trace is no longer an execution input. Online execution asks an
external strategy for one move at each current decision point through an exact
history-restricted interface. A completed run may then be replayed, but replay
alone grants no causal or adversary-model conclusion.

Fiat--Shamir is admitted only for a structurally public-reconstructible Core.
The transcript plan is derived from Core meaning. It cannot elect to omit a
Statement, proof message, oracle binding, or branch marker. The construction
supplies exact K1 algorithms and state types for initialization, framing,
absorption, squeezing, decoding, bounded retry, and completed failure. The
challenge namespace is derived from identified semantic occurrences rather
than trusted human labels.

This selection is a structural kernel, not a Fiat--Shamir security theorem.
Analysis must still establish the exact interactive property, adversary model,
random-oracle or quantum-random-oracle model, theorem hypotheses, and loss.

## 2. Why the prior target is insufficient

### 2.1 The factorization is sound; its execution contract was not

The pre-K2 target correctly separated a common `InteractiveCore` from Fresh
and Fiat--Shamir challenge interpretation. It also made transcript state and
composition explicit. Those decisions survive.

The following details do not survive:

- `ExecuteProtocol` consumed a complete `ProverTrace`; an early message could
  therefore be correlated with a future challenge while still replaying.
- `Message` could be authored as Wire-only even before a later challenge.
- transcript initialization accepted Context ports but had no faithful complete
  Statement-occurrence route.
- Fiat--Shamir admission did not derive public-coin eligibility.
- `SqueezeAndSampleRule` named the decisive state-to-challenge transition but
  did not define its state, inputs, output state, retry law, namespace, or ABI.
- `PublicEnvironment` mixed external public sources, a semantic role, and a
  projection obligation while endpoints contained only prover and verifier
  programs.
- canonical ROBDD guards placed a variable-order-sensitive exponential object
  in Core identity even though K1 now provides bounded portable Boolean
  algorithms.
- native oracle publication and query were absent; a Merkle-compiled FRI could
  be encoded as flat messages, but an IOP/IOR interaction could not be stated
  without erasing its oracle lifecycle.

These are missing laws and misplaced authority, not a contradiction in the
Core/interpretation factorization.

### 2.2 What the shipped system actually protects

The current authoritative kernel provides important non-regression pressure:

- E211 rejects an authored challenge dependency that was not absorbed;
- E212 keeps the generalized Frozen-Heart condition global across segment
  seams;
- E213 derives round-message prefixes from reduction contracts, including a
  Last-Challenge case that a flat "all earlier slots" rule cannot express;
- E214 requires each extant public binding before its segment's first
  challenge;
- E215 validates an identity-bearing segment decomposition while preserving one
  continuous transcript state across link; and
- E216 enforces collision-free authored challenge domains and rechecks them
  after composition.

K2 preserves the causal properties, not the exact flat-slot representation.
The shipped system does not generally prove that every application Statement
has a bind occurrence, positively classify public-coin eligibility, implement
a native oracle state machine, or establish the stated Binding Lemma. Those are
target obligations rather than already-shipped guarantees.

## 3. Research constraints

The source cases narrow, rather than dictate, the model.

| Source pressure | Constraint carried into K2 | Deliberately not copied |
|---|---|---|
| [CFRG Fiat--Shamir draft](https://datatracker.ietf.org/doc/draft-irtf-cfrg-fiat-shamir/) | Stateful absorb/squeeze; session and instance separation; complete instance before prover messages; canonical codecs; proof serialization distinct from transcript encoding | A Sigma- or fixed-I/O-only grammar; raw concatenation assumptions; an Internet-Draft treated as a universal theorem |
| [Weak Fiat--Shamir Attacks on Modern Proof Systems](https://eprint.iacr.org/2023/691) | The complete public statement must influence challenges; omission is a structural error, not a caller option | A finite list of vulnerable fields used as the definition of Statement completeness |
| [Multi-Round Fiat--Shamir](https://eprint.iacr.org/2021/1377) | Challenge inputs are cumulative prefixes; theorem coordinates and losses vary with round structure and special-soundness hypotheses | A claim that every admitted multi-round Core inherits the paper's result |
| [Interactive Oracle Proofs](https://eprint.iacr.org/2016/116) | Round-indexed immutable oracle publication, later random-access query, public-coin interaction, and state-restoration as a separate analysis concern | Merkle commitments conflated with logical oracle publication; one trace treated as an adversary |
| [Fiat--Shamir Security of FRI](https://eprint.iacr.org/2023/1071) and [IOP soundness notions](https://eprint.iacr.org/2023/1256) | Public-coin and round-by-round hypotheses are theorem inputs, not consequences of a transcript hash | RBR, special soundness, knowledge soundness, ROM, and QROM collapsed into one property subtype |
| [Last Challenge Attack](https://eprint.iacr.org/2024/398) | A challenge cannot precede prover material that its exact round/reduction contract requires | A blanket rule that every response must precede every challenge |
| [Wizard-IOP](https://eprint.iacr.org/2022/1633) | Round-indexed columns/publications, coins, queries, visibility, and protocol compilation are useful first-class coordinates | Callbacks, `any` payloads, mutable transcript state, insertion-order identity, or skip flags as semantic authority |

The current CFRG draft defaults to an infallible oversqueeze-and-reduce mapping
for its supported challenge types. K2 keeps that as the simplest construction
but also permits an explicitly bounded rejection decoder. Squeeze itself is a
total state transition. Exhaustion belongs to the decoder and never rolls back
state. Grinding is not a sampler retry: it is a prover search followed by one
published witness and a verifier check.

## 4. Selected semantic stack

```text
K1 authenticated regime, values, algorithms, failures, evaluation control
                              |
                              v
                 AuthenticatedInteractiveCore
                              |
                     PIR structural admission
                              v
                       AdmittedCore
                       /          \
        FreshInterpretation       AdmittedTranscriptConstruction
                |                              |
                v                              v
       AdmittedFreshProtocol          AdmittedFSProtocol
                \                              /
                 \-- CheckedFSConstruction --/
                              |
                 strategy-generated execution
                              |
                    completed RunRecord
                              |
               replay / PIR-owned source views
                              |
           K3 Relations, Analysis, and OIR questions
```

`CheckedFSConstruction` establishes exact structural correspondence over one
literal `CoreId`. It establishes no cryptographic property. A BCS or another
IOR-to-argument construction may create a different Core and needs its own
checked relation before this same-Core FS step.

## 5. Interactive Core

### 5.1 Identity and order

`InteractiveCore` is an ordinary K1 regime-qualified semantic subject. Its
canonical body contains exact used module dependencies, typed declarations,
explicit scope openings, and one total occurrence sequence. Author labels,
filesystem paths, MLIR operation names, compiler routes, plans, and evidence do
not enter the body.

The total order is semantic because it determines visible history, legal
strategy input, transcript state, challenge prefixes, failure precedence, and
terminal selection. K2 does not quotient commuting occurrences. Analysis may
later prove two differently identified Cores equivalent under an explicit
observation question.

References in values, guards, claims, and occurrences point only backwards.
The schedule therefore supplies its own acyclic execution order; a redundant
authored causal-edge graph is not part of Core identity.

### 5.2 Parties and sources

The v0 Core has exactly one Prover and one Verifier. A public environment is
not a third interacting party:

- public Statements and context arrive through the invocation;
- Fresh challenges arrive through an explicit public-coin source; and
- Fiat--Shamir challenges arrive through an admitted transcript construction.

This matches the abstract two-party proof while preserving the provenance of
public data. A multi-prover protocol whose provers can be treated as one joint
strategy is representable through that strategy. Protocols whose security
depends on independent, noncommunicating provers or distributed verifiers need
a new supported role module and regime-qualified semantics; K2 does not erase
that distinction by pretending the parties are ordinary labels.

### 5.3 Inputs and explicit scopes

Public input occurrences have one of three PIR-owned roles:

```text
Statement | SessionContext | PublicParameter
```

Every occurrence has an exact K1 value type and one explicit scope. A Statement
may be an invocation value or a public value derived before its scope opens.
Session context prevents cross-application or cross-session confusion. A
runtime public parameter that affects verifier behavior is bound like other
public instance material; static parameters belong in the Core or construction
identity.

Scopes form one finite rooted tree. The root opens before the first occurrence.
A child names its parent and an exact boundary before a later occurrence. A
scope opening is deterministic and identity-bearing. It binds the scope path,
all Statement occurrences in that scope, and its declared public context before
any challenge in that scope. Challenges inherit every ancestor binding.

This represents sequential composition without allowing an unmarked adaptive
statement inside an active scope. The transcript state remains continuous
across scope openings. A future statement may be derived from earlier public
protocol output, but it is fixed and bound at the child opening before that
child's first challenge.

Private witnesses, prover advice, private randomness, and implementation state
are not verifier-observable Core values. They enter an external strategy or a
separately identified Interface/Plan. K3 must distinguish Witness from private
nonwitness material without placing concrete secrets in `CoreId`. A verifier-
private input may occur in a general interactive Core, but any influence from
it makes the Core ineligible for this Fiat--Shamir construction.

### 5.4 Values and guards

Core values are public inputs, canonical constants, messages, challenges,
oracle answers or bindings, check results, and results of exact K1 portable
algorithms over earlier available values. An occurrence guard is an admitted
K1 Boolean algorithm plus exact earlier operands. It is evaluated once at its
boundary.

There is no identity-bearing ROBDD. K2 accepts intensional algorithm identity:
two extensionally equal guards may give different Core IDs. Semantic guard
equivalence is an Analysis question. K1's term and evaluation bounds prevent an
unbounded guard language or hidden solver.

### 5.5 Base effects and oracle module

The base v0 occurrence algebra contains:

```text
ProverMessage
DeterministicVerifierMessage
Challenge
InvokeCheck
ReachTerminal
```

The standard oracle module adds:

```text
PublishOracle
QueryOracle
AnswerOracle
```

Publication fixes one finite immutable logical oracle before any dependent
challenge or query. A query names that oracle and an exact in-domain point; an
answer is determined by the published object and cannot define or mutate it
retroactively. Visibility is explicit. The ideal oracle is distinct from a
commitment root, an authentication path, and a BCS lowering.

An FS-eligible concrete committed-oracle Core may expose the binding value as
the transcript material and check every answer/opening against the earlier
publication. Whether that binding is computationally adequate is an Analysis
or construction theorem obligation, not a structural assertion hidden in the
event kind.

Additional event kinds are introduced only by exact-used K1 semantic modules.
An evaluator admits a Core using such a module only when it supports the
module's complete formation, transition, visibility, influence, and replay
laws. An unknown constructor is `Unsupported`; a generic opaque effect cannot
claim transcript or verifier semantics.

## 6. Causal execution and replay

### 6.1 Strategy-generated execution

Each active prover occurrence creates one decision point. The Core derives an
exact `ProverView` from values and occurrence receipts visible to Prover before
that point. An external strategy transition has the mathematical shape:

```text
StrategyStep(private_state, ProverView, private_randomness)
  -> (legal_move, next_private_state) | Stop
```

The strategy receives no complete invocation object, future public coin,
future transcript state, verifier-private value, ambient registry, clock, file,
or mutable Core handle. A host capability implementing this interface must
record every read against the current view. Analysis later quantifies over
strategy classes and adversaries; PIR owns only the legal decision coordinates,
visible history, move grammar, and run relation they require.

`Stop`, unavailable strategy code, exhausted implementation search, or failure
to produce a legal move is qualified operational noncompletion. It is not an
intrinsic verifier terminal and not a second `ProverDidNotProduce` semantic
plane. A protocol that wants an explicit prover abort must represent a public
message and terminal behavior.

### 6.2 Replay

A completed `RunRecord` contains the invocation identity, exact interpretation,
occurrence decisions, public coins or derived challenge receipts, oracle
receipts, checks, transcript state commitments where applicable, and terminal.
Replay re-executes those decisions and refuses the first malformed, unavailable,
or illegal occurrence according to one identified K1 evaluation contract.

Replay proves that one record follows the declared transitions. It does not
prove that the record was generated without future information, that a sampler
followed a distribution, that a prover belongs to an adversary class, or that a
rewinding/state-restoration theorem applies. A strategy-generated record carries
the stronger provenance that the engine exposed only current views; a raw
replay record does not acquire it.

Removing whole-trace binding also removes the pre-K2 five-way prover-binding
failure rank. Malformed carriers fail before replay; at a live decision, one
move is checked in fixed structural/type/legality order; absence is
noncompletion. There is no need to choose a semantic winner among early,
duplicate, failed-randomness, missing, and late records that no longer form the
execution input.

## 7. Public-coin eligibility

`PublicCoinEligible(Core)` is a derived PIR predicate. The durable model now
computes it over one finite, canonically ordered dependency graph containing
inputs, derived values, scope/binding observations, occurrence activity and
outputs, claims/reductions, terminals, and exact module control/output nodes.
There is no authored `publicly_recomputable` field. The predicate requires:

1. every prover-visible nondeterministic Verifier value to be an explicit
   Challenge occurrence;
2. each Fresh challenge law to depend only on its admitted distribution and
   earlier public coins named by an explicit joint group, never on prover
   material or verifier-private state;
3. every deterministic verifier-to-prover message to be produced by an exact
   public K1 algorithm over public invocation values and prior public history;
4. every acceptance-relevant verifier computation, query point, check input,
   and terminal decision to be reconstructible from public invocation values,
   prover publications, oracle answers, and challenges; and
5. no verifier-private input, randomness, hidden query, or ambient value to
   influence an FS-relevant value or control decision.

Fresh execution consumes exact public coins from a source with the declared
law. The semantic distribution is a mathematical contract; source failure is
operational noncompletion. Fiat--Shamir execution replaces the same Challenge
occurrences with deterministic transcript transitions. The event coordinates,
value uses, claims, checks, and terminal behavior remain one literal Core.

## 8. Derived strong-FS structure

### 8.1 Required influence

The Core and its standard modules derive `RequiredInfluence(c)` for each
challenge occurrence `c`. It includes:

- construction, Core, application, session, and active-scope identity material;
- all Statement occurrences in the active scope ancestry;
- every active prover-controlled message before `c`;
- every active oracle publication or public binding before `c` on which `c` or
  a later checked reduction depends;
- every prior challenge in the same continuous transcript;
- exact query/answer material when it occurs before and influences `c`; and
- typed occurrence or skip framing whenever a conditional path would otherwise
  make two different histories encode identically.

Round/reduction contracts can add a semantically required earlier publication
even when ordinary value dataflow does not expose it. This retains E213's
important distinction. A Schnorr response after its only challenge is legal;
a PLONK or KZG message required before a later batching challenge is not.

No event owns a `Transcript` Boolean. Standard occurrence semantics derive its
transcript action. A supported extension module must define the same influence
law for each new constructor. The independently checked runtime law is exact
full-prefix equality:

```text
TransitionInputLog(actual before c) = DerivedPrefix(c)
```

`RequiredInfluence(c)` is then the exact ordered projection used to explain and
audit why that prefix contains every Core-required source. Safe extra influence,
such as explicit session context, is permitted because it is already part of
the derived full prefix. Missing, late, duplicate, reordered, wrongly scoped,
type-incompatible, or conditionally ambiguous source material either prevents
the required projection from being derived or breaks full-prefix equality; the
projection is not a second independent runtime rejection after equality passes.

### 8.2 Prefix and framing

The runtime transcript is one fold over:

1. construction initialization;
2. root-scope binding;
3. every active derived action in Core schedule order; and
4. each child-scope binding at its exact opening boundary.

Each frame commits to an action tag, semantic occurrence reference, K1 value
type, payload length, and canonical payload. Scope paths and challenge
occurrences are typed coordinates, not concatenated display labels. Inactive
conditional occurrences emit an exact skip frame when their absence can affect
later public control flow. An empty payload cannot alias a skipped event.

The required prefix is recomputed; it is not stored as an authoritative map.
A stored cache or witness is checked byte-for-byte against the derivation and
does not enter Core meaning independently.

## 9. Transcript construction and challenge transition

An admitted `TranscriptConstruction` is a K1 subject scoped to one exact
`CoreId`. It contains exact references to:

- transcript-state and byte value types;
- initialization and typed framing algorithms;
- total state-passing absorb and squeeze algorithms;
- one challenge decoder/sampler rule per admitted challenge type;
- exact static application domain material;
- a `BindConstructionSelfId` initialization instruction;
- deterministic K1 evaluation contracts and bounds; and
- the supported standard effect modules whose transcript rules it implements.

Initialization binds the hash/sponge suite, `CoreId`, resolved construction
identity, application domain, session schema, framing law, and root scope. A
literal self ID is not stored inside its own preimage; the instruction resolves
the already-authenticated `TranscriptConstructionId` at execution.

For challenge occurrence `c` and draw ordinal `i`, the namespace is derived
from:

```text
(TranscriptConstructionId,
 CoreId,
 active scope path,
 ChallengeRef,
 challenge domain and value type identities,
 explicit shared-coin group or independent-draw identity,
 i)
```

Two challenges share a draw only through one explicit group occurrence with a
compatible joint law. Otherwise their derived namespaces cannot collide.
Composition reruns admission on the new Core and its scope paths. Repeated
human-readable names carry no authority.

One transition is exact without asking one K1 algorithm to return a
heterogeneous product or sum:

```text
bytes = SqueezeBytes(state, namespace, requested_length)
require OctetLength(bytes) = requested_length
post_state = AdvanceState(state, namespace, requested_length, bytes)

accepted = Accept(bytes, public conditional inputs)
if accepted:
  challenge = Decode(bytes, public conditional inputs)
else:
  retry from post_state
```

All four algorithms have one exact K1 success type and empty failure rows. An
infallible rule accepts its one draw. For a rejection rule, the FS owner runs a
finite loop of K1 evaluation requests; every attempt advances state before
acceptance is tested.
Exhausting the admitted draw count completes with one exact, module-owned
`SamplingExhaustedFailure`. It never returns a partial challenge or restores a
pre-squeeze state. A successful squeeze with the wrong exact byte length is an
owner-qualified refusal before state advancement; provider disagreement is a
checker failure rather than a semantic sampling result.

Grinding is separate:

```text
Prover searches private candidates
  -> publishes one nonce/witness
  -> verifier applies an exact predicate to prior challenge + witness
  -> ordinary check and terminal behavior
```

Search exhaustion is strategy/Plan noncompletion. A supplied invalid witness is
a failed verifier check. Neither is `SamplingExhausted`.

## 10. Claims, reductions, and terminal closure

K2 retains claims and reductions as typed Core structure rather than replacing
them with generic checks:

- a Claim has an exact contract, scope, source, and linear or reusable usage;
- a Reduction occurrence consumes exact live input claims, cites exact required
  challenge and publication occurrences, and produces exact output claims;
- a Check may discharge exact claims under its contract but does not establish
  any cryptographic theorem merely by existing; and
- every accepting terminal requires all linear claims consumed or discharged,
  all required reductions saturated, and all terminal checks resolved.

A reduction cannot name a future challenge. A publication required by a round
or reduction records its mechanically checked least following required
challenge, or `None` only when it follows the reduction's last required
challenge. The former must influence that challenge even if ordinary dataflow
does not expose the role; the latter admits a genuine final response such as
Schnorr's. Every prover publication in the reduction side-input dependency
closure must appear exactly once. This is the K2 structural form of
Last-Challenge closure. K3 defines relation correspondence and Analysis
property meaning over these exact coordinates.

The final schedule occurrence is an unconditional fallback terminal. Earlier
guarded terminals stop execution. This gives finite operational closure without
requiring a theorem prover to establish guard exhaustiveness.

## 11. Composition, repetition, and extensions

Canonical Core composition creates and admits a new finite Core. Child
occurrences receive exact semantic scope paths; statement binding reopens at
each declared child scope, while the transcript state and earlier required
influence remain continuous. `CoreId` already commits to the complete composed
semantics. Authoring lineage and `CoreCompositionSpecId` are not separately
hashed into challenges. Two authoring routes that normalize to one exact Core
are intentionally replay-compatible; applications requiring separation use an
identified application/session domain.

V0 repetition is finite unrolling. A bounded template or loop is a workbench
authoring mechanism and must lower before Core authentication. Recursive proof
verification is one finite message/check interaction, possibly supplied by an
exact supported extension module. It does not recursively execute an ambient
child Core or import its authority. Dynamic schedules, unbounded recurrence,
noncommunicating multiprover semantics, verifier-secret FS, and unknown effects
are explicit unsupported boundaries.

## 12. Decision matrix

| Question | Selected answer | Why | Reversal trigger |
|---|---|---|---|
| Fresh/FS relationship | Same literal admitted Core; distinct Protocol IDs; checked structural construction | Keeps interaction meaning fixed while challenge realization varies | A real protocol requires verifier-observable event/value differences that cannot live in a separate prior construction |
| Statement scope | Explicit finite rooted scopes with deterministic openings and continuous transcript state | Supports composition-derived statements without unmarked adaptive introduction | A protocol needs a statement chosen inside an active scope after its first challenge with a theorem that justifies it |
| Transcript participation | Derived from typed Core and extension meaning | Authored flags recreate weak-FS and Frozen-Heart holes | A supported event has a proof of non-influence that cannot be represented as a typed semantic module rule |
| Execution | History-restricted strategy generation; replay is secondary | Exposes the interface required for adversary quantification and blocks future reads by construction | A primary theorem requires a different visible-history coordinate that this view cannot export |
| Party model | One Prover and one Verifier; public data/coins are sources | Removes a role with no endpoint while preserving provenance | A selected v0 family depends on independent multiple provers or distributed verifier knowledge |
| Prover nonproduction | Operational noncompletion outside Core terminal semantics | Absence of a move is not a verifier-observed cryptographic result | A consumer demonstrates an intrinsic protocol distinction not expressible by explicit abort message/terminal |
| Oracle layer | Standard first-class immutable publication/query/answer module; BCS separate | Preserves IOP/IOR meaning and prevents openings from defining the oracle retroactively | The K4 native FRI/IOR pair cannot state its exact lifecycle or creates unavoidable duplicate authority |
| Guard representation | K1 portable Boolean algorithm over earlier values | Bounded and executable without ROBDD order explosion | A required guard predicate cannot inhabit K1 without a general VM or unacceptable cost |
| Schedule | Exact total semantic order | Visible history and transcript depend on it | A real family requires scheduler nondeterminism as protocol meaning rather than an Analysis equivalence |
| Challenge namespace and reuse | Namespace derived from semantic occurrence; correlation uses a joint group; reduction-level sharing reuses one ChallengeRef under an explicit use policy | Composition-safe and independent of human names without turning equal domains into equal draws | A protocol requires cross-occurrence coin equality or reuse not expressible by one occurrence, a joint law, or the sharing policy |
| Sampling | Total squeeze; one-shot total decode or explicit bounded retry with advancing state and typed exhaustion | Closes the state/value ABI and prevents hidden rollback | A required exact distribution needs unbounded rejection; it must then be unsupported or use a different exact construction |
| Grinding | Prover search, publication, verifier check | Search is not random-challenge decoding | A protocol demonstrates a grinding step whose selected witness is verifier-generated rather than prover-controlled |
| Composition context | Semantic composed Core and scope path only; provenance excluded | Core identity already binds meaning, while authoring history should not change proofs | Two equal Cores need security-domain separation that application/session identity cannot state |
| Repetition/recursion | Finite unrolling; recursive verification as finite typed check/extension | Keeps Core bounded and verifier-observable | K4 requires a symbolic recurrence in canonical meaning to avoid infeasible or semantically lossy expansion |
| Extension model | Exact-used supported K1 semantic modules; unknown constructors refuse | Adds local vocabulary without rotating unrelated subjects or admitting opaque effects | Module extraction creates ambiguous constructor ownership or unverifiable transition semantics |

### 12.1 Narrow exactness amendment

The post-selection exactness review did not reopen the selected architecture.
It found two local canonical-body contradictions: the Fiat--Shamir Oracle answer
frame was typed at the element type even though Core execution produces the
total `OracleLookupResultType`, and the guard-outcome body admitted a second
Boolean spelling beside the exact K1 Boolean datum. The repaired bodies use the
Core lookup-result type and the single K1 Boolean representation. No Core,
Protocol, Fresh/FS, execution, public-coin, Oracle-lifecycle, or namespace
factorization changed.

Because those body repairs change exact `FrameOctets`, this reclosure
supersedes the earlier unshipped K2 candidate law. No earlier target byte stream
is supported or reinterpreted. A concrete semantic module or regime frozen from
the earlier draft would have to rotate before admitting the repaired law.

The same pass tightened the common transcript-byte ceiling to `2^20 - 26`,
including K1's byte-datum and tagged-success envelopes, and bound construction,
Protocol, generation, and replay handles to one retained evaluator identity.
It also closed replay over terminal and typed interpretation-failure records.

The review also narrowed the claim made for ordered influence. Exact full-prefix
equality remains an independently checked execution and replay law. Because the
required-influence sequence is derived as an ordered projection of that exact
prefix, it is an exported audit and admission view rather than a second
independent runtime gate. This removes an overstated evidence claim without
weakening transcript closure.

Finally, the selected construction intentionally does not carry the current
system's theorem-priced relaxation for an unabsorbed prover slot before a later
challenge. K2 absorbs every active prior prover-controlled publication. A
protocol that needs the relaxation must identify a distinct checked prior
construction or introduce a new supported construction whose assumptions,
scope, and quantitative consequence are explicit. A theorem or Analysis result
cannot mutate the already checked K2 transcript. Inability to express such a
justified construction reopens only the Fiat--Shamir construction cone.

## 13. K1 and downstream ownership

K2 reuses, rather than redefines, K1 canonical values, typed content IDs,
semantic modules, portable algorithms, derived function types, typed completed
failures, and evaluation contracts. PIR owns Core-specific value roles,
occurrence types, influence, admission, public-coin eligibility, execution,
replay, and structural construction judgments.

K3 must consume the following frozen seams without adding Protocol meaning by
backflow:

- Relations: Statement occurrence/scope table; a separate Interface surface
  for Witness and private advice; claim and reduction coordinates;
- Analysis: exact public history, legal strategy move interface, public-coin
  fact, transcript declaration, challenge transitions, oracle lifecycle, and
  loss occurrences;
- OIR: role projections, public inputs, messages, oracle effects, checks,
  failures/noncompletion boundary, terminals, and optional Plan requirements.

These are source declarations and open read seams, not prevalidated
correspondence. K3 must first reconcile the pre-K2 Interface/Plan, canonical
carrier, and Analysis source bindings; check that an external relation's full
Statement set maps to the exact PIR bindings; distinguish Witness from private
nonwitness advice; and define the strategy, theorem, loss, and minimum OIR
questions over the resulting views. Nominal claim/reduction coordinates and
module-declared dependency facts do not acquire theorem meaning or semantic-
honesty evidence by being present in K2. A consumer need for new verifier-
observable behavior or identity-bearing source data reopens the affected K2
cone; an ordinary consumer proposition remains owned by K3 without backflow.

K4 must still test native FRI/IOR, Sumcheck/GKR, polynomial commitments,
pairing and IPA arguments, folding/recursion, and recent variants at their
assigned strengths. K2's oracle fixture is a model discriminator, not portfolio
completion.

## 14. Exact nonclaims

The selected structural rules do not prove:

- soundness, knowledge soundness, completeness, zero knowledge, simulation
  extractability, RBR soundness, state-restoration soundness, or special
  soundness;
- applicability or loss of any ROM, QROM, correlation-intractability, BCS,
  Merkle-binding, polynomial-commitment, or recursive-proof theorem;
- that a concrete hash, sponge, codec, sampler, oracle commitment, prover,
  verifier, or endpoint implements an admitted K1 algorithm or contract;
- that strategy source code has no side channel beyond the capability model;
- protocol-family completeness, production feasibility, constant-time behavior,
  or implementation migration; or
- that two differently identified guards, schedules, Cores, or constructions
  are semantically inequivalent.

Executable validation can establish only the exact finite formation,
admission, transition, identity, and negative-boundary behavior its fixtures
exercise.

## 15. Promotion conditions

Promote this selection only after the frozen K2 exit gate is green. The durable
specification must contain every selected law without depending on this note;
the evaluation package must name its independent surface and limitations; the
pre-K2 target pages must visibly defer to the new owner where they conflict;
and one final cold pass must find no undefined formation, comparison,
transition, resource, or failure symbol on the K2 path.
