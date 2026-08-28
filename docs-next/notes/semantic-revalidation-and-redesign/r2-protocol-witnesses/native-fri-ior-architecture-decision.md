# Native FRI/IOR Provisional Architecture Decision

> **Kind:** Temporary candidate comparison and constructive decision
> **State:** Provisional; selected for executable falsification
> **Authority:** None. The decision may be reopened by the witness, independent
> reconstruction, cross-domain reconciliation, or external review.
> **Basis:** [Native FRI/IOR Source Dossier](native-fri-ior-source-dossier.md)
> and [Native FRI/IOR End-to-End Validation
> Plan](native-fri-ior-validation-plan.md)

## 1. Decision in one view

Use four semantic subjects and three checked constructions:

```text
Native logical FRI IOR Core
  - fixed logical oracles
  - fresh public fold coins and an ordered query-occurrence vector
  - direct logical queries and answers
  - fold and terminal decision semantics
                 |
                 | CheckedOracleCommitmentCompilation
                 v
Committed FRI Core
  - ordered caps
  - fresh public fold coins and an ordered query-occurrence vector
  - proof-supplied opened fibres and salts
  - authentication, fold, terminal, and decision checks
                 |
                 | CheckedGrindingAugmentation
                 v
Work-augmented committed FRI Core
  - the committed interaction above
  - a post-terminal work-seed challenge
  - one nonce publication and deterministic work check
  - query randomness only after valid work
                 |
                 | CheckedFSConstruction (same augmented Core)
                 v
Work-augmented committed FRI Fiat--Shamir Protocol
  - identical augmented committed interaction
  - coins derived by one exact transcript profile
```

The source and committed Cores have different identities because commitment
compilation changes verifier-observable messages and capabilities. Adding the
work challenge, nonce publication, and check is another Core-changing
construction because original FRI has no such rejection path. The Fresh and
Fiat--Shamir forms of the final work-augmented Core share one Core identity
because only challenge interpretation changes.

Relations grounds the initial oracle statement, construction inputs, caps,
and selected run occurrences. Analysis alone owns security transport across
the three arrows.

## 2. Alternatives compared

### 2.1 One `PublicBinding` Oracle Core for every form

This alternative keeps the current oracle carrier and models each public cap
as the result of its binding algorithm. Native, committed Fresh, and
Fiat--Shamir executions would all use that one Core.

It is attractive because it minimizes new vocabulary and makes root equality
executable. It fails two source boundaries:

1. native oracle publication becomes a cryptographic commitment rather than
   logical access; and
2. public replay of a committed proof requires the confidential full oracle so
   that the engine can recompute every answer.

The second failure is decisive. A committed verifier must authenticate proof-
supplied openings; it does not receive the complete prover oracle as a replay
capability. This alternative would move semantic authority into an evaluator
with more information than the protocol verifier.

**Classification:** modeling workaround with semantic loss; rejected.

### 2.2 Publish full canonical oracles in the native Core

This avoids choosing a commitment and lets existing query effects operate.
It discloses every oracle entry to the verifier, changes the verifier view and
work, destroys the oracle-access abstraction, and makes query complexity
semantically irrelevant.

**Classification:** semantic loss; rejected.

### 2.3 Distinct source and target Cores with a checked compilation

The native Core owns logical access. The target Core owns exactly what the
committed verifier sees. A typed construction relates their schedules, values,
and decisions without asserting a security theorem.

This introduces a real construction object and more correspondence work, but
it preserves both verifier models and permits public-only target replay. It
also accommodates a later compiler with different roots, caps, salts,
multiproofs, or terminal handling without redefining native FRI.

**Classification:** conservative semantic completion; selected.

### 2.4 A new universal interaction skeleton above Core

This alternative would factor a protocol-neutral oracle/query skeleton and
make native and committed interactions realizations of it. It could eventually
serve several oracle protocols, but the current evidence does not identify a
stable law that is both more informative than a checked construction and less
general than another universal transition algebra.

The new abstraction would also postpone the concrete question: which values,
views, and failures belong to each verifier. A checked source-to-target
construction is sufficient and reversible.

**Classification:** capability expansion without present justification;
deferred.

### 2.5 Hide all FRI behavior in a module effect

An exact owner module is appropriate for field, domain, fold, tree, and
terminal algorithms. It is not appropriate for replacing the standard message,
challenge, check, terminal, and oracle lifecycles with one opaque action. That
would prevent shared transcript, strategy, correspondence, and evidence laws
from inspecting the very boundaries under test.

**Classification:** owner-local algorithms selected; opaque lifecycle
rejected.

## 3. Required semantic extensions

### 3.1 Logical oracle access mode

Add an oracle publication meaning whose result is fixation and restricted
query access, not a public canonical carrier or cryptographic binding:

```text
OraclePublicationMode += LogicalAccess {
  domain_law: ProtocolDeclarationRef<"pir.oracle-domain-law">
}
```

`PublishOracle` remains an occurrence and fixation boundary. It has no public
value purporting to bind the carrier. Public query positions and answers may
still become exact observations when the protocol declares them public.

An active `LogicalAccess` oracle affecting an accepting sink is not directly
same-Core Fiat--Shamir eligible. A checked commitment compilation must first
produce a Core whose prior prover material has public transcript influence.

The finite Python witness uses a trusted evaluator that stores the complete
finite carrier so that it can check exact-domain formation and answer selected
queries. Its public observation and query operations omit the unqueried
entries, but the host-language carrier does not enforce noninterference. The
witness therefore validates observation discipline, not verifier capability
isolation. A durable runtime claim requires owner-side carrier admission to
issue an exact-domain query handle whose verifier view exposes metadata and
selected answers only.

### 3.2 Oracle origin and supply

Distinguish invocation-supplied and strategy-supplied oracle material:

```text
OracleOrigin = InitialOracle | ProverOracle
```

- `InitialOracle` is supplied once by an exact invocation capability before
  execution and activated at its publication occurrence. It is not a prover
  decision.
- `ProverOracle` is supplied through the causal strategy relation at its
  publication occurrence.

Both are immutable after fixation. A relation binding can ground the initial
oracle to one exact `OracleStatement` material occurrence. Equal values do not
turn a later strategy oracle into the initial subject.

### 3.3 Ordered query-occurrence vector

The Core owns the exact value consumed by its verifier: one ordered vector of
four domain indices sampled with replacement. It does not own a byte seed.
Repeated positions remain distinct vector occurrences.

The Fresh interpretation samples the vector directly from verifier public
coins. The Fiat--Shamir interpretation may derive a construction-internal
query seed and expand it deterministically, but its result resolves the same
Core-owned vector. Seed derivation and expansion belong to the challenge
interpretation and transcript plan rather than to native FRI semantics. Any
claim that the two sampling experiments have the required distribution or
security relationship remains an Analysis proposition.

### 3.4 Exact-domain law

The standard finite carrier remains useful for partial lookup protocols. FRI
adds an owner-local law declaring an exact finite domain and total answer:

```text
OracleDomainLaw = {
  domain_enumerator,
  domain_size,
  exact_entry_order,
  answer_projection
}
```

Admission derives the expected index sequence and checks that the carrier has
every and only those entries. Missing, duplicate, extra, or reordered entries
refuse before execution. The FRI profile's answer is the declared element, not
an accepted `Absent` variant.

This is not a general “totality evidence” Boolean. It is an exact algorithmic
law with a bounded evaluator contract.

### 3.5 Checked oracle-commitment compilation

Introduce a PIR-owned structural construction:

```text
CheckedOracleCommitmentCompilation {
  source_protocol,
  target_protocol,
  profile,
  oracle_publication_map,
  coin_map,
  query_occurrence_map,
  answer_opening_map,
  decision_map,
  checked_commutation
}
```

The profile fixes:

- logical value codec and leaf/fibre layout;
- commitment advice type and ownership;
- cap/root construction and order;
- query normalization and occurrence-to-opening selection;
- opening payload, salt, path, and authentication algorithms;
- source-answer extraction from a verified opening;
- terminal treatment; and
- intrinsic syntax and algorithm bounds.

Admission checks complete source and target coverage, type equality or an
explicit value relation, causality, target public replay sufficiency, and exact
commutation of the selected finite algorithms. It never accepts an authored
`corresponds` flag.

The result proves only structural and deterministic correspondence for its
named profile. Commitment binding, hiding, extractability, IOP soundness, and
property transport remain Analysis propositions. Request-local evaluation
limits and measured work belong to the validation basis, not the construction
or Core identity.

### 3.6 Checked grinding augmentation

Original FRI has no grinding message or rejection path. The finite committed
profile adds those effects through a separately checked construction:

```text
CheckedGrindingAugmentation {
  source_protocol,
  target_protocol,
  preserved_occurrence_map,
  inserted_work_seed_challenge,
  inserted_nonce_publication,
  inserted_work_check,
  query_suffix_map,
  checked_constructed_trace_commutation
}
```

The source committed Core ends after terminal material, query randomness, and
its ordinary checks. The target inserts, after terminal material and before
query randomness, one fresh public work-seed challenge, one prover nonce, and
one total verifier predicate over that seed and nonce. All pre-existing
occurrences remain mapped explicitly; inserted effects have no source
occurrence.

Deterministic commutation is required only for target traces constructed with
a valid work witness. An invalid nonce may reject in the augmented target even
though the source has no corresponding rejection. Analysis, not this
construction, states any theorem that prices the added work or transports a
round-by-round error coordinate. The augmentation does not itself establish
soundness amplification.

### 3.7 Construction advice

Randomized commitment material is a separate owner-local occurrence:

```text
CommitmentAdviceAssignment =
  OwnerLocalOccurrence<construction_id, publication, advice_value>
```

Generation consumes the exact advice once when constructing a cap. Public
replay consumes only the opening-local advice disclosed by the proof. Advice
has no portable semantic identity and is absent from the logical oracle.

### 3.8 Typed opening correspondence

Extend Relations with an additive opening clause that binds exact occurrences:

```text
OpeningCorrespondenceClause {
  source_oracle_answer,
  target_query_occurrence,
  target_opening_selector,
  target_publication,
  target_authentication_check,
  extraction_algorithm,
  value_relation
}
```

Structural admission establishes types, occurrence order, unique resolution,
and complete selected coverage. A run-grounded operation evaluates extraction
and equality for one run. It proves neither universal opening correctness nor
cryptographic binding.

Logical query multiplicity and physical opening identity remain separate.
Several occurrence clauses may select one authenticated opening only when they
derive the same oracle, position, and value under the exact profile.

## 4. Exact finite structural object graph

“Exact” in this section means the one object graph admitted by the finite
evaluator. It does not mean exact correspondence to a cited FRI algorithm. The
selected Core stops after two folds and checks a degree-less-than-two terminal
polynomial. It is an implementation-style early-termination witness, not the
three-fold scalar-terminal protocol specified by Section 5.7 Algorithm 1 of
ePrint 2023/1071 for `d0 = 8`.

The witness instantiates:

```text
FriAlgebraProfile
  field F_97
  extension F_97[u]/(u^2-5)
  domains D0, D1, D2
  binary fold and terminal evaluation

NativeFriCore
  initial logical O0
  beta0
  prover logical O1
  beta1
  terminal coefficients
  four ordered query occurrences
  O0/O1 logical answers
  native fold and terminal checks
  Accept/Reject

FriCommitmentProfile
  pair-leaf codec
  salted SHA-256 tree
  two-node ordered cap
  deduplicated opening table
  occurrence selectors

CommittedFriCore
  cap0
  beta0
  cap1
  beta1
  terminal coefficients
  four ordered query occurrences
  opening table message
  authentication checks
  fold and terminal checks
  Accept/Reject

CommitmentCompilation
  NativeFriCore -> CommittedFriCore

GrindingProfile
  work-seed challenge
  nonce type and two-bit predicate
  placement after terminal and before query randomness

WorkAugmentedCommittedFriCore
  CommittedFriCore plus the inserted work effects

GrindingAugmentation
  CommittedFriCore -> WorkAugmentedCommittedFriCore

FreshWorkAugmentedProtocol
  fresh resolver over WorkAugmentedCommittedFriCore

FiatShamirConstruction
  exact statement/context/frame/hash/sampler/work profile
  construction-internal query seed -> Core query-occurrence vector

FiatShamirWorkAugmentedProtocol
  same WorkAugmentedCommittedFriCore
```

Exact-source validation remains additive. A later profile must separately
construct the three-fold scalar-terminal Algorithm 1 instance and its protocol
correspondence. Batched FRI, DEEP-ALI derived quotient views, and STIR virtual
oracles and dynamic query routing are further validation obligations rather
than properties attributed to this object graph. None requires merging native
oracle semantics, commitment compilation, protocol augmentation, or
Fiat--Shamir interpretation.

The target verifier runs from public input and proof only. It never receives
`O0`, `O1`, all salts, polynomial coefficients used to generate the oracles,
or a private replay oracle.

## 5. Claims, reductions, and terminal meaning

The native and committed Cores may use structural claim/reduction declarations
to identify the protocol's intended fold chain:

```text
RSProximityClaim(O0, D0, degree < 8)
  -> FoldReduction(beta0, O0, O1)
  -> FoldReduction(beta1, O1, terminal polynomial)
```

These declarations identify role and order. Applying them in one execution
does not prove that proximity was preserved. The accepting terminal requires
the exact authentication, sampled fold-consistency, and terminal-degree checks
for that run.

The public terminal may be `Accept` because the complete finite verifier is
modeled. The residual scientific proposition remains:

> For an exact-source protocol profile with checked protocol correspondence,
> the exact FRI theorem's field, distance, strategy, and coin premises may
> bound the probability that the initial logical oracle is far from the
> declared Reed--Solomon code. Applying such a conclusion to this early-stop
> profile additionally requires a separate applicable early-termination
> theorem and correspondence.

That proposition is Analysis-owned and unproved here. It does not imply an
outer computation relation.

## 6. Analysis profiles required, not asserted

The architecture must be able to form separate questions for:

1. native FRI completeness and soundness under its exact public-coin strategy
   experiment;
2. commitment binding and, where claimed, hiding or extractability;
3. source-to-target property transport through the exact commitment compiler;
4. property transport through the exact grinding augmentation, including its
   placement and work accounting;
5. restricted state-restoration or round-by-round soundness of the exact
   augmented committed Fresh Protocol;
6. classical or quantum Fiat--Shamir transport with an exact random-oracle
   query budget and loss; and
7. composition with an outer relation or polynomial-commitment claim.

The executable witness checks only that these questions can name all required
subjects and premises without inventing theorem truth.

## 7. OIR and implementation boundary

The native Core need not be projected to an endpoint in this package. Its
purpose is semantic source authority and construction comparison.

The committed Core contains ordinary public messages, challenges, checks, and
terminals. It is therefore the correct future projection source. Supporting it
may require exact field, cap, opening, and hash profiles, but does not require
the endpoint verifier to receive a logical-oracle capability.

This boundary avoids disabling Analysis while the Core changes. Existing
Analysis profiles remain valid for their exact subjects; FRI-specific profiles
are additive and activate only after the new construction and source views are
available.

## 8. Benefits and costs

### Benefits

- Native oracle semantics remain independent of Merkle, PCS, transcript, and
  proof-format choices.
- Public committed verification does not depend on confidential replay data.
- Fresh/Fiat--Shamir same-Core factorization survives at the correct layer.
- Plonky3 caps, Winterfell roots, individual paths, and multiproofs become
  profiles of one checked construction shape rather than competing meanings of
  `Oracle`.
- Query probability, logical multiplicity, unique opening count, and proof
  size remain measurable as different quantities.
- Initial-oracle ownership and outer-relation grounding cannot disappear into
  proof generation.
- Theorem assumptions remain attached to the exact arrows whose properties
  they transport.

### Costs

- There are three Core identities before Fiat--Shamir, not one universal FRI
  ID.
- A complete compiler profile must map schedules and values, not only compare
  roots.
- Grinding has its own structural augmentation and Analysis edge rather than
  being attributed to commitment compilation.
- Randomized commitment advice needs an owner-local lifecycle.
- Relations gains a typed opening clause and run operation.
- Analysis must distinguish source soundness, compiler security, and
  Fiat--Shamir security rather than offering one “FRI secure” property.
- Migration from any implementation that treats an oracle root as the oracle
  itself requires explicit reconstruction.

These costs are semantic work the protocol already contains. Removing their
types would move the work into callbacks, conventions, or trusted evaluators.

## 9. Reversal conditions

Reopen the three-subject decision if executable pressure shows any of the
following:

- the source and target Cores admit a smaller shared subject that preserves
  both verifier capabilities without hiding a construction;
- public target replay unavoidably requires a confidential logical oracle even
  after exact openings are present;
- a typed source-to-target map cannot preserve adaptive queries without making
  the runtime Core branch or rewind;
- commitment advice cannot remain construction-local without changing the
  logical-oracle relation;
- at least two materially different protocols require a common abstraction
  that the checked construction cannot express cleanly; or
- the required opening relation changes native FRI meaning rather than merely
  relating source and target occurrences.

Reopen the separate grinding augmentation if a source-faithful protocol
already contains the identical work-seed, nonce, predicate, and placement, or
if multiple independent constructions show that work is an intrinsic part of
the exact commitment compiler rather than an orthogonal protocol transform.

Do not reopen merely because two identities, more declarations, or migration
work are inconvenient.

## 10. Executable acceptance criteria

The provisional decision survives only if the finite package demonstrates all
of the following:

- one direct native execution with exact-domain logical oracles;
- one public-only committed verification of the corresponding proof;
- exact reconstruction of all fold and query randomness;
- exact reconstruction of the inserted work seed before nonce verification;
- one concrete same-Core coupling from a work-augmented Fresh execution to the
  one-shot Fiat--Shamir execution, including the complete ordered query vector;
- ordered query occurrences with at least one duplicate;
- a smaller deduplicated opening table with total occurrence coverage;
- cap, leaf, salt, path, position, fold, and terminal first-boundary refusals;
- a late fold-consistency negative whose authentication is valid;
- a late terminal-degree negative whose prior folds are valid;
- relation grounding that refuses an outer-relation inference;
- an independently coded public verifier reaching the same classification;
- bounded work and copied-checkout replay; and
- no private-generation or expected-result input read by report construction.

Until those conditions pass, this page is a hypothesis selected for a hard
test, not a completed redesign.
