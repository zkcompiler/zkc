# Fiat–Shamir construction obligations

This chapter defines the obligations a Fiat–Shamir construction meets before a
security claim covers it: which query identities exist, what a challenge may
depend on, which producer messages a construction may leave out of its
transcript, what binds the statement and the deployment, what a transcript
provider or an authored explicit-input construction must establish, and in which
model and under which equivalence notions claims are stated. The installed
native construction is one instance ([transcript construction](construction.md));
request operands are defined with [service queries](../runtime/services.md#operands-fixed-before-sampling);
commitments and openings are [authenticated finite tables](../domains/oracles.md).
The [formal model](../../../lean/docs/spec/fiat-shamir-security.md#construction-obligations)
states the experiments these obligations feed.

An obligation is a property of an actual construction, provider or verifier
body. A construction that meets every obligation of its class is an admitted
design target; implemented admission checks, proved correspondence and
cryptographic security are separate statuses.

## Query identities

Three identities name a challenge at three levels.

| Identity | Level | Contents |
|---|---|---|
| Request | Source protocol | The authority (the randomness root after alias resolution: contract and root), the occurrence (entry, application and repeat path, site, service port, owner, iteration coordinates), the method, the operands fixed before sampling and the result sort |
| TranscriptQuery | Ideal transcript | A scope, the absorbed data the answer may depend on, together with the request (history class) or a request class (explicit-input class) |
| PrimitiveQuery | Concrete provider | The primitive calls (compressions, permutations, byte hashes) a provider makes to realize one TranscriptQuery, with their encoded inputs |

The ideal Fiat–Shamir oracle has one cell per distinct TranscriptQuery. A request
is not a TranscriptQuery: a challenge that depends on the site and the statement
but not on an earlier producer message lets the producer choose that message
after the challenge. In Schnorr, a challenge `e` that does not depend on the
commitment lets the producer pick `z` and set `R = g^z · Y^(-e)` (informative).

**Correspondence.**

- The construction class fixes the map from requests to TranscriptQueries.
- Aliases of one randomness root are one authority but distinct occurrences,
  because an occurrence names its service port; in the history class they are
  distinct cells. Every alias of a selected root is selected.
- Loop coordinates are part of the occurrence. In the history class a model may
  omit them where the absorbed history determines them.
- The scope binds the construction's identity. The installed native suites bind
  their descriptor, including the construction plan, in the invocation root
  ([proof format](../formats/proof.md#deployment-policy-and-descriptor)). Any
  other provider binds its own identity; for a programmable history provider the
  canonical form is the digest of its **interaction pattern**: the
  compiler-emitted sequence of public, message, hint, challenge, proof-of-work
  and salt steps with their sorts, static maxima and labels. The pattern binds
  configuration that changes the step sequence (counts, maxima, gate
  difficulties); it does not replace statement binding, authenticated
  configuration that leaves the shape unchanged, or key correctness.
- There is one oracle per primitive namespace, not per deployment. Deployments
  are separated only by their encoded inputs: identical inputs to one primitive
  share cells, and composition arguments keep that sharing.
- A provider's serialization and execution map TranscriptQueries to
  PrimitiveQueries ([provider obligations](#history-providers)).

## Construction classes

**History class.** A TranscriptQuery is the binding events, then every event the
observation policy absorbs before the request, then the request. The request is
the last event, so the answer's type may depend on it. Distinct occurrences
never share a cell.

**Explicit-input class.** The construction, or the original protocol, computes
an oracle input explicitly from declared values and calls a hash effect: the
TranscriptQuery is a namespace tag with the encoded input. Equal inputs receive
equal answers, by intent, at any occurrence. Security is compositional over the
hash effect ([explicit-input obligations](#explicit-input-constructions)); the
history-class theorem does not apply. EIP-4844's evaluation challenge, the
SHA-256 of a tag, the degree, the blob and the commitment, is an instance:
identical blob and commitment pairs share one cell at any batch position.

**Declared roles of hash calls.** Every hash-effect call in a verifier body has
exactly one declared role:

- a **binding digest**, compared for equality with a commitment or digest (a
  Merkle path step, a versioned hash, a setup digest); or
- an **explicit-input challenge**, decoded into a sampling sort and used in
  arithmetic, with the explicit-input obligations.

A call whose output is decoded and used in computation without a declared role
is refused. Classification between the two classes follows the obligations a
construction meets, not convenience.

## Request operands

Request operands follow the [operand contract](../runtime/services.md#operands-fixed-before-sampling):
reconstructed by both roles from shared data, bound in the TranscriptQuery,
validated before the transcript state is consumed, bounded by static maxima, and,
when they enter a certificate error, of authenticated provenance. A production
security claim needs each such operand restricted to an authenticated admissible
range that supports the claimed bound.

## Realized laws

A request's realized law relates the raw answer of its TranscriptQuery to the
ideal law of its result sort. Laws are stated on the raw answer, and provider
codecs are the identity at the oracle boundary. A law record for a request class
`q` consists of:

- `Raw q`, a finite nonempty type with its uniform law (the oracle's answer type
  at `q`);
- `decode q : Raw q → Option (Value q)`, where `Value q` is the sort the verifier
  continues with, and the ideal law `ν q` on `Value q` (joint for a block);
- a coefficient `κ q ≥ 0`, a slack `λ q ≥ 0` and a proof that
  `Pr[decode U = some x ∧ x ∈ A] ≤ κ q · ν q (A) + λ q` for every event `A` fixed
  before sampling;
- a refusal bound `Pr[decode U = none] ≤ refuse q`, a completeness quantity.

A record is presented by one of five constructors, each a checked claim about
the realized subdistribution `μ`:

- **exact**: a bijective decoder; `μ = ν`;
- **exact with refusal**: `μ = p_success · ν`, as for a rejection sampler
  conditioned on success;
- **dominated with refusal**: `μ ≤ κ · ν + λ`. This suffices for soundness but
  says nothing about the success-conditional law: a decoder that returns `0` on
  one outcome of a fair bit and refuses on the other is dominated by the uniform
  bit law, yet constant on success;
- **bounded point ratio**: `μ(x) ≤ κ · ν(x)` for every value;
- **additive**: `κ = 1` and `λ` the statistical distance.

A refusing decoder stops the verifier, and stops never accept, so soundness needs
only the inequality. A decoder that resamples consumes more transcript output and
changes the successor state, so its law belongs to the provider's execution
simulation, not to a record. A certificate charges each oracle key a function of
the whole key, its preceding history and its last event: `κ · ε + λ` for a site
with ideal-law error `ε`. The richer charge discharges neither the all-table
resampling bound nor the pathwise weighted budget that the weighted bad-query
argument requires of each certificate.

## Observation policy

A construction absorbs every producer message at its occurrence, except values
in the three classes below. Each class has an obligation and an equivalence
notion. Classification is by data flow, never by name or type: a value the
producer chooses that plays the role of a challenge, such as a challenge share
of an OR proof, is a producer message.

1. **History-reconstructible values.** Values the validator reconstructs from
   the absorbed history and earlier oracle answers, such as challenge deliveries
   and pinned constants. Their omission is justified by a **causal replay
   coupling**: a re-encoding of oracle keys that
   - computes each omitted value from the key and from answers to strictly
     earlier queries only, never from the answer being selected;
   - maps repeated queries to repeated queries and distinct queries to distinct
     queries;
   - keeps every query fresh in one experiment fresh in the other, across the
     joint adversary and verifier cache; and
   - translates the adversary's direct queries with a stated
     [query-cost relation](#provider-simulations-and-their-query-cost).

   Injectivity of a re-encoding that reads the oracle is not enough: over two
   keys with uniform bits, sending one key to a zero-valued cell whenever one
   exists is a bijection for every table, yet selects zero with probability
   `3 / 4` (informative). A constant re-encoding is causal and preserves
   repetition, yet makes two independent answers equal.
2. **Certified openings.** Openings followed by further requests, under the
   four conditions of [certified openings](#certified-openings).
3. **Terminal messages.** Messages after which no selected request is reachable.
   The obligation is that the abstract transform's outcome is unchanged for every
   challenge function. This is not operational equivalence: native observations
   may fail, consume budget or run a handler, so an omitting construction is a
   distinct construction with its own construction theorem.

### Certified openings

An opening followed by a reachable selected request may be omitted from the
transcript only if all four conditions hold. An opening after which no selected
request is reachable is a terminal message instead, with that class's
obligation.

- **Fixed at the receive point.** The root, the positions, the dimensions and
  the interpretation (the committed table, its leaf layout and codec) are
  functions of data available at the receive point from three sources only:
  absorbed messages; bound statement inputs or authenticated configuration; and
  earlier challenge answers, through the causal replay relation. Values that are
  merely visible to both roles do not count. The producer supplies only row
  values and authentication data. A root binds neither the table height nor
  the scheme (two tables whose heights have the same depth authenticate the
  same rows, and rows of a field and of its extension over the same coordinates
  give one root), so dimensions and scheme identity come from these sources,
  never from the root or the opening.
- **Authentication dominates use.** Every use of the returned row is dominated
  by a successful authentication check against that root; a failing check stops
  or rejects.
- **Representation independence.** Only the authenticated semantic value affects
  later computation. Paths, alternative encodings and unchecked fields reach
  nothing but the check, and no control decision other than the check's guard
  depends on them.
- **Consistent answers.** In the ideal reading the committed table fixed at the
  commitment's checkpoint answers the opening. In the concrete reading this is
  an obligation of extraction and composition: a joint game over transcript
  cells and hash cells, with extraction at each transcript key that contains a
  root under the [checkpoint convention](#extraction-checkpoints), a
  multi-extraction (drift) error, and a statistical-distance step to the
  committed-table experiment (Chiesa and Yogev, *Building Cryptographic Proofs
  from Hash Functions*, Theorem 25.2.1). The joint-game theorem discharges this
  condition without a separate resampling-stability premise; key-reconstruction
  and extraction-stability lemmas are an alternative proof route.

The first three conditions are checked per compilation, over the actual verifier
and handler bodies, by data-flow and dominance analysis in the style of the
[public-coin analysis](public-coin.md). The fourth is a theorem. Temporal
precedence of the hash record in verifier execution is not oracle independence:
an adversary can query a transcript cell before arranging the hash record.

### Construction profiles

Support starts from a closed set of construction profiles, each naming its class,
observation policy, gate form and provider, with its obligations. Custom
observation policies outside these profiles are not admitted.

| Profile | Class and observations | Obligations |
|---|---|---|
| Absorb everything | History; every message | The history-class construction theorem |
| Terminal-opening omission | History; openings after the last request omitted, positions as one block request | Query-free suffix; commitment bridge; block law |
| Delivery omission | History; challenge deliveries omitted (reconstructible), terminal response omitted | Causal replay coupling |
| Certified openings between requests | History; openings between requests | The four certified-opening conditions |
| Explicit input | Explicit-input class | The explicit-input obligations |
| Native atomic gate | A gate on a native suite | Gate law; the suite's execution simulation |

Omitting terminal openings removes the omission obligation, not the commitment
bridge: relating roots and openings to committed tables still needs
authentication to dominate every use of an opened row.

## Blocks and gates

**Blocks.** A block is one request whose result is several values with one
joint law: one occurrence, one transition or handler, one TranscriptQuery and
one delivery. Its law is a proof obligation on the joint value; uniform
marginals do not establish it. A handler that copies one uniform position into
every entry of a block has uniform marginals and the escape probability of a
single position.

**Gates.** A proof-of-work gate attaches to one selected request (a challenge or
a block). The producer searches its transcript state for a witness, the witness
travels in a slot the record codec reserves, both roles run the provider's gate
step, which yields a successor state and a pass bit, the validator requires the
pass bit, and the gated request derives its value from the successor state.

- **Custody.** The witness is internal to the construction; its only consumers
  are the gate step, the producer's re-check and the record codec.
- **Placement.** Nothing is absorbed between the gate step and the request.
- **Difficulty.** The difficulty is an operand of the occurrence, under the
  operand contract.
- **No search in the validator.** The validator never searches.
- **Necessary conditions.** The gate step's primitive input includes the full
  transcript state before the gate, and the state from which the gated value is
  derived has absorbed the witness. These are necessary, not sufficient.

The gate's local obligation is an accepted-value law for the gated request:
`Pr[pass ∧ value ∈ A] ≤ γ · ν(A) + λ` for every event `A` fixed before sampling,
where `γ` may be written as the pass probability times the challenge's factor
only with a proved factorization. Gate bits read after the gate are part of the
gated value. Each grinding attempt is one TranscriptQuery, charged to the round
whose challenge it precedes. Acceptance, honest search (any procedure returning a
passing witness within explicit limits; exhaustion is the terminal stop
`exhausted`) and reproducibility of a particular witness are separate
properties.

## Cryptographic effects

An opaque family declares an effect signature, and its meaning is a process over
that signature. A construction has three readings of one syntax: the concrete
reading (the actual hash, which the runtime implements), the random-oracle
reading (a lazily sampled oracle with a query record) and the ideal reading
(commitment carriers are the committed tables). The readings do not transfer
security by themselves; the relations below do.

1. **Effect trace.** The ordered calls with their arguments and replies.
2. **Shared-oracle namespace.** One oracle specification per primitive
   namespace: a disjoint union of named families with typed inputs and outputs
   (transcript oracles, Merkle leaf and node families, proof-of-work trials,
   explicit-input hash families). The abstract families are independent by
   definition. That a deployed primitive realizes them is an obligation with a
   precise game and a feasibility check per deployment. Every role of the
   primitive in the deployment is enumerated, tagged or not, and the concrete
   input domains of different roles do not overlap, or the overlap is
   accounted for.
3. **Budget.** Every adversary call to any family counts toward its budget;
   verifier calls count toward the experiment's total query bound.
4. **Concrete-to-ideal relation.** For false-statement acceptance,
   `Pr[concrete verifier accepts ∧ statement false] ≤ Pr[ideal verifier accepts ∧
   statement false] + extraction error + collision terms`. The relation preserves
   the statement, including an adaptively chosen one, and its falsity, and
   relates values (roots and paths to committed tables), adversaries (primitive
   access to committing tables) and executions.
5. **Preservation classes.** A transformation of verifier code that changes
   effect calls is classified as one of:
   - **exact trace preservation**: the same calls, order, arguments and replies;
     every reading transfers;
   - **law-conditioned outcome preservation**: equal outcomes for every handler
     with hash consistency (equal inputs receive equal answers, as a function of
     the input) and the failure law (no stop depends on the number or order of
     calls), for example verifying a pruned multi-opening instead of separate
     paths. A handler that answers a repeated input differently, or stops after
     a call limit, distinguishes the two. For the random-oracle reading a cache
     coupling and a query-cost relation are proved separately;
   - **one-way acceptance preservation**: soundness only.

### Extraction checkpoints

The extractor follows one convention. For each transcript key `K` that contains
a root, extraction runs once, immediately before the first fresh query of `K`
in the joint record, from the record so far, whichever party issues that query;
in an experiment that starts from an empty cache this is the first query of `K`.
Every later query of `K` is a cache hit and reuses the frozen extraction, so the
extraction is fixed before the answer at `K` is sampled, and resampling that
answer cannot change it; any later disagreement between the frozen table and an
accepted opening is the drift event. The extracted object `T*[c, K]` is indexed
by the authenticated configuration `c` and the key `K`, not by the root alone:
one root under two configurations has two checkpoints. Re-extraction at a
repetition is admissible only as a separately specified checkpoint, charged in
the multi-checkpoint bound. The convention is stated against an abstract query
record, a classical log or a compressed-oracle database. Extraction from the
terminal record is not frozen: an adversary that queries a transcript cell and
then arranges the hash record makes it depend on that cell's answer.

## Binding

Four obligations bind what a TranscriptQuery's scope stands for.

- **Exact statement determination.** When the scope encodes the statement
  injectively, the initial histories determine the statements: an initial
  history followed by any events equals another statement's initial history
  followed by any events only for equal statements. It follows from constructor
  injectivity of typed public-value binding events (vectors, indices and
  canonical rows as well as scalars) and prefix freedom over every statement the
  adversary can output, malformed ones included. A count is encoded before its
  vector, or the vector carries its length.
- **Collision-bounded binding.** When the scope holds a digest, the experiment
  with digests equals the one with full statements outside a collision event.
  The event ranges over every relevant hashing operation: the adversary's
  queries; deployment setup (initialization vectors, asset identities,
  verification-key digests, the interaction-pattern digest); verifier
  recomputation; and authenticated digests that exist before the experiment,
  counted as fixed queries or covered by a stated collision-resistance or
  second-preimage assumption. A finite digest is not injective, so it never
  establishes exact determination; a digest truncated below its field's size is
  admissible only here, with its collision term.
- **Authenticated configuration.** Inputs a theorem treats as fixed are
  authenticated by the deployment and quantified before the adversary.
  Classifying an input as configuration does not fix it: a value treated as
  configuration flows from compile-time constants or from pinned assets of the
  authenticated deployment, and a configuration-classified input that arrives as
  a runtime parameter is refused unless it is bound as a statement input.
- **Verification-key correctness.** A verification key is correct by checked
  recomputation, a certificate or a realization theorem; native computation and
  indexer determinism do not provide it.

An input that reaches a handler is not thereby bound. Statement binding ties the
actual observation expression to a proved serialization law.

## History providers

A history provider has a state (copyable, or the managed capability) and these
operations, each a process over the namespace effects that may stop with
`refused`, `exhausted` or `reject`: `initialize` and `start` on bound inputs,
producing the binding; `absorb` of an event; `request`, returning a successor
state and a raw answer; `gate` on a witness and a request, returning a successor
state and a pass bit; and the producer-only `search` within limits. Construction
handlers are the source form; native suites are installed instances.

A history provider realizes the **history-to-primitive correspondence**:
distinct reachable TranscriptQueries reach distinct primitive inputs, outside the
collision event of collision-bounded binding. The occurrence need not be an
explicit label in the input; it must be recoverable, for example from the
evolution of the state. Monero's transcript draws `y` and `z` consecutively with
only ignored deliveries between them and absorbs no occurrence label, but each
draw replaces the state by the encoding of the scalar it returns, so the two
inputs differ and the construction is admitted. Two reachable requests that
reach the same primitive input, such as a stateless draw used twice, are
unintended cell sharing and are refused; such a provider is corrected or
declared explicit-input with its intended shared cells listed.

A history provider meets six obligations.

- **Construction correctness.** The compiled handlers implement the provider's
  operations, effects and stops included, checked per compilation.
- **Serialization.** Typed events and requests map to primitive inputs
  injectively and prefix-free, or with collision-bounded binding. Injectivity
  holds under shape and domain facts the validator checks or reconstructs; a
  variable-length observation encodes its length unless authenticated
  configuration fixes it. Prover-message codecs have an efficient left inverse,
  which governs extraction time. Challenge codecs admit preimage sampling; this
  condition is reserved for zero-knowledge claims and is not an obligation of a
  soundness claim.
  An imported codec carries no security claim until this obligation is
  discharged for it.
- **Execution simulation.** The adaptive execution of the chain or sponge in
  primitive calls, together with the adversary's direct primitive access, is
  simulated in the primitive's ideal model: the joint view matches the ideal
  history-oracle experiment for the stated property up to an explicit loss, with
  an adversary translation and its
  [query-cost relation](#provider-simulations-and-their-query-cost).
- **Realized laws.** The law records and gate obligations hold for the realized
  answers under the execution simulation.
- **History binding.** The statement and the construction identity are in the
  history under exact or collision-bounded binding (for a programmable provider,
  the interaction-pattern digest); configuration is authenticated.
- **Certified omission.** Every omitted event belongs to an
  [observation class](#observation-policy), decided by data flow, with its
  obligation.

### Provider simulations and their query cost

A provider simulation is stated for one property (soundness first), one provider
and one class of bounded executions. Its query-cost relation has this type.

| Component | Domain and codomain | Meaning |
|---|---|---|
| Families | a finite type | The primitive families of the namespace |
| Concrete budget | family → natural number | Primitive calls the adversary may make on every path, per family |
| Execution bound | the verifier's static maxima | Loop and operand maxima, message and request counts |
| Private tape | budget → finite type | Randomness the translated adversary draws uniformly before its oracle computation; it is never charged |
| Translation | concrete adversary → (tape → ideal adversary) | From primitive access to the history-oracle experiment, through a simulator |
| Cost | budget → natural number, monotone | The TranscriptQuery budget of the translated adversary |
| Verifier expansion | execution bound → natural number | Primitive calls of one verifier run within the bound, initialization included: `v_init + Σ_e n_e · v_e + Σ_r n_r · v_r`, with `v_e`, `v_r` the calls per absorbed event kind and per request kind and `n_e`, `n_r` their counts at the bound's maxima |
| Loss | budget → natural number → probability | Applied to the adversary's budget and the verifier expansion |

The translation is a simulator run against the concrete adversary, and the
relation is defined on its traces. In each state of the simulator a primitive
call either belongs to an **attempt**, the TranscriptQuery it realizes, or is
answered by the simulator from its state and the private tape with no
TranscriptQuery, as a hash-chain simulator answers a query at a state no
history reaches with a fresh digest. The simulator starts with no recorded
answer. A call's assignment to an attempt persists through every later call, so
a repeated call stays in its attempt, and the calls the simulator declares to
make up one concrete attempt, such as both calls of a split-hash gate attempt or
the counter blocks of an extended output, belong to one attempt in every state.
The first call of an attempt on a path, whichever call of the attempt comes
first, therefore asks the history oracle once and the simulator records the
answer; every later call of the attempt, interleaved with any other calls, is
answered from that one recorded answer, and any two calls of one attempt are
answered from one ideal answer in either order. A grinding attempt is therefore
one TranscriptQuery whatever its primitive cost. A call the simulator answers
privately may later join an attempt, as a query at a state that a later answer
reaches does; the difference this makes from the concrete primitive belongs to
the loss. On every path each
primitive call makes at most one TranscriptQuery, and only calls of the families
that carry attempts make any; a per-family bound on the concrete adversary
transports to a total query bound on every translated program, and through it to
the pathwise weighted budget. The ideal adversary is the mixture over the tape,
so the ideal experiment is the typed engine's experiment for provers drawn from
a distribution, each bounded on its support. For every adversary `A` within
budget `q` and every execution bound `b`:

```text
Pr_concrete[property fails](A, b) ≤ Pr_ideal[property fails](translate q A, b) + loss q (expansion b)
```

The ideal side is the typed history-oracle experiment with per-key charges; the
verifier's own TranscriptQueries are charged there, not by the cost. For a hash
chain with full `λ`-bit states the loss is about `(Σ q + V)² / 2^λ` for collision
and prediction over the joint primitive-query trace; for a duplex it is a
capacity term plus codec terms. A stateless simulator is used where one exists
and is not required.

## Explicit-input constructions

An explicit-input construction is an authored computation with explicit
hash-effect calls and no provider state machine. It meets six obligations.

- **Construction correctness.** The compiled computation produces exactly the
  declared explicit inputs and decodes as declared. Canonical decoding makes the
  received bytes equal to the reference re-serialization. The obligation states
  whether a match with an upstream implementation means equal outcomes or
  identical primitive queries.
- **Exact primitive-query sharing.** Equal declared inputs yield identical
  primitive queries; namespaces are separated by tags, with the feasibility
  check of the shared-oracle namespace, and sharing survives composition. Byte
  equality coincides with value equality only under canonical decoding.
- **Typed decoding.** Every decoded challenge has a law record.
- **Local binding predicates.** Each check states the values its explicit input
  binds, through an injective, length-determined encoding, with every bound
  value decoded canonically before hashing or re-encoded canonically. Binding
  the whole statement is not a universal requirement: EIP-4844's evaluation
  input binds the blob and the commitment; its batch input binds commitments,
  evaluation points, evaluations and proofs, and not blobs.
- **Composition theorem.** The construction's own security theorem over the hash
  effect, stated per property. It specifies:
  - each extraction it relies on, with its failure term, fixed before the oracle
    answer it is used against is sampled. For EIP-4844, a polynomial of degree
    below 4096 is extracted from each commitment before the evaluation-namespace
    answer for that commitment's input is sampled, under KZG evaluation
    extractability in the algebraic group model or an explicitly named
    alternative assumption. Opening binding alone does not suffice: the
    adversary produces a single opening, so no second opening contradicts it;
  - each namespace's term. In EIP-4844's evaluation namespace, if `C_i` is not
    the commitment to `blob_i`, then `y_i = p_{C_i}(z_i)` holds with probability at
    most `κ · 4095 / r` per evaluation query, `κ` being the hash-to-field factor;
  - multi-instance soundness where a check covers several items: the false
    statement of a batch is that some item is false, and in EIP-4844's batch
    namespace a combination with weights `r^0 … r^(n−1)` passes an invalid opening
    with probability at most `κ · (n − 1) / r` per batch query;
  - the chained-namespace term where one namespace's input contains another's
    answers: a batch query made before the matching evaluation queries commits
    to guessed evaluation points, and a later evaluation answer may hit any of
    them, at most `q_eval · q_batch · n · κ / r` in EIP-4844;
  - budgets that count the verifier's own hash queries alongside the
    adversary's: an EIP-4844 batch verification makes `n` evaluation queries and
    one batch query.
- **Challenge-input coverage.** For every explicit-input challenge `c` and every
  check that uses `c`, each value the check reads that the producer controls or
  that is a statement input is in `c`'s encoded input, is determined by values
  in it (including answers of other namespaces that are themselves in it), or
  is named in an exemption carried by the composition theorem. It is checked by
  data flow per compilation.

## Equivalence notions

Each equivalence is claimed only under its stated notion.

| Notion | Meaning |
|---|---|
| Ideal erasure | A step is erased in the ideal interactive model |
| Distributional equivalence by coupling | An explicit coupling, or an experiment-equivalence theorem, under which the outputs of two experiments, the adversary's view included, have the same distribution; established by a fixed re-encoding injective on every key either experiment can query, or by a causal replay coupling |
| Distributional equivalence up to a bad event | Identical until a stated bad event, with its probability bound |
| Construction correctness for a provider | The constructed meaning equals the transform of the gated original for every challenge function and lawful monad |
| Operational equivalence | Equal outcomes, stops, consumed proof, state and work |
| One-way acceptance preservation | If the new verifier accepts, the old one does |

Distributional equivalence, a provider simulation and law-conditioned outcome
preservation are distinct notions, related only by stated theorems:
equivalence up to a bad event of probability `ε` gives, for every property
event, a provider-simulation inequality with loss `ε` under the coupling's own
adversary translation and query-budget transport; law-conditioned outcome
preservation with a cache coupling and a query-cost relation gives
distributional equivalence for the random-oracle reading. No converse holds in
general. Absorbing a constant at a zero-difficulty gate is an ideal erasure and
a distributional equivalence by the re-encoding that inserts the constant, but
not the same construction: it changes later keys.

## Model and scope of claims

Claims are made in the classical random-oracle or ideal-permutation model.
Knowledge soundness, zero knowledge and quantum claims are separate claims.

- **Random-oracle scope.** Claims do not transfer to a concrete hash when the
  relation can evaluate that hash: Khovratovich, Rothblum and Soukhanov (ePrint
  2025/118) obtain accepted proofs of false statements for every concrete hash
  through a GKR circuit that computes it. A security report flags such relations
  (GKR circuits, virtual-machine programs, recursive verifiers) and makes no
  concrete-hash claim for them.
- **Quantum reservations.** Every proof component is classical: the lazy cache,
  resampling one cell, query records, extraction from the hash record, cache
  couplings. Four choices keep quantum formulations possible:
  1. certificates are model-neutral: a worst-case, per-prefix local bound under
     the uniform raw law, never an averaged bound;
  2. couplings and namespace separation are stated as transformations of oracle
     functions where possible. Only exact identities of oracle functions
     (measure-preserving transformations, as for domain separation and fixed
     re-encodings) can support a quantum formulation; classical bad-event
     bounds, collision and prediction terms, cache couplings, lazy sampling and
     query-cost relations do not transfer by restatement;
  3. extraction obligations are stated against an abstract query record;
  4. gate coefficients are quantities of the classical model: Grover search
     roughly halves the bits of a proof of work, so a statement that grinding
     adds `b` bits names its model.
- **Reporting.** Every bound is reported twice: per round, as `−log2` of the
  error with grinding included, and as the complete bound at a stated query
  budget. Each figure names its proximity regime; a conjectured capacity-regime
  figure is labelled conjectured.
