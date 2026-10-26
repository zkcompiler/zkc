# Selected property adapters

These adapters consume exact mathematical experiments in the existing security
and ArkLib packages. They introduce neither native codecs nor new compiler-stage
correspondences. ArkLib remains pinned by
[`integrations/arklib/lakefile.toml`](../../integrations/arklib/lakefile.toml).

## KZG evaluation binding

`ZkcArkLib.Kzg.EvaluationBinding` selects the pinned KZG evaluation-binding
experiment. Setup samples a nonzero trapdoor privately, generates the two SRS
vectors and gives only those vectors to the adversary. The adversary chooses
one commitment, one point, two field values and two private opening states.
Its actual upstream one-message opening prover runs twice against the KZG
verifier. Those runs share the same initially empty uniform-oracle cache.
Failed opening runs count as rejection. Success means both openings accept and
the two claimed values differ. The bound averages over setup and oracle answers;
it is not a worst-case statement for each SRS.

The adapter's record retains the trapdoor, SRS, commitment, point, both values,
both verdicts and both proof elements for analysis. It does not give those
analysis fields to the adversary. `averageSuccess_eq_bindingExperiment` proves
exact agreement with the base upstream game. `averageSuccess_le_tSdh` uses the
pinned intermediate condition implication, mapped-event law and experiment
equality, before any hardness invocation.

`Scope` fixes binding and SDH budgets, their admissibility predicates and closure
under this exact reduction. `ScopedHardness` bounds only SDH algorithms admitted
at that selected budget. `scoped_bound` combines those premises with the
unconditional reduction inequality. Budgets acquire their computational meaning
from the supplied predicates and closure proof; their numerals alone establish
no runtime property. The upstream `Groups.tSdhAssumption`, which quantifies over
all functions of its adversary type, is not used. These theorems make no
unconditional or efficient-adversary security headline.

`ZkcArkLib.Kzg.OpeningClient` supplies a concrete group/field consumer: a client
returns a commitment, point, two values and two group proofs. Its opening prover
sends exactly the selected proof and makes no opening-phase oracle queries.
`experiment_openingAdversary` equates the whole adapter computation to a direct
record experiment using the actual `KZG.verifyOpening` twice. This preserves
unsuccessful outcomes as well as conflicts. `opening_success_eq` and
`opening_success_le_tSdh` transport the direct client's average success.
`claim_query_bound` preserves a supplied bound on the claim computation's
uniform-oracle queries; it is not a machine-time bound.

The finite-field controls instantiate the actual pairing equations in the
multiplicative tagging of the additive group of `ZMod 7`. They check accepted
honest zero-polynomial openings, equality of experiments, the reduction bound,
and the failure of the nondegeneracy premise for the zero pairing. The small
public group is an algebraic control, not a computational-hardness instance.
Evaluation binding establishes no polynomial knowledge, degree binding,
function binding, native byte binding, or correspondence to an imported zkc
KZG participant.

## Request-fixed straight-line oracle recovery

`ZkcSecurity.Commitment.FiniteRecovery` fixes an immutable two-cell oracle with
query type `Fin 2`. A request contains the expected sum. Its relation requires
the recovered ordered pair to have that sum. The extraction program is defined
by the request API: query cell zero, query cell one, return both values. Evidence
contains no algorithm or witness-search function. The query-bound theorem proves
the two-query scope. No witness validity restriction shrinks the input oracle
universe.

`ZkcSecurity.Claims.FiniteRecovery` registers the separate model-level profile
`extractors.finite_two_cell_sum@0`, with schema
`zkc.extractor.finite-two-cell-sum/0`. Its registry uses `Zkc.Claims.Registry`;
lookup refuses missing keys, unknown versions and duplicate entries, including
externally assembled duplicates. A known entry without a definition remains
incomplete. The carrier is a closed profile token whose interpretation is fixed
by the library. Registry entries and evidence cannot contain a replacement
relation, access handler, algorithm or proposition.

The typed evaluator takes the original `Commitment.FiniteRecovery.Request F`
directly and requires the resource coordinate to be exactly two cell queries
before selecting evidence. It checks the canonical identifier and schema even
when a caller supplies the registry. `Evaluation.meaning_eq` pins every successful
evaluation to `Guarantee request queries`. That proposition requires recovery of
the actual ordered pair for every input, the exact operational query law
`IsQueryBoundP request.extract (fun _ => True) bound ↔ 2 ≤ bound`, and equality of
acceptance and recovery probabilities for every sender of type
`ProbComp (F × F)`. The model run retains the sent cells and the verdict of the
fixed verifier under `answers cells`. The success event is that verdict being
true; recovery uses the same sent cells. Only addition and decidable equality on
`F` are required, with no field, validity-support or computational-admission
assumption. Evidence supplies proofs of this proposition, with no algorithm
field. `certify` is a direct proof method for the evaluated model meaning.

Here, the native runner means ArkLib's actual interaction interpreter, without
a claim about the zkc native compiler or runtime.
`ZkcArkLib.Knowledge.FiniteRecovery` uses the pinned oracle-send protocol and
`KnowledgeCertificate`. The concrete message determines its backward witness
map. Its terminal witness is unit; its terminal predicate is the same fixed sum
relation. `extract_eq_native` connects the operational two-read program to
`RoundExtractor.extractWitness` on that exact path. `native_extraction` invokes
ArkLib's extraction-failure theorem; this selected tree has no verifier
challenges on which extraction could fail.

The restricted native verifier accesses the received message only through the
latest resource added by `Access.extendImpl`. `closed_verifier` binds that
handler to the request verifier. The same binding proves `honest_accepts`.
`nativeRun_eq` preserves the actual paired runner's path, sender output and
verdict. `acceptance_eq_recovery` proves equality of average native acceptance
and successful request-fixed recovery on the same sent oracle for arbitrary
probabilistic senders. This single-stage consumer needs no sequential knowledge
composition theorem, although it uses the existing native execution API exposed
with `KnowledgeComposition`.

`ZkcArkLib.Knowledge.RegisteredFiniteRecovery` is the optional integration for
that registered meaning. `observations_eq` projects the actual runner's received
cells and verdict to the model run, using `nativeRun_eq` and its
`closed_verifier` binding. `registered_extractor` uses `extract_eq_native` on
every payload, without a relation premise. `acceptance_of_evaluation` transports
evidence for the fixed evaluated proposition to actual upstream acceptance for
an arbitrary probabilistic sender. Conversely, `certify_native` proves the
same evaluated meaning using the existing `acceptance_eq_recovery`. The security
model module does not import ArkLib; the adapter cannot change its meaning.

A fully finite `ZMod 7` sender ranges over all 49 two-cell messages; the checked
native acceptance and recovery probability is exactly `1 / 7`.
Controls cover positive registered evaluation, missing/undefined/duplicate and
wrong-version entries, schema mismatch, one-query refusal and exact two-query
cost. Concrete pairs refute a one-cell access substitution, a changed sum
relation and a constant valid witness substituted for the requested recovery;
a first-query observation also distinguishes reversed read order. Registration
controls check that the straight-line profile and response-difference forking
cannot be selected as each other's meaning. This supplies separately registered
extraction for this typed model. The property is separate from registered
response-difference forking in `Claims.Extractor` and from KZG evaluation binding.
It assumes access to both immutable cells and establishes only this finite oracle
relation. It does not
supply a KZG extractor, an extraction cost calculus, a new canonical claim wire
schema, or a native/compiler receipt.

## Private producer and concrete verifier WP

`ZkcSecurity.FiatShamir.PrivatePairWP` extends the empty-private-service WP
consumer to a producer with fresh private sampling. Fixing a public ROM answer
table leaves the producer computation probabilistic. `producerWP` quantifies
over every supported actual producer execution: the producer must return, and
the actual emitted proof must satisfy `validatorWP`. The verifier WP uses the
same complete deterministic table handler as `HonestCompiled.pairWP`.
It requires a returned accepting result and complete proof consumption.

`validate_of_wp` transports the complete returning verifier execution to the
sampled interpreter. `pair_success` retains the actual producer state handoff
and proves the existing whole-pair success event with probability one. It does
not discard stopped or rejected producer observations. The pre-existing
`SampledCompiled.simulate_computation` supplies full handler correspondence,
including environments, proof buffers, ordered events and both post-states.
One outer ROM cache encloses production and validation. Private draws stay on
the uncached uniform summand, including repeated draws at the same port.

`Claims.PrivateCompleteness.perfect_of_private_producer_wp` consumes this law
through canonical completeness. Source relation, honest input preparation,
nonvacuity and the complement definition of all unsuccessful mass remain the
request's existing meanings. Failed preparation is not conditioned away.
`PrivateReadbackWP.of_readback` lets existing sampled component proofs supply
this concrete verifier WP. It changes only a proof interpreter: producer draws
remain unchanged, while the reference validator refuses private services.
A successful reference WP therefore cannot reach a private validator draw.
The selected consumer supports private producers and returning deterministic
validators; genuinely randomized validator continuations need their own
support-aware consumer.

`TestsSecurity.PrivateProducerWP` applies the bridge to the actual admitted
randomized Schnorr producer and verifier, using the existing ABI preparation,
retained relation and nonvacuity proof. It also checks supported producer-stop
refusal, fresh repeated draws, and a real sampled producer whose zero draw
stops with exactly `1 / 7` unsuccessful mass. These are ideal mathematical
experiments, without native entropy, scheduling or provider correspondence.
