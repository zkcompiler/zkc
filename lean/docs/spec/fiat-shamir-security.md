# Multi-round Fiat–Shamir security

This chapter specifies the retained mathematical transcript, query and security
interfaces. They state conditional bounds under explicit sampling, soundness,
commitment, extraction and resource premises. They do not currently establish a
connection to a native compiled artifact: the former concrete source/compiled/byte
installations were retired. See [support](../support.md).

The shared transcript definitions and Protocol library own these models. The
typed query, round-by-round, provider and stage relations remain mathematical
interfaces. A new actual-source application must install its exact source meaning
and transformations before using their bounds for a compiled security claim.

## Typed query sites

A validator is a process `PIR.Process I A` over any operation signature `I`. A
**transcript interface** `Zkc.Transcript.Interface I E P Raw` (also
`Zkc.Transcript.Interface`) states, for each operation, how the transform treats it
(`Zkc.Transcript.Absorption`); `Raw : E → Type` is the raw answer type of each
query occurrence:

- `receive event recover`: read the next proof message `m : P`, absorb the
  event `event m : E` and continue with the reply `recover (event m)`; a message
  whose event recovers no reply refuses without being consumed. The reply is a
  function of the absorbed event, which is what binds it.
- `send event value`: absorb `event` and continue with `value`.
- `query event decode`: absorb the challenge occurrence `event`, ask the
  transcript oracle at the history `preceding ++ [event]` and continue with
  `decode raw` of its raw answer `raw : Raw event`; a refused decoding stops
  with `exhausted`.
- `refuse`: stop.

The raw answer type is a function of the occurrence, so it may depend on the
request the occurrence carries, for example on its method, its result sort and
operands fixed before sampling. The decoder reads the raw answer alone; an
operand it needs is carried in the occurrence. Each query site chooses its
result sort (a field or extension element, a bounded index, a bit string, a
gated pair or a block of indices) and its decoder; decoders may refuse, as
rejection samplers do. The transform `Zkc.Transcript.transform absorb oracle`
(also `Zkc.Transcript.transform`) runs a validator from an absorbed history on a proof
in any monad, asking `oracle preceding event` at every query, and returns the
outcome and the unread proof suffix. A result is accepted when its outcome is
(`Accepted accepts`); complete acceptance (`AcceptedComplete`) also requires
the unread suffix to be empty, so a bound on acceptance bounds it.
`Zkc.Transcript.replay` replays a validator along given events against an
answer table.

The transcript oracle on all event histories, `OracleSpec.ofFn R`, answers a
history `key` in `R key`. `Typed.ReadsByOccurrence R Raw` reads its answer at a
key `preceding ++ [event]` as a raw answer of the occurrence, by an
equivalence: a range independent of the key reads every answer as itself, and
the range by the last event, `Typed.ByLast Raw`, reads it in `Raw event`
([below](#raw-answers-by-the-last-event-and-lifting)). The typed engine's
transform asks the history oracle through this reading (`ZkcSecurity.FiatShamir.Typed.ask`). Oracle
identity, replay and doomed sets depend on the whole history; the answer type
and the decoder depend on the occurrence only.

A **certificate** `Typed.Certificate absorb accepts error` is a set `doomed` of
residual processes, with an error `error e` for every absorbed occurrence `e`,
whose members meet the local obligations `ZkcSecurity.FiatShamir.Typed.Step`:

- a doomed `done` result does not satisfy `accepts`;
- a doomed receive stays doomed for every reply, and a doomed send stays doomed;
- from a doomed query with occurrence `e`, after every absorbed prefix, the
  site's decoding of a fresh uniform raw answer of `e` yields a value that
  leaves the doomed set with probability at most `error e`; refused answers
  never escape.

The escape bound is stated for the decoded law of the site, so a site's error
already includes its sampling correction (see [realized laws](#realized-sampling-laws)).
`ZkcSecurity.FiatShamir.Typed.QueryBound` counts the queries on every path of a validator, and
`ZkcSecurity.FiatShamir.Typed.CostBound` charges each query the error of its occurrence.

**Per-key charges.** A charge `charge : List E → E → ENNReal` is a function of
the whole key: the absorbed history before a query and its occurrence. It can
count loop iterations that the history determines and read operands carried in
the occurrence. A **charged certificate** `Typed.ChargedCertificate absorb
accepts charge` has a doomed set of pairs of an absorbed history and a residual
process, so one residual shape can be doomed with a different error at each
place it is reached. Its local obligations `ZkcSecurity.FiatShamir.Typed.ChargedStep` at a doomed pair
`(history, process)` are: a doomed result does not accept; after a receive whose
event recovers a reply, and after a send, the residual is doomed at the extended
history; and a doomed query with occurrence `e` escapes, at
`history ++ [e]`, with probability at most `charge history e`. A loop whose
occurrence carries no iteration coordinate is thus charged each round's own
error, read from the history (`TestsSecurity.LawRecords.loop_soundness`), where
a certificate whose doomed set ignores the history must charge every round the
largest error (`historyFree_error_ge`). The security argument uses a doomed pair
only where replaying a validator along the history reaches the residual
(`ZkcSecurity.FiatShamir.Typed.BadKeyAt`, `ZkcSecurity.FiatShamir.Typed.EscapesAt`), not an honest execution. A certificate
with an error per occurrence is the charged certificate whose doomed set and
charge ignore the history (`Certificate.charged`, `Step.charged`).
`Typed.ChargedCostBound absorb charge process history cost` bounds the charges
on every path of a validator started from the absorbed `history`, a receive
constraining only the replies its absorbed event recovers; a cost bound with an
error per occurrence is one from every history (`CostBound.charged`), and a
query count with every charge at most `bound` charges at most `budget * bound`
(`QueryBound.chargedCostBound`).

The charged certificate is the endpoint certificate. Per-occurrence
certificates, the round-by-round certificates of the construction model
(`RoundByRound.typed`), uniform-sort certificates of law interfaces and the
imports from ArkLib become charged certificates, and their theorems are
corollaries of the charged ones.

## The ideal experiment

The transcript oracle on all event histories is `OracleSpec.ofFn R`.
`Typed.answer key` asks it at `key`. The experiments are

```text
Typed.fixedExperiment absorb validator initial prover :=
  prover >>= fun proof => Typed.transform absorb Typed.ask validator initial proof

Typed.experiment absorb validator initial prover :=
  prover >>= fun (statement, proof) =>
    (statement, ·) <$> Typed.transform absorb Typed.ask
      (validator statement) (initial statement) proof
```

Both run under VCVio's lazily sampled `randomOracle`, from an empty cache: a
history asked for the first time receives a fresh uniform answer of its raw
type, and a repeated history its recorded answer. The prover and the transform
share the one oracle.

The adversary interface is:

- **Prover.** Any oracle computation on the transcript oracle: an adaptive
  computation with arbitrary internal state that may ask any history, including
  histories no honest execution produces, in any order and repeatedly.
- **Query accounting.** Every oracle key is charged the error of its last event
  (`ZkcSecurity.FiatShamir.Typed.keyError`), or, with a per-key charge, the charge of its last event
  after the history before it (`ZkcSecurity.FiatShamir.Typed.keyCharge`, which is `keyError` for a
  charge that ignores the history, `keyCharge_const`); a key that ends with no
  query occurrence of the validator can be charged zero. `WorstCaseCostBound prover ⟨keyError error⟩ proverCost`
  bounds the prover's charge on every path, counting repeated and cached
  queries. With every error at most `bound`, a prover with
  `IsTotalQueryBound prover queries` is charged at most `queries * bound`. The
  transform's own queries are charged on top of the prover's, also when they
  are cache hits.
- **Grinding.** Every candidate witness of a gated site is part of the key the
  prover asks, so every attempt is one charged query; grinding does not
  amortize.
- **Auxiliary effects.** None inside the oracle computation. For a fixed
  statement, private randomness sampled before it is a `ProbComp` distribution
  over provers, each bounded on its support.
- **Statement.** In `fixedExperiment` the statement is fixed: the validator and
  the initial history are chosen before the experiment. In `experiment` the
  prover chooses the statement after its queries, and the initial histories
  must determine the statements (`Zkc.Transcript.Determined`): if one statement's initial
  history followed by some events equals another statement's initial history
  followed by some events, the two statements are equal.
- **Event.** `Accepted accepts outcome`: the transform returns a value
  satisfying `accepts`; in the adaptive experiment, also for a false chosen
  statement. Stops never accept. The event ignores the unread proof suffix, so
  the bounds also cover verifiers that reject leftover proof data.

## The typed-site theorems

`ZkcSecurity.FiatShamir.Typed.adaptive_soundness_weighted`: if the false statements' validators are
doomed, every validator's queries charge at most `validatorCost`, the initial
histories determine the statements and the prover's queries charge at most
`proverCost`, then

```text
Pr[falseStatement result.1 ∧ Accepted accepts result.2.1
     | (simulateQ randomOracle (Typed.experiment …)).run' ∅]
  ≤ proverCost + validatorCost
```

`ZkcSecurity.FiatShamir.Typed.adaptive_soundness` is the case of errors at most `bound`, `queries`
prover queries and validators with at most `budget` queries:
`(queries + budget) * bound`. `ZkcSecurity.FiatShamir.Typed.soundness_weighted` and `ZkcSecurity.FiatShamir.Typed.soundness`
are the fixed-statement forms, and `ZkcSecurity.FiatShamir.Typed.randomized_soundness_weighted` and,
for adaptive statements, `ZkcSecurity.FiatShamir.Typed.randomized_adaptive_soundness_weighted` add
private randomness drawn before the oracle computation. Charging each key its
own error gives the sum over the asked keys; the uniform form is
`(queries + budget) * max` over the sites.

The per-key forms are `ZkcSecurity.FiatShamir.Typed.adaptive_soundness_charged`,
`ZkcSecurity.FiatShamir.Typed.soundness_charged`, `ZkcSecurity.FiatShamir.Typed.randomized_soundness_charged` and
`ZkcSecurity.FiatShamir.Typed.randomized_adaptive_soundness_charged`: a charged
certificate, validators whose queries from their initial histories charge at
most `validatorCost` (`ChargedCostBound`) and a prover whose queries charge at
most `proverCost` with every key charged `keyCharge charge` give the same bound
`proverCost + validatorCost`. The theorems with an error per occurrence are
their instances at the charge that ignores the history, and the uniform forms
follow from those; their statements are unchanged. A per-key charge discharges
neither obligation of the weighted bound: the all-table resampling bound and the
pathwise weighted budget are proved for each certificate. With law records, the
charge of a query site is `κ · ε + λ` at its key.

**One endpoint.** Every bound of this chapter is one application of the
keyed certificate `ZkcSecurity.FiatShamir.KeyedCertificate R game fails`: for a
game `game` on the lazily sampled oracle `OracleSpec.ofFn R` over any key space
(typed histories, or the joint keys of transcript queries and hash calls) and
an event `fails` of its result, a charge per key, a set of bad keys under each
answer table, the all-table resampling bound (`ResampleBound`: under every
background table, resampling the answer at a key makes it bad with probability
at most its charge) and the trace (on every table where the game fails, it
queries a bad key). `ZkcSecurity.FiatShamir.KeyedCertificate.soundness` bounds the probability of
`fails` by every pathwise charge bound of the game (`WorstCaseCostBound`),
through VCVio's weighted adaptive bad-query bound
`OracleComp.prEvent_randomOracle_le_of_bad_queries_weighted`; a mixture of games
drawn before the oracle computation is bounded by its worst game
(`ZkcSecurity.FiatShamir.KeyedCertificate.soundness_mixture`). Certificate transformers produce it:
`ZkcSecurity.FiatShamir.Typed.ChargedCertificate.keyed` and `keyedFixed` for the adaptive and the
fixed-statement experiments, and `ZkcSecurity.Commitment.keyed` for
[verifiers with committed tables](#verifiers-with-committed-tables).

The keyed certificate of the typed experiments works directly on the history
oracle, with no routing to library keys:

- **Bad keys.** `Zkc.Transcript.replay` walks a statement's validator from its initial
  history along a key's events, recovering received replies from the absorbed
  events and answering earlier queries by decoding the table. A key is bad
  (`ZkcSecurity.FiatShamir.Typed.BadKey`) when, for some statement, this reaches a doomed query whose
  occurrence is the key's last event and whose decoded answer at the key leaves
  the doomed set.
- **Resampling.** The key determines the statement and the replayed events, and
  replay reads the table only at histories no longer than the replayed prefix
  (`Zkc.Transcript.replay_congr`). Resampling the answer at a key therefore leaves the
  replayed residual unchanged, and the key is bad with probability at most the
  charge of the key under every background table (`ZkcSecurity.FiatShamir.Typed.badKey_resample_charged`
  for a doomed set indexed by the replayed history; `ZkcSecurity.FiatShamir.Typed.badKey_resample` for an
  error per occurrence).
- **Trace.** An accepting deterministic run from a doomed validator must leave
  the doomed set at one of its own queries, whose key is in the query log and is
  bad (`ZkcSecurity.FiatShamir.Typed.escape_logged_charged`, `ZkcSecurity.FiatShamir.Typed.escape_logged`).
- **Cost.** The transform charges at most the validator's cost
  (`ZkcSecurity.FiatShamir.Typed.transform_chargedCostBound`, `ZkcSecurity.FiatShamir.Typed.transform_costBound`), so the
  whole execution charges at most `proverCost + validatorCost`.

The proofs use four properties of the transform: every received reply is
determined by the event absorbed for it; every query is answered at the history
ending with its own occurrence, which is absorbed; every sent value is absorbed;
and histories only grow. A transform that did not absorb a prover message would
break replay, and with it the theorems. For adaptive statements the initial
history must also bind the statement.

## Composing certificates

Certificates of composite validators are assembled from **charged reductions**
`Typed.Reduction absorb Post charge`: a set of doomed pairs of an absorbed
history and a residual whose members meet the charged local obligations, with
a postcondition `Post history value` on returned values in place of rejection
(`ZkcSecurity.FiatShamir.Typed.ChargedStepTo`).

- `ZkcSecurity.FiatShamir.Typed.Reduction.bind`: a head's reduction with postcondition `Post₁` and, for
  every returned value, a reduction of the continuation, linked by
  `Post₁ history value → doomed₂ history (continuation value)`, give a reduction
  of the sequence.
- `ZkcSecurity.FiatShamir.Typed.Reduction.repeatN`: an invariant indexed by the absorbed history, the number
  of remaining iterations and the carried state, with one reduction per
  iteration whose returned states meet the invariant at one fewer iteration,
  gives a reduction of the bounded repetition that ends in the invariant at
  zero.
- `ZkcSecurity.FiatShamir.Typed.Reduction.union` and `Reduction.union₂`: branches under one charge, or under
  two charges both dominated by a common charge.
- `ZkcSecurity.FiatShamir.Typed.Reduction.receive`: a received message followed by one reduction per
  message.
- `ZkcSecurity.FiatShamir.Typed.Reduction.toCertificate`: a postcondition that implies rejection gives a
  charged certificate. Conversely every charged certificate is a reduction with
  the postcondition "not accepted" (`ChargedCertificate.toReduction`), and so
  are per-occurrence certificates (`Certificate.toReduction`) and uniform-sort
  certificates of law interfaces (`UniformCertificate.toReduction`).

## Path bounds

The query count `ZkcSecurity.FiatShamir.Typed.QueryBound`, the cost with an error per occurrence
`ZkcSecurity.FiatShamir.Typed.CostBound` and the charged cost `ZkcSecurity.FiatShamir.Typed.ChargedCostBound` are path
bounds of one combinator (`queryBound_iff`, `costBound_iff`,
`chargedCostBound_iff`). A walk (`Zkc.Transcript.Walk`) states at each position
which operations are admitted, a shape admissibility kept apart from charges,
what an operation costs, and which positions follow each reply;
`Walk.Bound walk process position budget` holds when every path from the
position admits its operations and charges at most the budget. Costs form an
ordered additive commutative monoid, so a vector budget with one coordinate per
resource is a cost. The combinators are shared: `Zkc.Transcript.Walk.Bound.mono` raises the
budget, `Zkc.Transcript.Walk.Bound.bind` sequences, `Zkc.Transcript.Walk.Bound.repeatN` bounds a repetition by
its count times the body's budget, and `Zkc.Transcript.Walk.Bound.convert` turns a bound into
one of another metric through a monotone additive map that dominates the target
walk's charges on the target walk's paths. A transcript interface walks either
its absorbed histories (`Interface.walk`), where a receive continues only with
the replies its absorbed events recover, or without positions
(`Interface.replyWalk`).

The metrics stay distinct, connected by proved conversions: transcript queries
(`Interface.queryCharge`), the weighted loss of a per-key charge
(`Interface.lossCharge`), counts of queries and messages
(`Interface.messageQueryCharge`), the hash chain's primitive calls
(`HashChain.callBound_iff`: receives and sends absorb, a query absorbs and asks
`width` counter blocks), and the commitment charges of verifiers with committed
tables with their shape admissibility (`Commitment.charged_iff`,
`Commitment.commitBound_iff`). A bound without positions holds at every history
(`replyWalk_walk`), and a query count becomes a charged cost through the
conversion `n ↦ n · bound` when every charge is at most `bound`
(`QueryBound.chargedCostBound_of_walk`). The executable instruction budget is a
separate operational contract: its exhaustion changes behaviour, and its
charges depend on executable environments and helper evaluation.

## Realized sampling laws

A protocol's round-by-round analysis bounds escapes under an ideal law, the
uniform law of the site's sort. A site's certificate obligation is under the law
its decoder realizes. `Realized decode factor slack` relates them for a decoder
`decode : B → Option R` of a uniform raw answer: every event `A` of the
successfully decoded value satisfies

```text
Pr[decode raw = some v ∧ v ∈ A] ≤ factor · Pr_uniform[A] + slack
```

The inequality is about the joint decoded value, so a block of values decoded
from one answer needs a joint law, not one per entry: copying one uniform bit
into both coordinates of a pair has uniform coordinates and factor two. Refused
answers belong to no event; their probability is a completeness quantity. A site
with ideal-law error `ε` and a realized decoder has decoded-law error
`factor · ε + slack` (`Realized.escape_le`). The realized shapes are:

- **Exact.** A bijective decoder has factor one and no slack
  (`realized_of_bijective`, `prEvent_of_bijective`), and so has reducing a
  uniform sample modulo a divisor of its range (`modulo_exact`). Field
  elements read from machine words of a binary field and power-of-two windows
  of uniform bit strings are of this kind.
- **Exact with refusal.** Masking a residue modulo `p` to `bits` bits below the
  largest multiple of `2 ^ bits` and refusing above it (`lowBitsRejecting`) is
  dominated with factor one (`lowBitsRejecting_realized`) and, since every value
  has exactly `⌊p / 2 ^ bits⌋` preimages (`lowBitsRejecting_fiber_eq`), its
  successful values have exactly the success probability times the uniform law
  (`lowBitsRejecting_exactWithRefusal`); it refuses with probability
  `(p mod 2 ^ bits) / p` (`prEvent_lowBitsRejecting_refuses`), `1 / p` for
  KoalaBear at 1 to 24 bits (`koalaBear_lowBitsRejecting_refuses`).
- **Point ratio.** If every value has probability at most `(1 + η) / |R|`, the
  factor is `1 + η` (`PointBound.dominated`, `Dominated.realized`). Masking a
  uniform residue modulo `p` to `bits` bits gives each value at most
  `⌈p / 2 ^ bits⌉` preimages (`lowBits_pointBound`). For KoalaBear,
  `p = 127 · 2 ^ 24 + 1`, so for `bits ≤ 24` the factor is
  `1 + (2 ^ bits - 1) / p` (`koalaBear_lowBits_dominated`): `1 + 65535 / p` at 16
  bits, with excess between `1 / 32513` and `1 / 32512`, and `1 + 2097151 / p` at
  21 bits, with excess below `1 / 1016`. Reducing a uniform 256-bit integer
  modulo the BLS12-381 scalar order `r`, as EIP-4844 derives its challenges from
  SHA-256, has factor `3r / 2 ^ 256`, between `1.3585` and `1.3586`
  (`bls12381_reduce_dominated`). Reducing a uniform sample below `N` modulo the
  field size has factor at most `1 + |F| / N` (`dominated_reduce`).
- **Additive loss.** `Balanced decode loss`, every event at most `loss` likelier
  than under the uniform law, is factor one with slack `loss`
  (`Balanced.realized`). `balanced_of_fibers` gives loss `|F| / |B|` when no
  value has more than `|B| / |F| + 1` preimages, and `balanced_reduce` gives
  loss `|F| / N` for reduction modulo the field size of a sample below `N`.

A multiplicative factor scales with the event and an additive loss does not:
for a 16-bit KoalaBear mask the additive loss is `65535 / (p · 2 ^ 16)`, about
`2 ^ -31`, which no smaller round error survives, while the factor costs
`1 + 2 ^ -14.99`. For EIP-4844's reduction the additive bound `balanced_reduce`
gives is `r / 2 ^ 256`, about `0.453`, and even the exact statistical distance,
about `0.0747` by direct computation, is far above any round error, while the
factor is about `1.36`.

Independent coordinates of a uniform answer multiply point bounds
(`prEvent_uniform_prod`, `prEvent_uniform_pi`, `PointBound.prod`,
`PointBound.pi`), and a site that reads one coordinate of a uniform pair keeps
its factor (`Dominated.comp_fst`, `Dominated.comp_snd`). These are the proved
factorizations from which joint laws of pairs and blocks follow.

### Law records

A law record `LawRecord Raw Value` (`ZkcSecurity.Transformations.FiatShamir.Laws`) is the
proof-bearing realized law of a request class, stated on the raw answer: a
decoder `decode : Raw → Option Value`, a coefficient `factor` and a slack
`slack` in `[0, ∞]` with `Realized decode factor slack` against the uniform law
of the sort, and a refusal bound `refusal` with
`Pr[decode raw = none] ≤ refusal`, a completeness quantity. The ideal law of the
sort is its uniform law: uniform field elements, `UniformIndex(N)` for an index
below `N`, and the product law of a block, which is the uniform law of the
function type. A gated accepted-value decoder may have a coefficient below one. A
site with ideal-law error `ε` escapes with probability at most
`factor · ε + slack` (`ZkcSecurity.FiatShamir.LawRecord.escape_le`).

Five constructors present a record from a checked claim about the realized
subdistribution `μ` against the ideal law `ν`:

- `ZkcSecurity.FiatShamir.LawRecord.exact`: a total decoding with `μ = ν` (`ExactLaw`); a bijection is
  exact (`exactLaw_of_bijective`), and so is any total decoding dominated with
  factor one, because the complements of its events are dominated too
  (`Dominated.exactLaw`).
- `ZkcSecurity.FiatShamir.LawRecord.exactWithRefusal`: `μ = p_success · ν`
  (`Obligations.ExactWithRefusal`), with the success probability as coefficient;
  a decoder whose every value has the same number of preimages is of this kind
  (`exactWithRefusal_of_fibers`).
- `ZkcSecurity.FiatShamir.LawRecord.dominated`: `μ ≤ κ · ν + λ` with refusal allowed. It suffices for
  soundness but says nothing about the success-conditional law: a decoder that
  returns `0` on one outcome of a fair bit and refuses on the other is dominated
  with coefficient one but not exact with refusal
  (`TestsSecurity.LawRecords.constantOnSuccess_not_exact`).
- `ZkcSecurity.FiatShamir.LawRecord.pointRatio`: `μ(x) ≤ κ · ν(x)` for every value (`PointRatio`,
  `PointRatio.realized`).
- `ZkcSecurity.FiatShamir.LawRecord.additive`: a total decoding with coefficient one and its additive
  loss as slack (`Balanced`).

`ZkcSecurity.FiatShamir.LawRecord.gated` is the accepted-value decoder of a gated site: from gate bits
and a challenge answer it refuses unless the gate passes, with coefficient and
slack a bound on the gate's passing probability times the challenge record's
(`gated_realized`) and refusal at most a bound on the gate's failure probability plus the
challenge's refusal. The sampling lemmas above instantiate the constructors:
`ZkcSecurity.FiatShamir.LawRecord.identity` and `ZkcSecurity.FiatShamir.LawRecord.modulo` (exact), `ZkcSecurity.FiatShamir.LawRecord.lowBitsRejecting`
(exact with refusal), `ZkcSecurity.FiatShamir.LawRecord.koalaBearLowBits` (point ratio
`1 + (2 ^ bits - 1) / p`, `koalaBear_lowBits_pointRatio`),
`ZkcSecurity.FiatShamir.LawRecord.bls12381Reduction` and `ZkcSecurity.FiatShamir.LawRecord.koalaBearCompound` (dominated),
`ZkcSecurity.FiatShamir.LawRecord.reduce` (additive, loss `|F| / N`) and `ZkcSecurity.FiatShamir.LawRecord.koalaBearQueryPhase`
(gated, with the factor of `koalaBear_queryPhase_realized`,
`ZkcSecurity.FiatShamir.LawRecord.koalaBearQueryPhase_factor`).

## Gated and compound sites

**Gated sites.** A gated site squeezes, from one absorbed prefix ending with the
prover's witness, both a proof-of-work test and the challenge it gates: its
answer decodes to gate bits and a challenge, and the validator rejects unless
the gate passes. This is ethSTARK's proof-of-work model (Theorem 6). If every
failing gate value leads to a doomed residual, the gated query escapes with
probability at most the probability of the passing gate value times the escape
probability of the continuation at that value (`gated_step_le`,
`gated_escape_le`). As a realized law: if the gate passes with probability at
most `ρ` and the challenge is realized with `factor` and `slack`, the decoding
that refuses unless the gate passes is realized with `ρ · factor` and
`ρ · slack` (`gated_realized`). The product follows from the independence of the
two coordinates of a uniform pair. `ρ` is `2 ^ -b` for uniform bits and at most
`(1 + (2 ^ b - 1) / p) / 2 ^ b` for the low `b` bits of a KoalaBear element
(`koalaBear_lowBits_pointBound`). At zero difficulty the gate has one value,
which passes with probability one (`lowBits_zero_difficulty`,
`prEvent_lowBits_zero_difficulty`), so the gated bound is the ungated one.

**Finite honest search.** `BoundedSearch.run` visits an ordered list of
candidates, stops at the first accepted decoded value, and returns both the
candidate/value and the number of attempts actually spent. An exhausted list
returns `none`. `returned_valid` connects a returned witness to a successful
trial; `attempts_le` bounds the counter on every structural execution.
For fresh probabilistic trials, `exhaustion` is the product of their failure
probabilities. A lower bound `success` on accepting the *complete* trial gives
exhaustion at most `(1 - success)^N`. Thus decoder refusal is part of the
completeness bound. `expectedAttempts_eq_sum` gives the actual expected count
as `sum (failure^j), j < N` for equal failure probabilities, and
`expectedAttempts_le_sum` gives the corresponding upper bound for varying laws.

These are fresh-trial theorems. Applying them to a cached random oracle needs
a freshness and simulation theorem for the selected construction. The
`TestsSecurity.BoundedSearch` control reuses one sampled answer twice and proves
that its exhaustion probability is one half, while two fresh trials exhaust
with probability one quarter. No independence follows merely from identical
marginals or repeated witness evaluation. `queryBound` separately multiplies
an explicit primitive-call bound per trial by the candidate count; a logical
gated request need not be one physical hash call. The native search,
state-advance and exhaustion behavior, zero-difficulty bypass, and multi-block
provider simulation require their own construction connection. This module
does not establish those connections.

**Compound sites.** A compound site decodes one answer into several values, for
example the `s` query positions of a FRI query phase squeezed from one absorbed
prefix. Its error is the joint escape probability of the block under the uniform
law of the block, times the block's factor; for the FRI query phase over a
committed word at relative distance at least `δ` from the code, at a proximity
radius `θ` in the unique-decoding regime or up to the cube-root radius and with
commitments read as the committed words, that law gives `(1 - min θ δ) ^ s`
([FRI security](fri-security.md)). Positions masked from `s` uniform KoalaBear
elements have factor `(1 + (2 ^ bits - 1) / p) ^ s`
(`koalaBear_compound_dominated`). A query phase gated by a proof-of-work
combines both (`koalaBear_queryPhase_escape_le`, `koalaBear_queryPhase_realized`).
With a 16-bit proof-of-work and 100 positions of 21 bits, the phase escapes with
probability at most `32513 / p` times `(1 + 2097151 / p) ^ 100` times the block's
uniform-law error (`koalaBear_benchmark_queryPhase_escape_le`); the block factor
is below `1.104` (`koalaBear_benchmark_block_factor_le`), less than `0.143` bits.
These are errors of one query site; a complete Fiat–Shamir bound charges the
site errors along every prover query and validator path
(`adaptive_soundness_weighted`).

## Raw answers by the last event and lifting

In the history class the request is the last event of its TranscriptQuery, so
the raw answer type of a key is a function of its last event
(`ZkcSecurity.ProgramLogic.Transcript.Lifting`). `Typed.ByLast Raw key` is `Raw` of the key's
last event, and `Unit` at the empty key, which no query reaches; it is uniform
when every `Raw event` is (`ByLast.sampleable`). At a key `preceding ++ [event]`
the answer reads as a value of `Raw event` (`ByLast.read`), with the same
uniform law (`prEvent_read`): `ByLast Raw` is the history oracle that reads by
occurrence (`ReadsByOccurrence (ByLast Raw) Raw`).

A **law interface** `Typed.LawInterface I E P Raw` presents a validator's
operations to the transform with every query decoded by a law record from the
raw answer of its occurrence into the operation's reply sort; its transcript
interface is `LawInterface.absorb`. A **uniform-sort certificate**
`Typed.UniformCertificate laws accepts error` is a round-by-round certificate,
with doomed pairs of an absorbed history and a residual, in which a doomed
query's uniform reply of its sort leaves the doomed set with probability at most
`error history operation` (`ZkcSecurity.FiatShamir.Typed.UniformStep`), the form a protocol's own
analysis produces. It lifts to a charged certificate over `LawInterface.absorb`,
with the same doomed pairs, whenever every query's charge at a history covers its
record's `factor · error + slack` there (`UniformCertificate.charged`).
Law-record decoders read only the raw answer: the operands they depend on are
carried in the occurrence. In `TestsSecurity.LawRecords` a validator with an
exact challenge in `Fin 5` and a gated block of positions has uniform errors
`1 / 5` and `1 / 4`; the lifted certificate charges `1 / 5` and `1 / 2 · 1 / 4`,
and the typed engine bounds its acceptance by `(queries + 2) / 5`. A loop that
draws twice at one occurrence, with first-round error `1 / 4` and second-round
error `1 / 2`, is charged `1 / 4 + 1 / 2`.

A doomed set and errors that ignore the history give the per-occurrence form:
a **history-free uniform-sort certificate** `Typed.UniformEventCertificate laws
accepts error`, with an error per operation, lifts to a per-occurrence
certificate over `LawInterface.absorb` whenever every query occurrence's error
covers its record's `factor · error + slack` (`UniformEventCertificate.typed`,
`UniformEventStep.typed`). The FRI verifier's typed step is this lifting: its law
interface reads the folding challenges exactly and decodes the query block by
its sampler's realized law, a refusal at every other block shape
(`ZkcSecurity.Examples.FriFiatShamir.laws`, `typedStep`).

Requests with different result sorts go through one interface. In
`TestsSecurity.HeterogeneousRequests` a validator receives a claim and asks a
field element, an index below a bound its request carries, read from a raw
answer below twice the bound reduced modulo it (an exact law), and a block of
two field elements. The raw answer type depends on the request's bound, so the
oracle reads by the last event. The uniform-sort certificate lifts through the
law interface, the weighted fixed-statement theorem bounds every prover by its
charge plus `1 / 5 + 1 / 3 + 1 / 5`, and the query-free prover is accepted with
probability exactly `43 / 75`, one minus the product of the three miss
probabilities, below the bound `11 / 15`.

## Binding codecs

`Zkc.Transcript.Determined` quantifies over every statement the prover can output,
malformed ones included, so a codec that discharges it is injective and
prefix-free on the whole statement type (`ZkcSecurity.Transformations.FiatShamir.Binding`). A **binding codec** `BindingCodec Stmt E` is an
injective, prefix-free encoding of statements as initial histories, and it
discharges `Zkc.Transcript.Determined` (`BindingCodec.determined`). Binding a statement as
one typed public-value binding event is such a codec when the event embeds
injectively into the transcript events and the row determines the statement
(`BindingCodec.single`, `determined_single`). In `TestsSecurity.BindingCodecs`
the raw Sumcheck statement (table values, claim and round count, with no length
check) is bound by one event and determined, while binding the table entries one
event each with no count or length is not prefix-free and is not determined.
A binding codec establishes statement determination only; that the native
transcript absorbs the encoded rows, in order, belongs to the encoding and
transcript-state [obligation](#obligations).

The host binds the policy's statements, its public inputs in policy order,
while a library's theorem is about the model's statements. A **statement
binding** `StatementBinding Policy Model E` pairs a binding codec of policy
statements with the relation between policy and model statements, required to be
functional: a policy statement denotes at most one model statement.
Determination transfers through it: a policy statement's initial history,
followed by any events, determines its model statement
(`StatementBinding.determines`); choosing a denoting policy statement for every
model statement gives model histories that determine the statement
(`StatementBinding.determined_represent`); and a policy statement is false
exactly when its model statement is (`falsePolicy_iff`). In
`TestsSecurity.StatementBindings` a relation that is not functional breaks the
transfer.

Determination says nothing about a policy statement that denotes no model
statement (`StatementBinding.Unmapped`): under the empty relation every policy
statement is unmapped and none is false in the model, so the modeled event
cannot see an accepted statement the application calls false. An adaptive
endpoint needs coverage of the application's false statements in one of two
forms. Either every application-false policy statement is false in the model or
unmapped (`StatementBinding.Covers`) and, as a separate obligation, the
validators of unmapped statements are doomed
(`StatementBinding.RejectsUnmapped`), which together make the validators of all
application-false statements doomed when those of model-false statements are
(`StatementBinding.doomed_of_covers`); or the application's false-acceptance
event implies the modeled event (`EventImplication`), which transfers the bound
(`EventImplication.prEvent_le`). Coverage and rejection are separate registry
obligations with separate schemas, so evidence for coverage does not stand for
rejection. `TestsSecurity.StatementBindings` shows the gap with the empty
relation and a validator that accepts every statement: an accepted false
statement is invisible to the modeled event, coverage holds only through
unmapped statements, and the rejection it then requires fails.

Statement determination is the first of four binding obligations. The other
three are typed obligation structures, each with its claim and its status
(`ObligationStatus`: a proof, or a reported assumption that cites an entry of
the obligation's own category in the registry `Zkc.Verification.Claims.Registry`, found by
its identifier with `registryEntry`):

- **Collision-bounded identity** (`CollisionBoundedIdentity`): a collision game
  over every digest in scope, whether computed at setup, recomputed by the
  verifier or given before the protocol (`DigestOrigin`), with its bound at
  every budget.
- **Authenticated configuration** (`AuthenticatedConfiguration`): the
  configuration is fixed before the adversary is quantified, it comes from a
  compile-time constant or a pinned asset (`Provenance`), and the security claim
  holds at every attacker-selected parameter in its admissible range.
- **Verification-key correctness** (`VerificationKeyCorrectness`): the key in use
  is the intended one, by checked recomputation, a certificate or a realization
  theorem (`KeyEvidence`).

## Imports from ArkLib's round-by-round soundness

`ZkcArkLib.FiatShamir.Upstream` imports ArkLib's worst-case-per-prefix
round-by-round soundness (`Verifier.rbrSoundnessWorstCase`) into the typed
engine. An ArkLib verifier for a protocol specification of `n` rounds has a
**process form** (`validator`): one operation per round (`signature`), receiving
a prover message at a message round and querying the challenge at a challenge
round, in round order, then returning the verdict on the full transcript. The
verdict is read from the verifier's `Verifier.GuardedForm`: the verifier outputs
a deterministic statement where a Boolean guard passes and fails elsewhere,
which covers verifiers that reject by `guard` or any other `OptionT` failure. The
process returns the output where the guard passes and no output where it fails
(`guardedVerdict`), and only an output in the output language accepts
(`Accepts`). A pure verifier (`Verifier.PureForm`) is the guard that always
passes (`Verifier.PureForm.toGuardedForm`). A verifier that queries oracles of
its own or samples has no guarded form and is not covered. The process form's
transcript interface (`absorb`) binds the statement as one event (`initial`,
which determines it), absorbs a message with its round, and reads a challenge
from the raw answer of its occurrence, uniform on the round's challenge type.

`ofWorstCase` turns a worst-case proof into a `ZkcSecurity.FiatShamir.Typed.Certificate` of the process
form: the doomed residuals are those at false states of false inputs, prover
messages keep them doomed by the state function's `toFun_next`, a doomed full
transcript is rejected by `toFun_full` read through the guarded verdict
(`verdict_rejected`: the guard fails or the output is outside the output
language; `prEvent_verdict_eq_zero` is the converse a guarded verifier's state
function uses), and a challenge round's escape is the worst-case bound for the
fixed prefix. Each challenge occurrence is charged its round's error
(`eventError`); the events carry the round, so the error is per occurrence and
`Certificate.charged` gives the charged form.

The process form queries once per challenge round and nowhere else: its query
count is the number of challenge indices (`validator_queryBound`), and its
queries charge the sum of the challenge rounds' errors (`validator_costBound`).
`worstCase_soundness_weighted` and `worstCase_adaptive_soundness_weighted` bound
the transform's acceptance of a false input by the prover's charge, each prover
query charged the error of the challenge round its key ends with, plus that sum,
for fixed inputs and for inputs the prover chooses after its queries.
`worstCase_soundness` and `worstCase_adaptive_soundness` are the uniform forms,
`(queries + challenges) · bound` for `challenges` challenge rounds when every
round's error is at most `bound`.

`TestsArkLib.UpstreamImports` checks the import on two protocols:

- A two-round guessing protocol with a pure verifier and error `1 / 4`: the
  transform accepts with probability at most `(queries + 1) / 4`, and a prover
  that sends a guess without querying is accepted with probability exactly
  `1 / 4`, so the experiment accepts and the bound at zero queries is attained.
- A four-round protocol with two challenge rounds of unequal error, `1 / 2` and
  `1 / 4`, whose verifier rejects by guard failure: the weighted bound is the
  prover's charge plus `3 / 4`, so `3 / 4` without queries, where the bound with
  the largest error at every query, `(queries + 2) / 2`, is vacuous; a prover
  that sends two guesses without querying is accepted with probability at least
  `1 / 2`.

The averaged form `Verifier.rbrSoundness` is not imported: its bound is over a
mixture of prefixes the prover samples, not a per-prefix step.

The import of ArkLib's interaction-stack soundness (`OrdinaryState` and
`LocalSoundness`) is outstanding adapter and instance work. The implementation
attempted so far met three obstacles:

- its protocols are trees whose residuals and execution prefixes
  (`ExecutionPrefix`) live in `Type 1`, while a validator's operation signature
  is in `Type`, so a process form over those trees does not fit an operation
  signature;
- its challenge models (`ChallengeModel.sample`) sample an arbitrary
  distribution rather than a uniform raw answer;
- the one interaction-stack instance, Sumcheck's local soundness model, is
  private to its module.

These are obstacles of that implementation, not prerequisites of every
adapter. A restricted route, not yet checked, keeps the upstream execution
prefix inside a propositional realization relation instead of an operation
signature, and defines the doomed participant residuals as those that realize
the residual of some false upstream prefix, as `Realizes.certificate` does for
process forms. It requires correspondence for messages, actual prefix
extensions, challenge distributions, and rank and error charges. Non-uniform
sampling stays an explicit law premise relating each challenge model to a
uniform raw answer, and the private Sumcheck instance blocks only the reuse of
that instance, not the generic adapter.

## Role separation and transcript constructions

The ideal model is a random oracle on typed transcript histories whose answer at
a gated or compound key is the whole tuple the site decodes. Deployed transcripts
realize it from a hash function or permutation:

- **Hash chain.** A chain of full-digest calls of one byte hash, read as a
  random oracle, as in the
  [native hash-chain suites](../../../docs/spec/ir/construction.md#native-hash-chain-suites):
  one call binds the first event, each further absorbed event is one call on the
  current digest and the event's frame, and a request's answer is read from
  counter-block calls at the current digest. It needs an injective, prefix-free
  encoding of events and requests with distinct role tags. The digest after a
  history then stands for that history: outside a bad event of the joint
  primitive-query trace, a fresh call that returns a digest an earlier call
  already generated (a collision) or already read as a state (a prediction), the
  chain is one oracle on histories, with loss at most `(q + V)² / |S|` for `q`
  adversary calls and `V` verifier calls ([provider simulations](../support.md)).
  Several outputs read at one key with distinct tags are role-separated answers
  of that oracle.
- **Duplex sponge.** Absorbing the encoded history and squeezing the answer
  stream. It needs the same injective encoding and the sponge idealization: the
  squeeze stream after an absorbed prefix acts as a random oracle on absorbed
  prefixes (Chiesa and Orrù prove this in the ideal-permutation model). The
  squeezes from one absorbed prefix form the tuple a gated or compound site
  decodes; a separate proof-of-work hash call is a further role under the same
  idealization.

**Role separation at one key.** For a uniformly random function on a finite
input space, the answers at distinct role inputs are independent and uniform
(`prEvent_roles`); in particular a proof-of-work test and a challenge read from
two distinct inputs have the law of a uniform pair (`prEvent_roles_gate`), which
is the law the gated-site results assume.

**Provider simulation.** Turning a deployed provider into one oracle on
transcript histories with product answers also needs a simulation of the whole
interaction: the prover's direct calls of the hash function or permutation,
states shared between calls, collisions between derived inputs, and the query
cost of each grinding attempt. This is a separate obligation of each transcript
construction, stated with the idealization above; role separation at one key
does not discharge it. Its type is fixed in
[provider simulations](../support.md), where it is proved for the
hash-chain suites' byte-level chain model; for the duplex suites it remains a
named obligation.

## Verifiers with committed tables

`ZkcSecurity.Commitment` bounds a verifier that sees roots and openings instead of
committed tables by the typed certificate of its ideal reading.

- **Verifiers.** A verifier with committed tables is a process over
  `committed J Shape Value`: the operations of a typed transcript interface, the
  commitment of a table of a given shape, and the read of one entry of a
  committed table. Its ideal reading `withTables` receives every committed table
  in the clear through a word operation of `J` and answers reads from the
  received tables. Its concrete reading `run` reads a root from the proof for a
  commitment and absorbs it, takes the next opening of the proof for a read and
  authenticates it against the root with hash calls, and asks the transcript
  oracle at each query.
- **Joint oracle.** One lazily sampled oracle answers transcript keys and hash
  calls (`joint`). A transcript key is the absorbed history before a query and
  the query's occurrence, answered in the occurrence's raw type `R [occurrence]`.
- **Extractable commitments.** `Extractable` states two deterministic laws of a
  straight-line extractor reading the record of hash calls: an opening accepted
  by recorded calls agrees with the extraction from a record without two calls
  answered alike, and recording one more call changes an extraction only when
  the call is new and is answered by the root or an earlier input label. Merkle
  trees with raw leaves satisfy them through VCVio's transcript extractor
  (`ZkcSecurity.Commitment.MerkleTrees.scheme`), and Merkle trees with hashed leaves through a leaf
  layer (`ZkcSecurity.Commitment.LeafHashing.scheme`).
- **Checkpoints and the event.** The tables committed by a transcript key's roots
  are extracted from the hash calls before the key's first query
  (`checkpointExtract`). `FalseAcceptance` holds when the verifier accepts and the
  statement is false for its tables extracted at the checkpoint of one of the
  verifier's transcript queries; it is empty for a verifier without transcript
  queries.
- **Theorem.** `soundness_weighted`: in the joint experiment
  (`experiment`), the probability of `FalseAcceptance` is at most the prover's
  charge plus the verifier's charge, where a transcript key is charged the error
  of its occurrence in a typed certificate of the ideal reading, the certificate
  that also gives the ideal reading's
  [typed-site bound](#the-typed-site-theorems), and every hash call is charged
  `targetBound / |Y|`. `soundness` takes `targetBound` from query counts:
  `(rootBound + inputBound + 1) · (proverQueries + verifierQueries)`, where
  `rootBound` bounds the roots of the verifier's transcript keys and `inputBound`
  the input labels of one hash call. The premises on the verifier are
  structural: committed tables are received by receives of the ideal reading,
  the statement's roots are the roots of its initial history, the verifier
  commits at most `rootBound` roots counting the statement's, the ideal reading's
  word operation carries every extracted entry, and a false statement's ideal
  reading is doomed.
- **Charged certificates.** `soundness_charged` takes a charged certificate of
  the ideal reading, whose doomed set and charge are indexed by the ideal
  reading's absorbed history. That history contains tables where the concrete
  history contains roots: an ideal history (`IdealHistory`) reads a concrete
  history through an extraction, and `CommitDoomed` keeps the doomed set across a
  commitment, which word messages give (`WordMessages.commitDoomed`). A
  transcript key is charged a concrete-key charge that dominates the ideal
  charge at the key's history read through every extraction; because the
  checkpoint extraction is fixed before the key's answer, resampling the answer
  stays bounded by the charge at the frozen extraction, and the all-table
  resampling bound of the per-occurrence case carries over
  (`bad_transcript_resample_charged`). `soundness_weighted` is its case for a
  per-occurrence certificate (`IdealHistory.events`), and `soundness` is
  unchanged.
- **Proof.** One application of the keyed certificate (`keyed`) of the joint
  oracle. A transcript key is bad when, for a statement whose initial history
  begins the key's history, the replay of the statement's verifier along the rest
  of that history, with every root read as its checkpoint extraction, reaches a
  doomed query whose answer at the key escapes; a hash call is bad when its answer hits a target of the
  record before its first query: an earlier answer, an earlier input label, or one
  of the first `rootBound` roots of an earlier transcript key, whoever queried
  it. Without a bad hash call the record is good: distinct calls have distinct
  answers (`responseInjective_of_good`), every checkpoint extraction of a root of a
  transcript key equals the extraction from the whole record
  (`extract_checkpoint_eq`), and an accepting concrete run is an accepting ideal
  run on the extracted tables, so it escapes the doomed set at one of its own
  transcript queries (`runTable_escape`). The proof does not use that reads
  follow the verifier's last query.
- **The committed-opening experiment.** `intendedBound` proves `IntendedBound` of
  [the committed-opening experiment](../support.md) for a
  straight-line extractor that reads the tree with hashed leaves committed by the
  checkpoint key's root, with the empty row where nothing is extracted, at factor
  `1`, extraction term `(q_M + k + 1) · 4 (q_T + q_M + k + 2) / |Digest|` and
  namespace term `0`, for the absorbed and the omitted terminal opening. An
  extractor that returned no table when a row is missing would make the
  proposition false. `CommittedOpeningBridge.soundness` applies the general
  theorem to the same verifier with every premise discharged.
- **Charges.** `Charged` bounds every path of a verifier with committed tables:
  a transcript query is charged its occurrence's charge, a read a fixed charge,
  and every committed shape is admissible. When every authentication at an
  admissible shape makes at most `authCalls` hash calls, the concrete reading
  inherits the bound as a worst-case cost (`run_costBound`) and as a query count
  (`run_queryBound`).
- **FRI.** [Committed words](fri-security.md#committed-words) applies the theorem
  to the FRI verifier.

### Shared batch authentication

`ZkcSecurity.Commitment.BatchOpening` relates a recorded binary frontier to its
parents and then to one root. Active siblings share a recorded compression;
a missing sibling consumes exactly one boundary digest. Each layer preserves
the remaining proof suffix. The root rule fixes the depth, root index and empty
suffix. `ZkcSecurity.Commitment.BatchOpening.Reduction.proof_length` derives the exact boundary demand from the
verifier's frontier, independently of hash assumptions.

`ZkcSecurity.Commitment.BatchOpening.Reduction.paths` recovers a `ZkcSecurity.Commitment.LeafHashing.Climbs` witness for every active leaf
from the same log. It does not rehash each scalar path. `RowsRecorded` preserves
the complete ordered request and whole-row lists, including repeated positions.
`batch_agrees_or_collision` proves that the existing extractor returns that
entire row list or two different complete hash queries in the log have the same
answer. The hash is not assumed injective; a quantitative collision reduction
belongs to the selected provider model.

The relation is library mathematics, not a second verifier. A source/native
connection must derive its witnesses from the actual accepted batch execution,
including sorted unique frontier construction, duplicate consistency, actual
height and width, codecs, shape, complete proof consumption and all refusal
outcomes. The derived `index < 2^depth` is not the stronger actual-height check
for non-power-of-two tables. The theorem neither binds shape through an
untagged root nor identifies the pre-challenge extraction checkpoint. Logical
query coverage, source association, shared provider history and application bad
event coverage remain separate required premises of a realized security claim.

`BatchVerification.verifyFramed` is an independent formal interpretation of
the binary, single-table, cap-zero pruned walk. It checks actual-height bounds,
row framing, unconditional duplicate-row agreement, verifier-derived boundary
count, row codecs, and complete proof consumption. Invalid requests stop with
`refused`; malformed authentication returns false; decode reservation failure
stops with `exhausted`. Shared parents issue one hash call each. The successful
execution theorem derives `Reduction` and `RowsRecorded` from its actual hash
history, together with the exact unique-leaf and grouped-compression count.
These counts are at the `LeafHashing` leaf-computation and node-compression
interface. A Poseidon sponge leaf can expand into several shared permutation
calls; the leaf and node primitive input ranges need not be disjoint.

`verify_agrees_or_collision` applies the existing extractor to that same log.
Completeness is currently relative to an answer-consistent recorded reduction;
it is not yet the honest native commit/open theorem. The operation is not a
proof of Rust execution. A realization must connect the selected decoder and
row framing, native lead-path restoration, primitive hashing, logical reads,
and the pre-challenge extraction checkpoint. It must also provide the provider
loss and application event implication required above.

`DecoderConsistent decode log` weakens the sufficient record premise to the
role actually decoded. Equal labels for two queries recognized by `decode`
must produce the same decoded value. `batch_agrees_of_decoderConsistent` uses
one law for node children and one for leaf rows. Cross-role aliases are allowed;
the first-match extractor and the complete ordered batch are unchanged. Global
response injectivity implies both laws and still supplies the existing
`batch_agrees` theorem. These deterministic conditions carry no probability
bound by themselves.

`BatchVerification.verify_agrees_in_record_of_decoderConsistent` derives the
same agreement from the actual successful batch operation when its query log
is included in that record. `verify_agrees_at_checkpoint` uses the existing
`GoodFrom` invariant, exact transcript-key membership and committed-root bound
to move agreement to the prefix before that key's first query. Log inclusion
alone proves neither chronological source association nor checkpoint stability.

`verify_complete` proves completeness of the entire decoded operation from an
answer-consistent tree reduction, public shape and allocation bounds, and
valid selected rows. The reduction determines the exact proof length.
`verify_table_complete` additionally discharges duplicate consistency and
representative selection for rows read from one fixed table, preserving the
original request order. An independent tree witness exercises this theorem;
acceptance is not used to manufacture its premise.


### Fixed extraction from a shared permutation record

`Commitment.PoseidonRows` defines a straight-line extractor from the full shared
permutation record. The request fixes the positive flattened row width, actual
height, depth and zero completion. Extraction normalizes repeated oriented pairs
in first-exposure order, descends the recorded Merkle path, and recovers the
overwrite sponge backwards through capacity links. It uses forward-born pairs;
inverse-born pairs retain their original direction even after a forward cache hit.
The last partial block checks the retained rate suffix. Exact block boundaries
introduce no extra padding call. Leaf and node inputs may alias.

`SpongeTrace`, `NodeClimb` and the existing `BatchOpening.Reduction` describe
concrete recorded operations. Their generic theorems derive extraction agreement
for ordered scalar/batch readings, including duplicate positions. The extractor
does not choose a witness or use a supplied successful decoder. Request height
excludes padded leaves independently of Merkle depth.

`PoseidonRows.Monitored.handler` constructs the history through one two-sided
ideal lazy permutation. Every primitive call is recorded, including cache hits,
inverse queries, prequeries and calls in computations that later fail. Successful
allocation attempts create physical markers and retain root occurrences, including
duplicates. Over-budget allocation returns false without silently registering
roots. Extraction uses the first marker for its key.

The support invariant proves that the absence of the charged bad event implies
`GoodHistory` for this actual history. Forward queries test sampled output
coordinates; inverse queries test sampled input coordinates. The inverse query's
adversary-chosen output is not treated as random. Root and capacity protection
prevent later exposure from changing an earlier checkpoint extraction.

`ZkcSecurity.Commitment.PoseidonRows.Monitored.extraction_disagreement_le` bounds disagreement for any concretely
recorded scalar or ordered batch operation, including zero completion. With
`d = |Fin rate → F|`, total primitive budget `Q`, and enforced root-occurrence
budget `b`, its bound is

```text
min(1, d * (5 * (Q * (Q - 1) / 2) + (b + 4) * Q) / (d^2 - Q)), if Q < d^2;
1 otherwise.
```

The triangular expression is natural-number arithmetic before casting to
`ENNReal`; the final fraction is `ENNReal` division. Allocation attempts do not
consume the primitive budget. Private randomization may select a reply-adaptive
program with the same all-path budget. The theorem reuses VCVio's potential
composition theorem and the shared lazy sampler. It is not an eager-permutation
equivalence theorem.

A source realization must derive the recorded-operation witnesses and align the
request, allocation identity and primitive budget with the actual accepted
execution. This library theorem is relative to the stated ideal primitive access
model. It does not assert a result for unrestricted local computation of the
public fixed Poseidon2 permutation or a native Rust refinement.

## Stage relations

A verification stage relates two attack games (`ZkcSecurity.Stage`). A game
(`Stage.Game`) packages an adversary class, budgets, the admissibility of an
adversary at a budget, and the probability of the game's bad event for each
adversary. A **stage relation** `Relation Src Tgt` bounds the target game by the
source game: a target adversary admissible at `b` is translated, with private
randomness allowed, into source adversaries admissible at the transported
budget `budget b`, and its bad probability is at most the worst translated
adversary's plus the loss `loss b`.

```text
Tgt.bad A ≤ ⨆ A' ∈ support (translate b A), Src.bad A' + loss b
```

The bound is against the worst adversary in the translation's support, not the
average over the translation's randomness: a translation that succeeds with
small probability can determine the supremum. This suffices for bounds that
hold at every budget for every admissible adversary, which is how the stages
are used; a stage that preserves a randomized translation's average success,
as a computational reduction does, is not of this form.

Composition runs the translations in sequence and transports budgets before
evaluating the earlier stage's loss: the loss of `first.comp second` at `b` is
`second.loss b + first.loss (second.budget b)` (`ZkcSecurity.Stage.Relation.comp`, `comp_loss`).
Composition has the identity relation as unit and is associative (`id_comp`,
`comp_id`, `comp_assoc`). A bound on the source game transfers to the target at
the transported budget with the loss added (`ZkcSecurity.Stage.Relation.transfer`); a bound on a
game is a relation from the trivial game (`ZkcSecurity.Stage.Relation.ofBound`), so a chain of
stages ending in an endpoint theorem is one relation from the trivial game whose
loss is the end-to-end bound (`ZkcSecurity.Stage.Relation.bounded`). The generic relation is available independently of any compiled endpoint.
Native realization and actual-source installation must supply their own exact
execution or event-transfer premise, including the resource map and all reached
stops. The former concrete joint-stage installations, source adapters and
hash-chain/committed-verifier endpoint assemblies are retired. No generic stage
composition theorem closes those links automatically.

## Obligations

The informal "random oracle" assumption separates into five obligations:

- **Encoding and transcript state.** Typed histories stand for the absorbed
  bytes: canonical value, occurrence and binding encodings are injective and
  prefix-free, proof bytes decode to the typed messages in order, the native
  transcript state is the absorbed history, and for adaptive statements the
  host's initial binding determines the statement. These belong to the
  construction rule and the native boundary.
- **Transcript primitive.** The suite's squeezed bytes on an absorbed history
  are a uniformly random function of that history: the chain or sponge
  idealization of the [transcript construction](#role-separation-and-transcript-constructions).
- **Provider simulation.** For a construction whose sites read several hash or
  permutation calls, the deployed interaction is simulated by one oracle on
  histories with the product answers the sites decode, with the type of
  [provider simulations](../support.md).
- **Challenge distribution.** Each site's decoder is the suite's derivation of
  the challenge from the squeezed bytes, with a [realized law](#realized-sampling-laws).
  For the native suite's field challenges, modelled as `reduce` of a uniform
  sample below `2 ^ 512`, the distance from a uniform field challenge costs at
  most `|F| / 2 ^ 512` per challenge additively (`balanced_reduce`) or a factor
  `1 + |F| / 2 ^ 512` (`dominated_reduce`).
- **Ideal-experiment reduction.** In the ideal experiment, which the obligations
  above connect to the deployed verifier, the bounds of this chapter hold.

[Support](../support.md) records which
obligations are proved and lists the controls.
