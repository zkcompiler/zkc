# Multi-round Fiat–Shamir security

This chapter states the security of Fiat–Shamir transforms of validators with
any number of challenges, derived from round-by-round soundness of the
interactive validator. The general theorems hold for any transcript interface
with typed query sites and an error per site; the transform
`Zkc.Construction.transform` of the [construction chapter](fiat-shamir.md) is one
instance, and the imported Sumcheck verifier is an instance of that. The general
theorems are in `ZkcSecurity.FiatShamir` (`Interface`, `Typed`, `Soundness`,
`Decoding`, `Sampling`, `Grinding`, `Roles`); the Sumcheck instance is
`ZkcSecurity.Examples.SumcheckFiatShamir`.

## Typed query sites

A validator is a process `PIR.Proc I A` over any operation signature `I`. A
**transcript interface** `Typed.Interface I E P R` states, for each operation,
how the transform treats it (`Typed.Absorption`):

- `receive event recover`: read the next proof message `m : P`, absorb the
  event `event m : E` and continue with the reply `recover (event m)`; a message
  whose event recovers no reply refuses without being consumed. The reply is a
  function of the absorbed event, which is what binds it.
- `send event value`: absorb `event` and continue with `value`.
- `query event decode`: absorb the challenge occurrence `event`, ask the
  transcript oracle at the history `preceding ++ [event]` and continue with
  `decode preceding raw` of its raw answer; a refused decoding stops with
  `exhausted`.
- `refuse`: stop.

The transcript oracle answers a history `key` with a value of its raw type
`R key`, so the raw answer may depend on the occurrence that ends the key, for
example on its method and on operands fixed before sampling. Each query site
chooses its result sort (a field or extension element, a bounded index, a bit
string, a gated pair or a block of indices) and its decoder; decoders may
refuse, as rejection samplers do. `Typed.transform` is the transform with a
challenge function in any monad.

A **certificate** `Typed.Certificate absorb accepts error` is a set `doomed` of
residual processes, with an error `error e` for every absorbed occurrence `e`,
whose members meet the local obligations `Typed.Step`:

- a doomed `done` result does not satisfy `accepts`;
- a doomed receive stays doomed for every reply, and a doomed send stays doomed;
- from a doomed query with occurrence `e`, after every absorbed prefix, the
  site's decoding of a fresh uniform raw answer yields a value that leaves the
  doomed set with probability at most `error e`; refused answers never escape.

The escape bound is stated for the decoded law of the site, so a site's error
already includes its sampling correction (see [realized laws](#realized-sampling-laws)).
`Typed.QueryBound` counts the queries on every path of a validator, and
`Typed.CostBound` charges each query the error of its occurrence.

**Per-key charges.** A charge `charge : List E → E → ENNReal` is a function of
the whole key: the absorbed history before a query and its occurrence. It can
count loop iterations that the history determines and read operands carried in
the occurrence. A **charged certificate** `Typed.ChargedCertificate absorb
accepts charge` has the local obligations `Typed.ChargedStep`, which are those
of `Typed.Step` except that a doomed query with occurrence `e`, after the
absorbed prefix `preceding`, escapes with probability at most
`charge preceding e`. A certificate with an error per occurrence is the charged
certificate of the charge that ignores the history (`Certificate.charged`,
`Step.charged`, `ChargedStep.uncharged`). `Typed.ChargedCostBound absorb charge
process history cost` bounds the charges on every path of a validator started
from the absorbed `history`; a cost bound with an error per occurrence is one
from every history (`CostBound.charged`), and a query count with every charge at
most `bound` charges at most `budget * bound` (`QueryBound.chargedCostBound`).

## The ideal experiment

The transcript oracle on all event histories is `OracleSpec.ofFn R`.
`Typed.answer key` asks it at `key`. The experiments are

```text
Typed.fixedExperiment absorb validator initial prover :=
  prover >>= fun proof => Typed.transform absorb answer validator initial proof

Typed.experiment absorb validator initial prover :=
  prover >>= fun (statement, proof) =>
    (statement, ·) <$> Typed.transform absorb answer
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
  (`Typed.keyError`), or, with a per-key charge, the charge of its last event
  after the history before it (`Typed.keyCharge`, which is `keyError` for a
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
  must determine the statements (`Typed.Determined`): if one statement's initial
  history followed by some events equals another statement's initial history
  followed by some events, the two statements are equal.
- **Event.** `Accepted accepts outcome`: the transform returns a value
  satisfying `accepts`; in the adaptive experiment, also for a false chosen
  statement. Stops never accept. The event ignores the unread proof suffix, so
  the bounds also cover verifiers that reject leftover proof data.

## The typed-site theorems

`Typed.adaptive_soundness_weighted`: if the false statements' validators are
doomed, every validator's queries charge at most `validatorCost`, the initial
histories determine the statements and the prover's queries charge at most
`proverCost`, then

```text
Pr[falseStatement result.1 ∧ Accepted accepts result.2.1
     | (simulateQ randomOracle (Typed.experiment …)).run' ∅]
  ≤ proverCost + validatorCost
```

`Typed.adaptive_soundness` is the case of errors at most `bound`, `queries`
prover queries and validators with at most `budget` queries:
`(queries + budget) * bound`. `Typed.soundness_weighted` and `Typed.soundness`
are the fixed-statement forms, and `Typed.randomized_soundness_weighted` adds
private randomness drawn before the oracle computation. Charging each key its
own error gives the sum over the asked keys; the uniform form is
`(queries + budget) * max` over the sites.

The per-key forms are `Typed.adaptive_soundness_charged`,
`Typed.soundness_charged` and `Typed.randomized_soundness_charged`: a charged
certificate, validators whose queries from their initial histories charge at
most `validatorCost` (`ChargedCostBound`) and a prover whose queries charge at
most `proverCost` with every key charged `keyCharge charge` give the same bound
`proverCost + validatorCost`. The theorems with an error per occurrence are
their instances at the charge that ignores the history, and the uniform forms
follow from those; their statements are unchanged. A per-key charge discharges
neither obligation of the weighted bound: the all-table resampling bound and the
pathwise weighted budget are proved for each certificate. With law records, the
charge of a query site is `κ · ε + λ` at its key.

The proofs apply VCVio's weighted adaptive bad-query bound
`OracleComp.prEvent_randomOracle_le_of_bad_queries_weighted` directly to the
history oracle, with no routing to library keys:

- **Bad keys.** `Typed.replay` walks a statement's validator from its initial
  history along a key's events, recovering received replies from the absorbed
  events and answering earlier queries by decoding the table. A key is bad
  (`Typed.BadKey`) when, for some statement, this reaches a doomed query whose
  occurrence is the key's last event and whose decoded answer at the key leaves
  the doomed set.
- **Resampling.** The key determines the statement and the replayed events, and
  replay reads the table only at histories no longer than the replayed prefix
  (`Typed.replay_congr`). Resampling the answer at a key therefore leaves the
  replayed residual unchanged, and the key is bad with probability at most the
  charge of the key under every background table (`Typed.badKey_resample_charged`;
  `Typed.badKey_resample` for an error per occurrence).
- **Trace.** An accepting deterministic run from a doomed validator must leave
  the doomed set at one of its own queries, whose key is in the query log and is
  bad (`Typed.escape_logged_charged`, `Typed.escape_logged`).
- **Cost.** The transform charges at most the validator's cost
  (`Typed.transform_chargedCostBound`, `Typed.transform_costBound`), so the
  whole execution charges at most `proverCost + validatorCost`.

The proofs use four properties of the transform: every received reply is
determined by the event absorbed for it; every query is answered at the history
ending with its own occurrence, which is absorbed; every sent value is absorbed;
and histories only grow. A transform that did not absorb a prover message would
break replay, and with it the theorems. For adaptive statements the initial
history must also bind the statement.

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

A law record `LawRecord Raw Value` (`ZkcSecurity.FiatShamir.Laws`) is the
proof-bearing realized law of a request class, stated on the raw answer: a
decoder `decode : Raw → Option Value`, a coefficient `factor` and a slack
`slack` in `[0, ∞]` with `Realized decode factor slack` against the uniform law
of the sort, and a refusal bound `refusal` with
`Pr[decode raw = none] ≤ refusal`, a completeness quantity. The ideal law of the
sort is its uniform law: uniform field elements, `UniformIndex(N)` for an index
below `N`, and the product law of a block, which is the uniform law of the
function type. A gated accepted-value decoder has a coefficient below one. A
site with ideal-law error `ε` escapes with probability at most
`factor · ε + slack` (`LawRecord.escape_le`).

Five constructors present a record from a checked claim about the realized
subdistribution `μ` against the ideal law `ν`:

- `LawRecord.exact`: a total decoding with `μ = ν` (`ExactLaw`); a bijection is
  exact (`exactLaw_of_bijective`), and so is any total decoding dominated with
  factor one, because the complements of its events are dominated too
  (`Dominated.exactLaw`).
- `LawRecord.exactWithRefusal`: `μ = p_success · ν`
  (`Obligations.ExactWithRefusal`), with the success probability as coefficient;
  a decoder whose every value has the same number of preimages is of this kind
  (`exactWithRefusal_of_fibers`).
- `LawRecord.dominated`: `μ ≤ κ · ν + λ` with refusal allowed. It suffices for
  soundness but says nothing about the success-conditional law: a decoder that
  returns `0` on one outcome of a fair bit and refuses on the other is dominated
  with coefficient one but not exact with refusal
  (`TestsSecurity.LawRecords.constantOnSuccess_not_exact`).
- `LawRecord.pointRatio`: `μ(x) ≤ κ · ν(x)` for every value (`PointRatio`,
  `PointRatio.realized`).
- `LawRecord.additive`: a total decoding with coefficient one and its additive
  loss as slack (`Balanced`).

`LawRecord.gated` is the accepted-value decoder of a gated site: from gate bits
and a challenge answer it refuses unless the gate passes, with coefficient and
slack the gate's passing probability times the challenge record's
(`gated_realized`) and refusal at most the gate's failure probability plus the
challenge's refusal. The sampling lemmas above instantiate the constructors:
`LawRecord.identity` and `LawRecord.modulo` (exact), `LawRecord.lowBitsRejecting`
(exact with refusal), `LawRecord.koalaBearLowBits` (point ratio
`1 + (2 ^ bits - 1) / p`, `koalaBear_lowBits_pointRatio`),
`LawRecord.bls12381Reduction` and `LawRecord.koalaBearCompound` (dominated),
`LawRecord.reduce` (additive, loss `|F| / N`) and `LawRecord.koalaBearQueryPhase`
(gated, with the factor of `koalaBear_queryPhase_realized`,
`LawRecord.koalaBearQueryPhase_factor`).

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
(`ZkcSecurity.FiatShamir.Lifting`). `Typed.ByLast Raw key` is `Raw` of the key's
last event, and `Unit` at the empty key, which no query reaches; it is uniform
when every `Raw event` is (`ByLast.sampleable`). At a key `preceding ++ [event]`
the answer reads as a value of `Raw event` (`ByLast.read`), with the same
uniform law (`prEvent_read`), and `Absorption.queryLast` is a query whose
decoder takes that value.

A **law interface** `Typed.LawInterface I E P Raw` presents a validator's
operations to the transform with every query decoded by a law record from the
raw answer of its occurrence into the operation's reply sort; its transcript
interface is `LawInterface.absorb`. A **uniform-sort certificate**
`Typed.UniformCertificate laws accepts error` is a round-by-round certificate in
which a doomed query's uniform reply of its sort leaves the doomed set with
probability at most `error operation` (`Typed.UniformStep`), the form a
protocol's own analysis produces. It lifts to a charged certificate over
`LawInterface.absorb`, with the same doomed set, whenever every query's charge
covers its record's `factor · error + slack` (`UniformCertificate.charged`), and
to a certificate with an error per occurrence under the same condition with
errors by event (`UniformCertificate.certificate`). Law-record decoders read only
the raw answer: the operands they depend on are carried in the occurrence. In
`TestsSecurity.LawRecords` a validator with an exact challenge in `Fin 5` and a
gated block of positions has uniform errors `1 / 5` and `1 / 4`; the lifted
certificate charges `1 / 5` and `1 / 2 · 1 / 4`, and the typed engine bounds its
acceptance by `(queries + 2) / 5`.

## Binding codecs

`Typed.Determined` quantifies over every statement the prover can output,
malformed ones included, so a codec that discharges it is injective and
prefix-free on the whole statement type (`ZkcSecurity.FiatShamir.Binding`). A
typed public value (`PublicValue`) is a scalar, a vector whose length is part of
the value, an index below a bound, or a count; a canonical row (`Row`) is a
statement's public values in canonical order, each labelled by its input; and
the **typed public-value binding event** (`PublicBinding`) is the application
context with a canonical row. A **binding codec** `BindingCodec Stmt E` is an
injective, prefix-free encoding of statements as initial histories, and it
discharges `Typed.Determined` (`BindingCodec.determined`). Binding a statement as
one typed public-value binding event is such a codec when the event embeds
injectively into the transcript events and the row determines the statement
(`BindingCodec.single`, `determined_single`). In `TestsSecurity.BindingCodecs`
the raw Sumcheck statement (table values, claim and round count, with no length
check) is bound by one event and determined, while binding the table entries one
event each with no count or length is not prefix-free and is not determined.

## Role separation and transcript constructions

The ideal model is a random oracle on typed transcript histories whose answer at
a gated or compound key is the whole tuple the site decodes. Deployed transcripts
realize it from a hash function or permutation:

- **Tagged hash chain.** A Merkle–Damgård chain of a compression function over
  tagged blocks, where each absorbed event, squeeze and proof-of-work step is a
  block with its own tag. It needs an injective, prefix-free encoding of
  histories into tagged blocks, and the chain idealization: the chaining value of
  every block prefix acts as a random oracle on prefixes, up to the collision
  terms of the chaining values. Several outputs read at one key with distinct
  tags are then role-separated answers of that oracle.
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
[provider simulations](#provider-simulations).

## The participant transform

The common participant actions form a transcript interface (`interface context
decode`): a receive absorbs its message occurrence with the payload and recovers
the payload's value at the expected type, a send absorbs its message occurrence,
and every query absorbs its challenge occurrence and decodes the oracle answer,
of one raw type `B`, with `decode : B → F`. Its transform is
`Zkc.Construction.transform` with the decoded oracle as challenge function
(`transform_eq`), and the experiments are the typed experiments
(`experiment_eq`, `adaptiveExperiment_eq`). The oracle `Oracle F G B` on all
typed histories `History F G` answers in `B`; `FieldOracle F G` answers field
elements directly. `decodedQuery decode` asks the oracle at the absorbed history
and decodes the answer; `historyQuery` is the undecoded case.

```text
experiment context validator initial prover :=
  prover >>= fun proof => transform context historyQuery validator initial proof

adaptiveExperiment context decode validator initial prover :=
  prover >>= fun (statement, proof) =>
    (statement, ·) <$> transform context (decodedQuery decode)
      (validator statement) (initial statement) proof
```

`RoundByRound accepts error` is a doomed set of participant processes with four
laws: a doomed `done` result does not satisfy `accepts`; a doomed receive stays
doomed for every received value; a doomed send stays doomed; and from a doomed
query, a fresh uniform challenge `$ᵗ F` leaves the doomed set with probability
at most `error`. The doomed set plays the role of the state function of
round-by-round soundness (Canetti et al., STOC 2019), with the residual
validator process as the state. Its laws are local, so they hold for any
interleaving of messages and challenges and for schedules that depend on
received values. `RoundByRound.ofStep` builds a certificate from a set whose
members each meet the local obligation `Step`, and `Step.mono` keeps the
obligations when the set grows, so certificates of several statements combine
into one. `QueryBound validator budget` states that every path of the validator
makes at most `budget` challenges. Such a certificate is a typed certificate over
the interface with the same error at every challenge occurrence, corrected by the
decoding: plus `loss` for a balanced decoding (`RoundByRound.balanced`), times
`factor` for a dominated one (`RoundByRound.dominated`).

`ZkcSecurity.FiatShamir.soundness`: if `certificate.doomed validator`,
`QueryBound validator budget` and `IsTotalQueryBound prover queries`, then

```text
Pr[Accepted accepts result.1 | (simulateQ randomOracle (experiment …)).run' ∅]
  ≤ (queries + budget) * error
```

`adaptive_soundness`: if the false statements' validators are doomed, every
validator is within `budget`, the initial histories determine the statements
(`Determined`), `decode` is balanced with `loss` and the prover is within
`queries`, then

```text
Pr[falseStatement result.1 ∧ Accepted accepts result.2.1
     | (simulateQ randomOracle (adaptiveExperiment …)).run' ∅]
  ≤ (queries + budget) * (error + loss)
```

`adaptive_soundness_dominated` is the same with a decoding dominated by
`factor`: `(queries + budget) * (factor * error)`; `adaptive_soundness_exact`
is the bijective case, `(queries + budget) * error`. These four theorems are the
typed-site theorems at the participant interface. `randomized_soundness` is the
fixed-statement bound for a distribution over provers, each within `queries` on
its support. `acceptance_le_of_image` compares a compiled verifier with the
transform for a fixed statement: if, for every proof, the compiled verifier is an
outcome image of the transform and an accepted image comes only from an accepted
outcome, the compiled verifier accepts no more often than the transform, so the
fixed-statement bound transfers to it. `acceptance_bind_done` moves a final
projection of the validator's result into the acceptance predicate: the
transform of `validator.bind (done ∘ f)` accepts with `accepts` exactly as often
as the transform of `validator` accepts with `accepts ∘ f`.
`adaptive_acceptance_bind_done` is the same equality in the adaptive experiment,
with any event on the chosen statement.

## The imported Sumcheck verifier

`importedValidator raw claim count handle` is the actual imported
`example::Interactive` verifier at role 1, with present inputs and the service
handle `handle`, projected to the common participant actions.
`importedValidator_eq` proves that for every admitted count (`count ≤ 2`) and a
raw vector decoding to the table, it is the plain process `validator`: per
round, two received field halves, the boundary check, one challenge, its
delivery and the interpolated claim; then the public-table terminal check.
Above the exported maximum it refuses (`importedValidator_excess`).

The doomed set describes each phase of the rounds (`Phase`, `residual`, `Holds`):
the current claim is false, as ArkLib's closed round relation
`MultivariateRound.closedRelation` for the table's multilinear extension
(`FalseClaim`), and the point length matches the rounds still to run. The
certificate (`certificate`) is stated for the rounds followed by any returned
`output` of the final point and claim, with the terminal law that no output of a
false claim at a complete point is accepted; the public-table decision is one
such output (`decision`, `decision_rejects`). The laws follow from:

- `falseClaim_initial`: a claim different from the table sum is false at the
  empty point (the bridge's `closed_statement`);
- `falseClaim_successor`: after a passed boundary check, a fresh uniform
  challenge makes the interpolated claim true with probability at most `1 / |F|`.
  This is ArkLib's `MultivariateRound.uniform_successor_soundness` at degree
  one, through the multilinear message and table bridge (`message_evaluate`,
  `domain_sum_message`);
- `falseClaim_terminal`: a false claim at a complete point fails the terminal
  evaluation (`closedRelation_last_iff`, `statement_evaluate`).

The Sumcheck theorems are:

- `soundness`: the plain verifier's transform accepts a false claim with
  probability at most `(queries + count) * (1 / |F|)`;
- `imported_soundness`: the same bound for the imported verifier, for every
  count, with the false claim on the raw public vector;
- `adaptive_imported_soundness`: the prover chooses a well-formed
  `PublicStatement` (a raw vector, a claim, a count and the table the vector
  decodes to at that count) after its queries; with a determining initial history
  and a balanced decoding, a false chosen claim is accepted with probability at
  most `(queries + 2) * (1 / |F| + loss)`, two being the exported maximum count.
  `DoomedAny` combines the doomed sets of all tables with the refused verifier;
- `reduced_imported_soundness`: the adaptive bound with challenges reduced
  modulo the field size from a uniform sample below `N`, with loss `|F| / N`.

The composed `example::Reduction` root returns its point and residual claim
instead of a decision. `importedReduction` is its imported verifier, equal to the
rounds for every admitted count (`count ≤ 4`, `importedReduction_eq`) and
refusing above (`importedReduction_excess`). For an external table of dimension
`remaining + count`, falsity is taken on the marginal table `sumRemaining`,
whose sum is the original sum and whose terminal relation is the residual one
(`reduction_rejects`). `reduction_soundness` bounds by
`(queries + count) * (1 / |F|)` the probability that the transform returns a
true residual claim (`residualObservation`) from a false initial claim, for every
count. The residual claim is a terminal obligation for a later opening argument,
not an acceptance decision.

## Composition with the construction rule

The original-stage export of the compiled `example::Proof` Entry is the
imported `example::Interactive` export, so the original validator of the
compiled Entry is `importedValidator`. `compiled_imported_soundness` takes the
compiled verifier as any function from proofs to oracle computations, with one
premise about it: with the transcript oracle as challenge function it is the
transform of `importedValidator` (`construction`), the equation that relates the
compiled Entry to its original program. Its conclusion is the fixed-statement
bound for the compiled verifier. `compiled_adaptive_soundness` is the adaptive
form: for every statement, the compiled verifier with the decoded oracle as
challenge function is the transform of the imported verifier from that
statement's initial history, the host binding; with a determining binding and a
balanced decoding the adaptive bound follows. `compiled_soundness` is the variant
for any original validator equal to the plain verifier (`projection`).

The equation may also relate the compiled meaning, read through a selection of
its returned values, to the transform of the original participant process read
through a matching selection of its outputs.
`compiled_participant_soundness` takes it in this form, for the imported
participant process followed by any `final` reading of its outputs, with one
further premise: an accepted reading implies the Boolean output `some true`. Its
conclusion is again the fixed-statement bound;
`compiled_adaptive_participant_soundness` is its adaptive form.

A compiled verifier that reports outcomes differently from the transform, for
example a returned rejection as the stop `reject` or acceptance as a value of
another type, may instead be an outcome image of the transform;
`acceptance_le_of_image` then carries the fixed-statement bound over when
acceptance of the image implies acceptance of the transform's outcome.

## The compiled Sumcheck proof Entry

`ZkcSecurity.Examples.CompiledSumcheckFiatShamir` composes these theorems with
the transcript-construction and
[participant projection](participant-projection.md#the-compiled-sumcheck-proof-entry)
rules. Its subject is the compiled verifier itself: `compiledVerifier challenge
raw claim count initial proof` is the ideal interpretation
(`Zkc.Construction.ideal`) of the exported validator `SumcheckProof.participant`,
under the occurrence context the check derives and with helper calls read by the
original's checked helpers, on the table values, the claim, the round count and
the initial transcript, read through the acceptance output the policy selects.

- `construction` is the vertical link: for every challenge function the
  compiled verifier is the transform of `importedValidator`. It instantiates
  `SumcheckProof.compiled_transform`, which follows from the composed check
  `checkCompiled` on the admitted Sumcheck source with no equation specific to
  the Entry, and
  `verifier_imported`, the definitional equality of the Proof Entry's original
  validator with the imported `example::Interactive` verifier. The construction
  bridge pins the bytes: the Proof Entry's fresh original export must render to
  `SumcheckSourceData`, the admitted source both readings use (the check
  `regenerated:lean/ZkcExamples/Structured/SumcheckSourceData.lean` of its
  `sumcheck` subject).
- `soundness`: for a fixed well-formed statement (the raw values decode to a
  table at the count) and initial transcript, the compiled verifier accepts a
  false claim on the raw table values with probability at most
  `(Q + count) / |F|`, against every prover with at most `Q` queries to the
  transcript oracle on all typed histories. Acceptance ignores unread proof
  messages, so the bound also covers an acceptance of the same ideal
  interpretation that requires the whole proof to be read. The
  [executable stage](executable.md#the-compiled-sumcheck-proof-verifier)
  transfers the bound to provers of proof bytes for the program the runtime
  admits.
- `adaptive_soundness`: for well-formed statements chosen after the queries,
  with decoded challenges, at most `(Q + 2) * (1 / |F| + loss)` when the initial
  transcripts `initial statement` determine the statement; `reduced_soundness`
  instantiates the decoding with reduction modulo the field size of a sample
  below `N`, `loss = |F| / N`.

The adaptive theorems take the binding as a premise. The host binds the
policy's public inputs, here the table values, the claim and the round count.
The [executable statement](executable.md#the-compiled-sumcheck-proof-verifier)
discharges the premise for a binding with one event per public input, the
table as its field entries and the round count in unary, whose events
determine the statement.

The controls (`TestsSecurity.CompiledSumcheckFiatShamir`) use the one-round
`ZMod 5` instance of the imported verifier's controls. The premises hold
together. The compiled program, evaluated in the kernel without the
construction equation, accepts the cheating proof exactly at the challenge `2`
and the honest proof for the true claim at every challenge. The query-free
cheating prover is accepted with probability exactly `1 / 5`, so the bound is
attained on the compiled Entry. Without a determining binding, a one-query
prover is accepted on a false claim with probability `4 / 5`, above the adaptive
bound `3 / 5`.

## The plain GKR verifier

`ZkcSecurity.Examples.GkrFiatShamir` bounds the transform of
`ZkcExamples.Structured.GkrVerifier.verifier`, the verifier of the
[GKR library](../../../libraries/gkr/README.md) for a statement already decoded
to tables: the claimed outputs and the inputs as tables of the width, and each
layer's add and mul wiring as a table over `(z, x, y)`. Its round-by-round
certificate composes one certificate per phase with
`ZkcSecurity.FiatShamir.Reduction`, whose sequential composition (`bind`,
`repeatN`, `union`, `receive`) keeps the error of each challenge:

- **Output point.** While the claimed outputs differ from the circuit's
  outputs, their difference is nonzero at some Boolean values of the remaining
  coordinates; a fresh challenge loses that with probability at most `1 / |F|`,
  since the extension is affine in each coordinate.
- **Layer rounds.** A false claim `m ≠ W~_i(r)` about a layer is a false claim
  about the Boolean sum of the layer's gate polynomial
  (`ZkcSecurity.ArkLib.Gkr.gatePolynomial`, `Zkc.Protocols.Gkr.extension_layer`),
  which has degree at most two in each variable. Across both `Rounds`
  applications each round keeps the claim false except with probability
  `2 / |F|` (`falseClaim_successor`, ArkLib's
  `MultivariateRound.uniform_successor_soundness` at degree two).
- **Line.** After the wiring check passes on a false claim at the complete
  point `(b, c)`, the received coefficients describe a polynomial other than
  the restriction `q(t) = W~_{i+1}((1 - t) b + t c)`, which has degree at most
  the width; the line challenge makes the next layer's claim true with
  probability at most `width / |F|` (`agreements_card_le`, Schwartz–Zippel for
  the line restriction).
- **Inputs.** A false claim about the input layer fails the input check.

With error `max 2 width / |F|` per challenge and `width + layers (2 width + 1)`
challenges, `soundness` bounds the probability that claimed outputs other than
the circuit's outputs on the inputs are accepted by
`(Q + width + layers (2 width + 1)) max 2 width / |F|`, for a fixed statement and
initial transcript, in the random-oracle experiment of the general theorems.

## The compiled GKR proof Entry

`ZkcSecurity.Examples.CompiledGkrFiatShamir` states the bound for the compiled
`example::Proof` verifier of the GKR example. `compiledVerifier challenge inputs
outputs add mul layers selector width initial proof` is the ideal interpretation
of the exported validator `GkrProof.participant`, as for Sumcheck, on the raw
public statement: the input values, the claimed outputs, the stacked add and
mul tables, the number of layers, the number of selector coordinates and the
width.

- `construction`: on a well-formed statement (`WellFormed`), for every
  challenge function, the compiled verifier is the transform of the plain GKR
  verifier at the decoded tables. It composes two equations.
  `GkrProof.spec_transform` follows from the transcript-construction rule
  alone: the compiled meaning is the transform of the interactive reading
  (`spec`) of the exported instructions. `GkrProof.reading` proves that reading
  equal to the plain verifier. Each loop of the export reads as repeated steps
  of the plain verifier (`Zkc.Construction.iterate_range_repeatN`), because the
  reading never inspects transcript histories (`specK_similar`); helper calls
  are read with the admitted unit's own helper equations
  (`ZkcExamples.Structured.GkrSourceLaws`). The composed check also accepts the
  export, so the same meaning is the transform of the original GKR validator
  (`GkrProof.compiled_transform`).
- `soundness`: for a fixed well-formed statement and initial transcript, the
  compiled verifier accepts claimed outputs other than the circuit's outputs on
  its inputs with probability at most
  `(Q + width + layers (2 width + 1)) max 2 width / |F|`.

A statement is well-formed when the input values and claimed outputs decode to
tables of the width, the stacked tables have `2 ^ selector` blocks of
`2 ^ (3 width)` values, every layer has a block and its add and mul blocks decode
to that layer's wiring, and the width and the number of layers are at most the
Entry's maxima, four each. Acceptance ignores unread proof messages; no
adaptive statement choice and no executable meaning of this Entry is covered.

## Construction obligations

The [construction obligations](../../../docs/spec/ir/construction-obligations.md)
are the shared contract: query identities, construction classes, realized laws,
observation classes and certified openings, blocks and gates, cryptographic
effects, binding, provider and explicit-input obligations, equivalence notions
and the [model and scope of claims](../../../docs/spec/ir/construction-obligations.md#model-and-scope-of-claims).
The theorems of this chapter are stated in that classical random-oracle model.
This section gives the formal readings of the obligations, the type of provider
simulations and the joint experiment of a committed opening.

### Formal readings

`ZkcSecurity.FiatShamir.Obligations` reads each obligation over abstract
carriers: a context `C` of the data present at one point of an execution and a
projection `scope : C → K` that keeps its admitted part.

- `Determines scope value`: two contexts with the same admitted part have the
  same value. Its instances are `Reconstructible` (an omitted value is a function
  of the absorbed history and earlier answers), `FixedAtReceivePoint` (an
  opening's root, positions, dimensions and interpretation are functions of the
  admissible sources), `CoveredByInput` (an explicit-input challenge's input
  determines each value its check reads) and `SharesEqualInputs` (equal declared
  inputs issue one primitive query). `not_determines` refutes it from two
  contexts with equal admitted parts and different values.
- `Omission` records an omitted producer value: the absorbed history at its
  point, the value, whether a selected request follows, and whether it is a
  certified opening. `Omission.Classified` holds when it is reconstructible, a
  certified opening, or terminal.
- `CausalReencoding earlier reencode`: a re-encoding of keys that may read the
  oracle table computes each key from answers at strictly earlier keys only.
  `PreservesQueryEquality`: under every table it is injective. These are two of
  the four causal replay conditions; freshness across the joint cache and the
  query-cost relation are properties of the two experiments.
- `DistinctPrimitiveInputs reachable input`: distinct reachable transcript
  queries reach distinct primitive inputs. `PrefixFreeEncoding encode`: no
  encoding followed by more data is another encoding; it implies injectivity.
- `ExactWithRefusal decode`: every event of the successful decoded value has
  the success probability times its ideal probability; such a decoding is
  realized with factor one and no slack (`ExactWithRefusal.realized`).
- `HashLaws hashing handler`: the outcome of every selected call, a reply or a
  stop, is a function of its operation alone, whatever the handler's state:
  equal inputs receive equal answers and no stop depends on the number or order
  of earlier calls, while a stop the input determines is allowed.
  `TotalConsistentHandler` is the stronger specialization that never stops
  (`TotalConsistentHandler.hashLaws`).
- `ConstructionCorrect`: a constructed meaning equals the transform of the
  original for every challenge function.
- `AuthenticatedOperand fixed operand checked admissible`: the statement inputs
  and authenticated configuration determine the operand, or every context the
  validator lets through has an admissible value. `ProductionRange` requires
  every admitted value to support the claim. `AuthenticatedConfiguration`
  requires the configuration to be the same in every context.
- `GateSite` records a gate's primitive input, the state before it, the
  witness, the events absorbed between the gate step and the request, and the
  input of the gated value. `Placement` (no event absorbed in between),
  `ReadsState` (the gate's input determines the state) and `AbsorbsWitness` (the
  gated value's input determines the witness) are the admission conditions.
  `GateDetermines` (the gate's input determines the gated value's input) is a
  weaker, necessary dependency condition of placement; a fixed constant absorbed
  in between meets it.

Exact statement determination is `Typed.Determined`, a realized law is
`Realized` and the per-prefix local obligation is `Typed.Step`. The
[counterexamples](../support.md#construction-obligation-counterexamples) refute
properties and violate these predicates.

### Provider simulations

`ZkcSecurity.FiatShamir.Provider` fixes the type of a provider simulation for
one property, one provider and one class of bounded executions.

- `Budget Family := Family → ℕ` is the adversary's primitive calls per family.
  `FamilyQueryBound family computation budget` bounds the calls of each family
  on every path (VCVio's `IsQueryBound` with one counter per family), and
  implies the total bound of the summed budget
  (`FamilyQueryBound.isTotalQueryBound`).
- `Expansion` gives a provider's calls at initialization, per absorbed event
  kind and per request kind, and `ExecutionCounts` the occurrence counts of one
  run at an execution bound's maxima. `Expansion.total` is
  `initialization + Σ_e n_e · v_e + Σ_r n_r · v_r`; initialization is always
  included (`Expansion.initialization_le_total`).
- `QueryCost Family ExecBound` has `cost : Budget Family → ℕ` with `monotone`,
  `expansion : ExecBound → ℕ` and `loss : Budget Family → ℕ → ENNReal`.
  `QueryCost.ofCounts` builds the expansion from an `Expansion` and the counts of
  each execution bound.
- `Simulator primitive R Tape` answers the primitive families from the history
  oracle `OracleSpec.ofFn R`, a state started from a private tape (`start`), and
  the attempt each call belongs to in a state (`attempt`), with recorded ideal
  answers (`recorded`, `record`), the reply `shared` read from an attempt's
  answer, the private reply `respond` with no TranscriptQuery, and the calls
  declared to make up one concrete attempt (`together`). Its laws: no answer is
  recorded at the start (`recorded_start`); recording an answer sets exactly
  that key (`recorded_record`, `recorded_record_of_ne`) and a private reply
  keeps every recorded answer (`recorded_respond`); recording and private
  replies keep every call assigned to an attempt assigned to it
  (`attempt_record`, `attempt_respond`); and declared constituents belong to one
  attempt in every state (`attempt_together`). `handle` is the simulator as a
  stateful oracle implementation: a call of an attempt with no recorded answer
  asks the history oracle at its key and records the answer (`handle_fresh`), a
  call of an attempt with a recorded answer reuses it (`handle_recorded`,
  `attempt_answer`), and a call outside every attempt is answered privately
  (`handle_private`). Recorded answers and assignments persist through every
  call (`recorded_persists`, `attempt_persists`), and each call makes at most
  one TranscriptQuery, none outside an attempt (`handle_queryBound`).
- `Simulator.Runs tape trace state` is the path relation: `trace` lists the
  calls of a path from `start tape` as `Answered` entries, each with the attempt
  the call belonged to when it was made and its reply, and `state` is the state
  after them. `Runs.invariant` proves, by induction on runs, that assignments
  persist, that an answer is recorded exactly for the attempts of earlier
  calls, that every recorded answer is the one every call of its attempt was
  answered from, and that a call made after a call of the same concrete attempt
  (`Constituents`: the same call, or a declared constituent in either order)
  belongs to that call's attempt. Hence the first call of an attempt on a run,
  whichever call of the attempt it is, makes exactly the attempt's
  TranscriptQuery (`Runs.first_call`); a later call reuses the answer earlier
  calls were answered from (`Runs.later_call`); any two calls of one attempt,
  in either order with any calls between them, are answered from one ideal
  answer (`Runs.shared_answer`, `Runs.constituent_attempt`,
  `Runs.constituents_share`); and every path of the translated program is a run
  (`translate_runs`). The laws constrain assigned calls: a call answered
  privately may later join an attempt, and the simulation's loss accounts for
  the difference from the concrete primitive. `TestsSecurity.ProviderSimulation`
  instantiates the laws with a split-hash simulator and shows that a preloaded
  start and a counter assignment violate them.
- `Simulator.translate adversary tape` runs the adversary against `handle`;
  with a family bound it makes at most the budget of the families that carry
  attempts (`chargedBudget`) on every path (`translate_queryBound`).
- `Simulation primitive family R concreteFailure idealFailure` carries a tape
  type per budget with its uniform sampler, the simulator per budget, the
  families that carry attempts (`charged`, with `carries`), a `QueryCost` whose
  cost covers their budget (`covers`), and the inequality
  `concreteFailure A b ≤ idealFailure (translate q A) b + loss q (expansion b)` for
  every adversary `A` within `q`, where `translate q A` draws the tape and runs the
  translated program, a mixture of provers. Every program in the mixture's
  support makes at most `cost q` TranscriptQueries (`Simulation.transport`),
  hence the typed engine's weighted budget (`Simulation.weightedBudget`). An
  ideal bound for mixtures bounded on their support transfers with the loss
  added (`Simulation.concrete_le`); for fixed statements the typed engine gives
  such a bound, `(queries + budget) · bound`
  (`randomized_soundness_of_queryBound`, from `Typed.randomized_soundness_weighted`).

**Hash-chain suites.** `ZkcSecurity.HashChain` instantiates this type for the
[native hash-chain suites](../../../docs/spec/ir/construction.md#native-hash-chain-suites),
with the byte hash read as a random oracle whose digests `S` are the states
(`2^256` of them for the installed suites). `Model` classifies primitive inputs
by role (binding the first event, absorbing an event at a state, counter block
`k` of a request at a state, every other input) and runs the validator of any
typed transcript interface with the chain: a query occurrence is answered by
`width` counter blocks at the current state and is then absorbed. The bad event
is read on the joint primitive-query trace of the adversary and the verifier, in
call order: a fresh call that generates a state (a binding, or an absorption at
a reached state) returns a digest that an earlier call generated or read as a
state, which is a collision or a prediction. The probability of any event of
the concrete experiment exceeds its probability in the experiment where a
lazily sampling simulator over the history oracle answers the adversary by at
most the probability of the bad event (`concrete_le`, through an
identical-until-bad coupling of simulations with different states,
`ZkcSecurity.VCVio.UntilBad`), and the bad event has probability at most
`(q + V)² / |S|` for `q` adversary calls and `V` verifier calls, initialization
included (`concrete_le_simulated`).

`chainSimulator` assigns counter block `k < width` of a request with occurrence
`e`, at a state reached by the recorded history `h`, to the attempt `h ++ [e]`,
and answers every other call from its private tape of `q` digests. A history is
recorded when its state is first reached and is never replaced, so assignments
persist. A request answered privately joins an attempt when a later answer
reaches its state, as the
[shared contract](../../../docs/spec/ir/construction-obligations.md#provider-simulations-and-their-query-cost)
allows; that divergence from the concrete hash is the prediction case of the bad
event. Deferred sampling (`ZkcSecurity.VCVio.Deferral`) shows that the lazily
sampling simulation has the law of the translation through `chainSimulator`
(`simulatedExperiment_eq_translated`), and `simulation` is the `Simulation`
instance with one family, cost `q`, the verifier's calls as expansion and loss
`(q + V)² / |S|`. Because initial histories determine the statements, it
composes with `Typed.adaptive_soundness` rather than the fixed-statement bound
above: with a certificate whose errors are at most `bound`, the concrete
experiment accepts a false statement with probability at most
`(q + queries) · bound + (q + V)² / |S|` (`concrete_soundness`; with pathwise
charges, `concrete_soundness_weighted`). `Encoding` proves the byte framing
injective and prefix-free and the three role tags pairwise non-prefix, and
`byte_soundness` transfers the bound to a hash on bytes, given injective state
encodings of one length, injective event encodings and `width ≤ 2^64`. The
theorems assume `0 < width` and nonempty initial histories; every request has
the same number of blocks.

### The committed-opening experiment

`ZkcSecurity.Examples.CommittedOpening` states the joint security experiment of
a protocol with commitment metadata, transcript binding, one challenge and one
authenticated opening; its bound is a proposition, proved for a total
straight-line extractor in
[verifiers with committed tables](#verifiers-with-committed-tables).

- **Protocol.** The authenticated `Configuration` fixes the scheme identity, the
  depth `k` of a binary Merkle tree and the row width. The binding event absorbs
  the context and the configuration; the producer sends a root, which is
  absorbed; the validator requests one index below `2 ^ k` at the key
  `verifierKey` (the binding, the root and the request); the producer sends the
  opening, absorbed or omitted; the validator authenticates it through hash
  calls at the configured width and depth (`authenticate`) and accepts exactly
  when the scheme accepts the row (`verifier`).
- **Readings.** `interpret` reads the process under an oracle for the joint
  namespace `Query` (transcript keys and hash calls) in any monad. The concrete
  reading accepts the honest proof exactly when its row is accepted, for every
  challenge and hash function (`concrete_honest`), and absorbing or omitting the
  terminal opening does not change any outcome (`concrete_absorption`). The
  random-oracle reading evaluated against a total table is the concrete reading
  (`evalWithAnswerFn_interpret`), so the honest experiment for a table of
  accepted rows accepts with probability one (`oracle_honest`). In the ideal
  reading hashing builds the tree of rows (`Carrier`, `idealHash`): an
  authenticated row is the committed row at its index (`ideal_authenticated`).
- **Experiment.** `experiment` runs any prover with access to every family,
  then the validator, in one oracle; `loggedRun` keeps the joint record of all
  calls in order. `Budgets` bounds the transcript and Merkle calls separately.
- **Checkpoints.** `beforeFirst key record` is the record before the first query
  of `key`, which is its first fresh query because the experiment starts from an
  empty cache, and `frozen extract c key record` the extraction for the
  configuration `c` and the key from it: `T*[c, K]`. Once the key is queried,
  later calls do not move it (`frozen_append`); in every deterministic run it does
  not change when the answer at the key is resampled (`frozen_update`); one root
  under two configurations gives two keys (`verifierKey_configuration`).
  `FrozenAt key extract` states that an extraction reads only the record before
  the key's first query.
- **Event and bound.** `Far` holds of no extracted table, or of a table with at
  least `δ · 2 ^ k` rejected rows. `AcceptsFar` is acceptance with the frozen
  extraction at the validator's key far. `IntendedBound` is the proposition
  `Pr[AcceptsFar] ≤ (q_T + 1) · κ · (1 - δ) + ε_ext + ε_ns` for every prover within
  the budgets: the history-oracle term, the extraction and drift term over at
  most `q_T + 1` checkpoints, and the namespace term. The extractor must be
  total: one that returns no table when a row is missing makes the proposition
  false at `δ = 1` for small `ε_ext + ε_ns`, since a prover that builds one half
  of the tree from accepted rows is accepted with probability one half while
  `Far` holds of the missing table.

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
  (`MerkleTrees.scheme`), and Merkle trees with hashed leaves through a leaf
  layer (`LeafHashing.scheme`).
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
- **Proof.** One application of VCVio's weighted bad-query bound to the joint
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
  [the committed-opening experiment](#the-committed-opening-experiment) for a
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
  [provider simulations](#provider-simulations).
- **Challenge distribution.** Each site's decoder is the suite's derivation of
  the challenge from the squeezed bytes, with a [realized law](#realized-sampling-laws).
  For the native suite's field challenges, modelled as `reduce` of a uniform
  sample below `2 ^ 512`, the distance from a uniform field challenge costs at
  most `|F| / 2 ^ 512` per challenge additively (`balanced_reduce`) or a factor
  `1 + |F| / 2 ^ 512` (`dominated_reduce`).
- **Ideal-experiment reduction.** In the ideal experiment, which the obligations
  above connect to the deployed verifier, the bounds of this chapter hold.

[Support](../support.md#fiatshamir-security-validation) records which
obligations are proved and lists the controls.
