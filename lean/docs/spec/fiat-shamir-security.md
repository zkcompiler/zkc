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
  (`Typed.keyError`); a key that ends with no query occurrence of the validator
  can be charged zero. `WorstCaseCostBound prover ⟨keyError error⟩ proverCost`
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
  error of its last event under every background table (`Typed.badKey_resample`).
- **Trace.** An accepting deterministic run from a doomed validator must leave
  the doomed set at one of its own queries, whose key is in the query log and is
  bad (`Typed.escape_logged`).
- **Cost.** The transform charges at most the validator's cost
  (`Typed.transform_costBound`), so the whole execution charges at most
  `proverCost + validatorCost`.

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
  largest multiple of `2 ^ bits` and refusing above it (`lowBitsRejecting`) has
  factor one on its successful values (`lowBitsRejecting_realized`); it refuses
  with probability `(p mod 2 ^ bits) / p` (`prEvent_lowBitsRejecting_refuses`),
  `1 / p` for KoalaBear at 1 to 24 bits (`koalaBear_lowBitsRejecting_refuses`).
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
law of the block, `(1 - δ) ^ s` for a query phase over a word `δ`-far from the
code, times the block's factor. Positions masked from `s` uniform KoalaBear
elements have factor `(1 + (2 ^ bits - 1) / p) ^ s`
(`koalaBear_compound_dominated`). A query phase gated by a proof-of-work
combines both (`koalaBear_queryPhase_escape_le`, `koalaBear_queryPhase_realized`).
With a 16-bit proof-of-work and 100 positions of 21 bits, the phase escapes with
probability at most `32513 / p` times `(1 + 2097151 / p) ^ 100` times the block's
uniform-law error (`koalaBear_benchmark_queryPhase_escape_le`); the block factor
is below `1.104` (`koalaBear_benchmark_block_factor_le`), less than `0.143` bits.

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
does not discharge it.

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
  histories with the product answers the sites decode.
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
