# Multi-round Fiat–Shamir security

This chapter states the security of the Fiat–Shamir transform
`Zkc.Construction.transform` of the [construction chapter](fiat-shamir.md) for
validators with any number of challenges, derived from round-by-round soundness
of the interactive validator, and its instance for the imported Sumcheck
verifier. The general theorems are in `ZkcSecurity.FiatShamir`
(`Replay`, `Soundness`, `Decoding`); the Sumcheck instance is
`ZkcSecurity.Examples.SumcheckFiatShamir`.

## The ideal experiment

The transcript oracle `Oracle F G B` answers every typed history
`History F G` with a value of `B`; `FieldOracle F G` is the oracle answering field
elements directly. `decodedQuery decode` is the challenge function that asks the
oracle at the absorbed history and decodes the answer to a field challenge;
`historyQuery` is the undecoded case.

```text
experiment context validator initial prover :=
  prover >>= fun proof => transform context historyQuery validator initial proof

adaptiveExperiment context decode validator initial prover :=
  prover >>= fun (statement, proof) =>
    (statement, ·) <$> transform context (decodedQuery decode)
      (validator statement) (initial statement) proof
```

Both run under VCVio's lazily sampled `randomOracle`, from an empty cache: a
history asked for the first time receives a fresh uniform answer, and a repeated
history its recorded answer. The prover and the transform share the one oracle.

The adversary interface is:

- **Prover.** Any oracle computation on the transcript oracle: an adaptive
  computation with arbitrary internal state that may ask any typed history,
  including histories no honest execution produces, in any order and
  repeatedly.
- **Query accounting.** `IsTotalQueryBound prover queries` bounds the prover's
  queries on every path, counting repeated and cached ones. The transform's own
  challenges are charged on top of these, also when they are cache hits.
- **Auxiliary effects.** None inside the oracle computation. For a fixed
  statement, private randomness sampled before it is covered by
  `randomized_soundness`: a `ProbComp` distribution over provers, each bounded on
  its support.
- **Statement.** In `experiment` the statement is fixed: the validator (which
  closes over the statement) and the initial history are chosen before the
  experiment. In `adaptiveExperiment` the prover chooses the statement after its
  queries, and the initial histories must determine the statements
  (`Determined`): if one statement's initial history followed by some events
  equals another statement's initial history followed by some events, the two
  statements are equal.
- **Event.** `Accepted accepts outcome`: the transform returns a value
  satisfying `accepts`; in the adaptive experiment, also for a false chosen
  statement. Stops never accept. The event ignores the unread proof suffix, so
  the bounds also cover verifiers that reject leftover proof data.

## Round-by-round soundness

A validator is a process over the common participant actions whose receives
read prover messages, whose queries are the challenges and whose sends deliver
values to the prover. `RoundByRound accepts error` is a set `doomed` of such
processes with four laws:

- a doomed `done` result does not satisfy `accepts`;
- a doomed receive stays doomed for every received value;
- a doomed send stays doomed;
- from a doomed query, a fresh uniform challenge `$ᵗ F` leaves the doomed set
  with probability at most `error`.

The doomed set plays the role of the state function of round-by-round soundness
(Canetti et al., STOC 2019), with the residual validator process as the state.
Its laws are local, so they hold for any interleaving of messages and
challenges and for schedules that depend on received values. `RoundByRound.ofStep`
builds a certificate from a set whose members each meet the local obligation
`Step`, and `Step.mono` keeps the obligations when the set grows, so
certificates of several statements combine into one. `QueryBound validator budget`
states that every path of the validator makes at most `budget` challenges.

## Decoded challenges

`Balanced decode loss` states that every event of a decoded uniform answer is at
most `loss` likelier than the same event of a uniform field challenge. The
identity decoding is balanced with loss zero (`balanced_id`).
`balanced_of_fibers` gives loss `|F| / |B|` whenever no field element has more
than `|B| / |F| + 1` preimages. `reduce numbering N` reduces a uniform sample
below `N` modulo the field size and reads the residue through a numbering of the
field elements; `balanced_reduce` gives it loss `|F| / N`. A suite that squeezes
`k` bytes and reduces their integer is this decoding with `N = 2 ^ (8k)`.

## The general theorems

`ZkcSecurity.FiatShamir.soundness`: if `certificate.doomed validator`,
`QueryBound validator budget` and `IsTotalQueryBound prover queries`, then

```text
Pr[Accepted accepts result.1 | (simulateQ randomOracle (experiment …)).run' ∅]
  ≤ (queries + budget) * error
```

`adaptive_soundness`: if the false statements' validators are doomed, every
validator is within `budget`, the initial histories determine the statements,
`decode` is balanced with `loss` and the prover is within `queries`, then

```text
Pr[falseStatement result.1 ∧ Accepted accepts result.2.1
     | (simulateQ randomOracle (adaptiveExperiment …)).run' ∅]
  ≤ (queries + budget) * (error + loss)
```

`randomized_soundness` is the fixed-statement bound for a distribution over
provers, each within `queries` on its support. `acceptance_le_of_image` compares
a compiled verifier with the transform for a fixed statement: if, for every
proof, the compiled verifier is an outcome image of the transform and an
accepted image comes only from an accepted outcome, the compiled verifier
accepts no more often than the transform, so the fixed-statement bound transfers
to it. `acceptance_bind_done` moves a final projection of the validator's result
into the acceptance predicate: the transform of `validator.bind (done ∘ f)`
accepts with `accepts` exactly as often as the transform of `validator` accepts
with `accepts ∘ f`. `adaptive_acceptance_bind_done` is the same equality in the
adaptive experiment, with any event on the chosen statement.

The proofs apply VCVio's adaptive bad-query bound
`OracleComp.prEvent_randomOracle_le_of_bad_queries` directly to the history
oracle, with no routing to library keys:

- **Bad keys.** `replay` walks a statement's validator from its initial history
  along a key's events, decoding received values from the absorbed message
  events and answering earlier challenges from the decoded oracle table. A key
  is bad (`BadKey`) when, for some statement, this reaches a doomed challenge
  whose occurrence is the key's last event and whose decoded answer at the key
  leaves the doomed set.
- **Resampling.** The key determines the statement and the replayed events, and
  replay reads the table only at histories no longer than the replayed prefix
  (`replay_congr`). Resampling the answer at a key therefore leaves the replayed
  residual unchanged, and the key is bad with probability at most
  `error + loss` under every background table (`badKey_resample`).
- **Trace.** An accepting deterministic run from a doomed validator must leave
  the doomed set at one of its own challenges, whose key is in the query log and
  is bad (`escape_logged`).
- **Budget.** The transform asks at most `budget` keys (`transform_queryBound`),
  so the whole execution asks at most `queries + budget`.

The proofs use four properties of `transform`: every received message is
absorbed as an event from which the received value is decoded; every challenge
is the oracle at the history ending with its own occurrence; every sent value is
absorbed; and histories only grow. A transform that did not absorb a prover
message would break replay, and with it the theorems. For adaptive statements
the initial history must also bind the statement.

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

## Obligations

The informal "random oracle" assumption separates into four obligations:

- **Encoding and transcript state.** Typed histories stand for the absorbed
  bytes: canonical value, occurrence and binding encodings are injective, proof
  bytes decode to the typed messages in order, the native transcript state is
  the absorbed history, and for adaptive statements the host's initial binding
  determines the statement. These belong to the construction rule and the
  native boundary.
- **Transcript primitive.** The suite's squeezed bytes on an absorbed history
  are a uniformly random function of that history. This is an assumption about
  the duplex construction.
- **Challenge distribution.** The field challenge is the suite's reduction of
  the squeezed bytes. Modelled as `reduce` of a uniform sample below `2 ^ 512`,
  its distance from a uniform field challenge costs at most `|F| / 2 ^ 512` per
  challenge (`balanced_reduce`).
- **Ideal-experiment reduction.** In the ideal experiment, which the three
  obligations above connect to the deployed verifier, the bounds of this chapter
  hold.

[Support](../support.md#fiatshamir-security-validation) records which
obligations are proved and lists the controls.
