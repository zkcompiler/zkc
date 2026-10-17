# Multi-round Fiat–Shamir security

This chapter states the security of the Fiat–Shamir transform
`Zkc.Construction.transform` of the [construction chapter](fiat-shamir.md) for
validators with any number of challenges, derived from round-by-round soundness
of the interactive validator, and its instance for the imported Sumcheck
verifier. The general theorem is in `ZkcSecurity.FiatShamir`
(`Replay`, `Soundness`); the Sumcheck instance is
`ZkcSecurity.Examples.SumcheckFiatShamir`.

## The ideal experiment

The transcript oracle `Spec F G` answers every typed history
`History F G` with a field element. `historyQuery` is the challenge function
that asks this oracle at the absorbed history.

```text
experiment context validator initial prover :=
  prover >>= fun proof => transform context historyQuery validator initial proof
```

The experiment runs under VCVio's lazily sampled `randomOracle`, from an empty
cache: a history asked for the first time receives a fresh uniform answer, and a
repeated history its recorded answer. The prover and the transform share the
one oracle.

The adversary interface is:

- **Prover.** Any `OracleComp (Spec F G) (Proof F G)`: an adaptive computation
  with arbitrary internal state that may ask any typed history, including
  histories no honest execution produces, in any order and repeatedly.
- **Query accounting.** `IsTotalQueryBound prover queries` bounds the prover's
  queries on every path, counting repeated and cached ones. The transform's own
  challenges are charged on top of these, also when they are cache hits.
- **Auxiliary effects.** None inside the oracle computation. Private
  randomness sampled before it is covered by `randomized_soundness`: a
  `ProbComp` distribution over provers, each bounded on its support.
- **Statement.** Fixed: the validator (which closes over the statement) and the
  initial history are chosen before the experiment.
- **Event.** `Accepted accepts outcome`: the transform returns a value
  satisfying `accepts`. Stops never accept. The unread proof suffix is not
  constrained, so the bound also covers verifiers that require the whole proof
  to be read.

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
`Step`. `QueryBound validator budget` states that every path of the validator
makes at most `budget` challenges.

## The general theorem

`ZkcSecurity.FiatShamir.soundness`: if `certificate.doomed validator`,
`QueryBound validator budget` and `IsTotalQueryBound prover queries`, then

```text
Pr[Accepted accepts result.1 | (simulateQ randomOracle (experiment …)).run' ∅]
  ≤ (queries + budget) * error
```

The proof applies VCVio's adaptive bad-query bound
`OracleComp.prEvent_randomOracle_le_of_bad_queries` directly to the history
oracle, with no routing to library keys:

- **Bad keys.** `replay` walks the validator from the initial history along a
  key's events, decoding received values from the absorbed message events and
  answering earlier challenges from the oracle table. A key is bad (`BadKey`)
  when this reaches a doomed challenge whose occurrence is the key's last event
  and whose answer at the key leaves the doomed set.
- **Resampling.** Replay is a function of the key and reads the table only at
  histories no longer than the replayed prefix (`replay_congr`). Resampling the
  answer at a key therefore leaves the replayed residual unchanged, and the key
  is bad with probability at most `error` under every background table
  (`badKey_resample`).
- **Trace.** An accepting deterministic run from a doomed validator must leave
  the doomed set at one of its own challenges, whose key is in the query log and
  is bad (`escape_logged`).
- **Budget.** The transform asks at most `budget` keys (`transform_queryBound`),
  so the whole execution asks at most `queries + budget`.

The proof uses four properties of `transform`: every received message is
absorbed as an event from which the received value is decoded; every challenge
is the oracle at the history ending with its own occurrence; every sent value is
absorbed; and histories only grow. A transform that did not absorb a prover
message would break replay, and with it the theorem.

## The imported Sumcheck verifier

`importedValidator raw claim count handle` is the actual imported
`example::Interactive` verifier at role 1, with present inputs and the service
handle `handle`, projected to the common participant actions.
`importedValidator_eq` proves that for every admitted count (`count ≤ 2`) and a
raw vector decoding to the table, it is the plain process `validator`: per
round, two received field halves, the boundary check, one challenge, its
delivery and the interpolated claim; then the public-table terminal check.
Above the exported maximum it refuses (`importedValidator_excess`).

The doomed set describes each phase of the plain process (`Phase`, `residual`,
`Holds`): the current claim is false, as ArkLib's closed round relation
`MultivariateRound.closedRelation` for the table's multilinear extension
(`FalseClaim`), and the point length matches the rounds still to run. The laws
follow from:

- `falseClaim_initial`: a claim different from the table sum is false at the
  empty point (the bridge's `closed_statement`);
- `falseClaim_successor`: after a passed boundary check, a fresh uniform
  challenge makes the interpolated claim true with probability at most `1 / |F|`.
  This is ArkLib's `MultivariateRound.uniform_successor_soundness` at degree
  one, through the multilinear message and table bridge (`message_evaluate`,
  `domain_sum_message`);
- `falseClaim_terminal`: a false claim at a complete point fails the terminal
  evaluation (`closedRelation_last_iff`, `statement_evaluate`).

`soundness` bounds the plain verifier's transform for a false claim by
`(queries + count) * (1 / |F|)`; `imported_soundness` states the same bound for
the imported verifier, for every count, with the false claim on the raw public
vector.

## Composition with the construction rule

`compiled_soundness` takes the compiled verifier as any function from proofs to
oracle computations, with two premises: the compiled verifier with the
transcript oracle as challenge function is the transform of an original
validator (`construction`), and that validator is the plain Sumcheck verifier
(`projection`). Its conclusion is the same bound for the compiled verifier.
The premises are the vertical links a construction rule and a projection rule
supply for the compiled `example::Proof` Entry.

## Obligations

The informal "random oracle" assumption is separated into four obligations:

- **Encoding and transcript state.** Typed histories stand for the absorbed
  bytes: canonical value, occurrence and binding encodings are injective, proof
  bytes decode to the typed messages in order, and the native transcript state
  is the absorbed history. These belong to the construction rule and the
  native boundary.
- **Transcript primitive.** The suite's challenge on an absorbed history is a
  uniformly random function of that history. This is a named assumption about
  the duplex construction and is not proved.
- **Challenge distribution.** Each fresh challenge is an exactly uniform field
  element. The suite reduces squeezed bytes to a field element, whose
  distribution is close to, not exactly, uniform; the difference is a named
  assumption here.
- **Ideal-experiment reduction.** Given the three above, the bound of this
  chapter is proved.

## Controls

`TestsSecurity.SumcheckFiatShamir` uses `ZMod 5`, one round and the raw vector
`[2, 1]`, whose extension is `2 - r` and whose sum is `3`. All premises of
`imported_soundness` hold together for the false claim `0`, giving the bound
`1 / 5`. The cheating proof `(0, 0)` passes the boundary check and is accepted
exactly at the challenge `2`, so the bounded event is not empty. For the true
claim `3` the honest proof is accepted at every challenge, so the false-claim
premise cannot be dropped.
