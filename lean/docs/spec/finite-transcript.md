# Finite full-prefix Fiat–Shamir experiment

`ZkcSecurity.ArkLib.FiatShamir.Transcript` reuses ArkLib's protocol tree and
knowledge interfaces for any fixed finite list of public-coin rounds. Each round
can have a different finite message type and a different finite, nonempty,
uniform challenge type. The list is fixed before the adversary runs; it is not
an adaptive round-selection, unbounded interaction or concurrent-session model.

## Queries and execution

A key contains the public input, every earlier message and delivered challenge,
and the current message. Round positions are distinguished by constructors.
Every well-typed prefix is queryable, including inconsistent prefixes, queries
made before their ancestors, and repeated keys. There is no implicit restriction
to honestly generated transcripts.

The adversary returns an input, a list of messages with the specified dependent
types, and a terminal witness. Completion queries one key per round, retaining
the actual answer in each later key. Adversary and completion share one lazy
classical random oracle, initially empty. Cached answers are reused. The budget
counts every access, including cache hits, precomputation and repeated attempts
performed by the adversary; it is not a native execution-time bound.

## Security theorem

The consumer supplies an initial knowledge predicate, a backward extractor,
prover preservation and a uniform local bad-challenge bound `error` at **every
authored prefix**, plus a terminal witness map. The local event existentially
quantifies the next knowledge witness. A bound for one fixed witness cannot
replace this premise.

`extraction_bound` proves that terminal knowledge with failure of the named
backward-extracted initial witness has probability at most

```text
(Q + rounds.length) * error
```

for an adversary with `IsTotalQueryBound adversary Q`. The proof identifies an
actually queried bad key and invokes VCVio's adaptive bad-query theorem. Earlier
challenges are explicit in the key, so its pre-challenge knowledge state is
independent of the random-oracle table. There is no salt-selection preparation
access. ArkLib supplies the knowledge definitions and extraction-failure lemma;
VCVio supplies the cached experiment and probability bound. This is a composed
proof from those results, not a premise asserting experiment correspondence.

The [two-round restoration simulation](prefix-simulation.md) remains a separate
proved route with its own cache equality and conservative `Q + 3` charge. The
direct theorem does not turn that simulation's query log into a shorter one.

## Actual computations

`Transcript.Direct.FailureTrace` connects a fixed computation and event to the
same knowledge argument for any fixed heterogeneous finite schedule. For every
answer table, an event occurrence must supply a terminal witness, failure of its
backward extraction, and all corresponding path keys in the actual query log.
`extraction_event_bound` then charges only the actual computation's total query
bound. Rejecting runs need not execute any remaining rounds.

The interface leaves terminal knowledge inside the event connection. A later
PCS composition can account separately for terminal failure in the same shared
experiment; this theorem supplies neither that PCS reduction nor independence.
The native two-round adapter in `Prefix.Direct` preserves the registered key
domain. A general native loop still needs a uniform execution/trace law and
adequate transcript interpretation; the generic theorem alone provides neither.

## Sumcheck consumer

`ArkLib.Sumcheck.FiatShamir.FiniteRounds` discharges the local knowledge premises
for quadratic Sumcheck with any finite number `n` of variables, using a degree-two
root bound. Statements and proof messages can be selected after adaptive oracle
queries. Its false-acceptance bound is `(Q + n) * 2/|F|`.

`source_accepted_iff` identifies this event with execution of the existing whole
typed `Sumcheck.Source.program n`, including every boundary guard and the final
public polynomial evaluation. `source_soundness` applies the bound to that
source execution. This completes a full transcript and then replays the source;
it does not identify the source's early-stop trace or final cache with completion,
nor prove an arbitrary native loop export denotes that program. The currently
registered constructed-program requests still use their reviewed two-round
consumer and its existing bound.

## Boundary and controls

The keys are typed values, not byte strings. Native extraction, transcript
initialization, injective serialization, raw-byte adversary routing, challenge
decoding, concrete hash/duplex security and subsequent native lowerings remain
separate. Efficient extraction and resource-bounded computational hardness do
not follow from the query-bound theorem. Probabilistic acceptance is not a
zero-knowledge or leakage theorem.

`TestsSecurity.FiniteTranscript` checks three different round alphabets, actual
completion replies, retained prior challenges, round separation, cached replies,
out-of-order queries and repeated-call accounting. Three-variable Sumcheck
controls include a real false-accepting path, rejection under a changed challenge,
and an adaptive experiment with the informative bound `12/101`. The optional
package's declaration audit checks the transitive axiom closure of these results.
`TestsSecurity.ActualTranscript` applies the actual-query interface to an
admission-guarded finite Sumcheck experiment, proves its trace law and query
budget uniformly in `n`, and checks that rejection adds no completion accesses.
This is a generic regression consumer, not a native loop correspondence.
