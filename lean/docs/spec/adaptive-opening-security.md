# Adaptive committed-table application security

This independent formal model is owned by
[`Commitment.Application`](../../security/ZkcSecurity/Transformations/Commitment/Application.lean)
and [`Commitment.AdaptiveOpening`](../../security/ZkcSecurity/Transformations/Commitment/AdaptiveOpening.lean).
It specializes the existing committed-opening bridge and hashed-leaf Merkle
extractor. It does not define a second commitment or execution framework.

The application samples a uniform start in `Fin (2 ^ depth)`, authenticates the
row at that position under statement root `root` and handle `0`, and repeatedly
authenticates the position `next row` selected by the previous reply. Its final
row is tested by `accepts`. `walk additional` performs `additional + 1` reads;
the application theorem `AdaptiveOpening.soundness` uses `additional + 2` reads.
The function `next` always returns a position in the same finite domain.

## Requested table and error

The requested table is `pinnedRows`: the existing Merkle extractor applied to
the hash entries strictly before the first query by either party of
`startKey = ([Absorbed.root () root], Event.index)`. A prover may query this key before
verification. The checkpoint is that earlier query, even if the verifier later
receives its answer from the cache. Every absent extracted entry on the finite
domain is replaced with the fixed `default` row. Positions outside the domain
are absent from the bridge's normalized table.

`pathResult` evaluates the complete adaptive walk on this single total table.
`FarPaths fraction` means at least `fraction * 2 ^ depth` starting positions
produce `false`. `ApplicationError` is actual acceptance together with this
property of the requested table. This is an oracle-table testing claim, not a
public-language membership claim or FRI proximity theorem. It does not assert
that the particular sampled path rejects, that a separately supplied table
agrees with extraction, or that a particular intended computation has been
encoded adequately.

`checkpointTables_eq_pinned` proves exact agreement with the table carrier of
the existing theorem. `applicationError_iff_pinnedFailure` also proves that the
existential table witness in the ideal relation must equal this requested
total table, on every position in the domain. Thus existence of some other bad
table supplies no application error. Agreement is with the normalized,
default-completed checkpoint extraction; it is not an unconditional claim
about every authenticated reply or a later whole-log extraction.

## Event coverage and certificate

`verifier_queries_start` derives query coverage from the actual `run`
computation for every proof and every structural execution, including refused
or rejected runs. The challenge is enforced syntactically before the reads.
`experiment_queries_start` lifts this to the existing joint experiment, and
`applicationError_implies_checkpoint` proves the event inclusion on its
execution support. Stateful oracle simulation can only shrink that support.
No coverage or event-inclusion hypothesis is supplied to `soundness`.

This client has no query-free branch. Its random start is intrinsic to the
table test. A different client that accepts without a transcript query cannot
use this inclusion without a separate argument. The focused controls exhibit
an accepted query-free result with the application error and without the
bridge event, and prove that the actual client cannot produce that result.

`withTables_walk` proves that all adaptive reads evaluate on the same fixed
ideal table. `certificate` proves an escape bound of `1 - fraction` at the
single start challenge, using the finite fraction of accepted starts. All
remaining ideal computation is deterministic. The client makes no new
commitments; its initial root is exactly the statement's root.

## Joint bound and resource model

Let `r = additional + 2`, `h = depth + 1`, `V = 1 + r * h`, and let `q` bound
all prover queries on every path. For digest type `Digest`, put

```text
H = 4 * (q + V) / |Digest|
```

Then `AdaptiveOpening.soundness` proves

```text
Pr[ApplicationError] <= q * ((1 - fraction) + H)
                     + (1 - fraction) + r * h * H.
```

The experiment is exactly `Commitment.experiment`, run through one
`simulateQ randomOracle` from the empty cache. Its prover can query both
transcript keys and hash calls adaptively. The bound follows from
`Commitment.soundness`, first for its checkpoint event
(`checkpoint_soundness`), then by the proved application inclusion. There is
no additional Fiat–Shamir term and no assumption that the two oracle families
are independently realized by concrete primitives. The factor four is the
existing target charge for one root, two input labels, and one earlier answer.

`verifier_queryBound` and `verifier_costBound` follow from structural charged
walks and the existing authentication bound of at most `h` hash calls per read.
They cover arbitrary proof contents, cycles and repeated positions. Repeated
oracle calls, including cache hits, count towards these conservative bounds.
The prover's security cost is derived from its total query bound.

`pinnedRows_append` proves checkpoint freezing. `applicationError_unseen` uses
the existing first-match hashed-leaf extractor to prove invariance when
cache-consistent prover logs are deduplicated. The security theorem itself
allows repeats directly and does not require deduplication or a fresh-key
prover. Opening order, refusal on absent openings, and rejection of malformed
authentication paths are inherited from the existing `run` and scheme.
Acceptance uses the existing returned-`true` predicate; unused proof suffixes
are not required to be empty.

The fraction parameter is an `ENNReal`. Values above one cannot satisfy
`FarPaths` on a total finite table. This is one random start followed by
adaptive reads, so the theorem claims no independent repetition amplification.
The bound can exceed one; it is useful only with suitable parameters.

## Boundaries

`LeafHashing`, finite uniform raw challenges and a finite uniformly sampled
digest oracle are the existing model parameters. The proof adds no
cryptographic assumptions. It does not establish a concrete hash's random
oracle security, a native provider or encoding correspondence, a compiled
source connection, FRI, STARK, or extraction of an independently requested
oracle. Such connections require their owning theorems and any provider loss
at the joint stage. The implementation is checked by the focused
[`CommitmentApplication`](../../security/TestsSecurity/CommitmentApplication.lean)
controls; broad package and native validation are separate scopes.
