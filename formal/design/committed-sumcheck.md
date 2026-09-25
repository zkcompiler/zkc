# Fixed-table committed Sumcheck

`Zkc.Protocols.Sumcheck.Committed.soundness` proves the scoped
interactive bound `2n / |F| + epsilonOpen` for two honestly committed originals.
The deterministic connection reaches the maintained direct-source acceptance
event on the **same adaptive round strategy and same verifier tape**.

This is a mathematical connection to `Sumcheck.Source.rounds` and
`Security.source_soundness`. There is no theorem yet interpreting the portable
`examples/protocols/two-factor.json` module, its generated roles, or its native
arkworks execution as this experiment.

## Objects and execution

`Statement scheme` fixes logical high-bit vectors `left` and `right` and one
opaque setup before the verifier coins. Its polynomial is
`Multilinear.productCoefficients n (ofVector left) (ofVector right)`, the product
of the two multilinear extensions. Its Boolean sum is the original statement's
sum. This is not the multilinear extension of a pointwise product table.

`Scheme` gives abstract setup, key, commitment, proof, commit, and check types
and functions. A setup selects the prover and verifier keys. Both advertised
commitments are computed by `scheme.commit`, under that selected prover key,
on `Layout.toLowStorage` of the immutable originals. An adversary does not
supply these commitments or select an unrelated verifier key in this experiment.
The interface has no cryptographic axioms or correctness fields. An adapter
must identify its `Setup` with actual honest setup outcomes and justify the
opening experiment assumption; the type alone does not prove that external fact.
For a randomized commitment implementation, the selected setup/key must also
carry its fixed commitment randomness. The current interface is deterministic
once setup/key and original table are fixed.

The adversary has arbitrary explicit state and four unrestricted callbacks:
`send`, `react`, `openLeft`, and `openRight`. `send` chooses a quadratic message
before the next coin is delivered; `react` receives that coin. `openLeft`
receives the actual post-round private state and reached query. Its successor
state and reply are available to `openRight`. Thus the two replies may be
correlated and the second may depend on the first. A callback receives no
unconsumed verifier-tape suffix. With fixed state and callbacks, it can retain
the entire observed history in its state.

`roundExecution` uses the existing `Source.rounds` and `Execution.handler`
directly. Its `PIR.Execution` retains the stopped outcome, event prefix, private
successor state, and unused tape suffix. `run` creates no opening query after
round rejection. On success, it derives the point from the returned ordered
challenge list and the claim from the returned accumulator. The first opening
is checked against the original left commitment at that point. A failed check
prevents the right request. Otherwise the right response is checked against
the original right commitment at the identical point, and the terminal check
requires `z = vf * vg`.

`reached_query` proves, rather than assumes, that a returned terminal has
`point = tapePoint n coins` and
`finalClaim (Execution.strategy send react n prover) claim coins = some z`.
Although the reused coordinate lookup is total, this theorem identifies every
successful query with a complete actual tape point. Rejected prefixes acquire
no fabricated complete point.

## Events and proof

`Accepted` means that this `run` produced a terminal whose two opening checks
and product equality pass. `BadOpening` means that this same run produced either
an accepted false left opening, or an accepted false right opening after the
left check passed. Falsity is measured against the fixed original extension at
the actual reached point. The event does **not** require terminal product
equality or overall protocol acceptance.
Probabilities include all rejecting tapes; there is no conditioning on reaching
the opening stage.

The proof has these steps:

1. `accepted_correct_source` uses `reached_query`, both correct reached values,
   and `Statement.polynomial_eval` to derive the maintained direct-source
   acceptance on that exact strategy and tape.
2. `accepted_source_or_bad` proves the pointwise event inclusion
   `Accepted subset DirectSourceAccepted union BadOpening`.
3. `acceptance_le_source_add_bad` lifts this inclusion through the existing
   exact rational average on uniform product tapes.
4. `soundness` applies `Security.source_soundness` and the external hypothesis
   `badOpeningProbability statement adversary claim prover <= epsilonOpen`.

The loss hypothesis is about an independently defined joint false-opening
event. It is neither the desired soundness conclusion nor a predicate silently
restricting received values to correct openings. A split union bound would need
bounds for the two actual events in this experiment; independence is unnecessary.

## Exact assumptions

| Assumption | Where it appears |
|---|---|
| `F` is a finite field with decidable equality | `soundness` typeclass arguments |
| Every coordinate is uniform over all of `F`, independently of the other coordinates | `UniformTape.average` on `AdaptiveTape.Tape F n` |
| Originals, setup, claim, strategy, and initial private state are fixed before this tape | Arguments outside the probability average |
| Each round message is chosen before the current challenge | `Execution.strategy` and the reused source handler |
| Commitments belong to the fixed originals under the selected setup/key | `Statement.leftCommitment` and `rightCommitment`, computed by definition |
| The advertised sum is false for those originals | `claim != statement.polynomial.booleanSum` |
| The actual joint adaptive false-opening probability is at most `epsilonOpen` | The sole external loss premise of `soundness` |

`randomized_soundness` additionally mixes finite uniform private seeds sampled
independently before the verifier tape. Its opening hypothesis bounds the mixed
joint event; it does not demand a bound separately for every private seed.
The fixed-setup theorem is conditional on the selected setup and opening bound.
It does not claim that a cryptographic theorem averaged over setup automatically
holds for each setup. If an adapter only has an averaged setup bound, it must
transport that distribution and average the pointwise connection accordingly.

The arithmetic theorem includes `n = 0`. With no coins it still checks the
original constant product. An actual positive-arity PCS must construct its
adapter only for `0 < n`; the mathematical zero case does not admit an invalid
PCS setup. Typed callbacks model supplied replies and the complete ordinary
tape; byte decoding, missing packets, provider exhaustion, scheduling, and
resource-admission policies need their implementation refinement.

## Coordinate law

`Zkc.Polynomial.Layout` reuses `Multilinear.index`, `vertex`, `ofVector`,
`extension`, and `productCoefficients`. It introduces only the storage conversion
and its laws. `bitReverse_involutive` and `bitReverse_lowIndex` imply `table_eq`:
low-bit interpretation after bit reversal is the original high-bit table.
`extension_eq`, `product_eq`, `product_eval`, and `product_booleanSum` preserve
the same point and full polynomial over any commutative ring. The full
polynomial equality transports all existing ordered restriction/round laws.
`Statement.stored_polynomial` applies the layout law to the actual subjects
passed to commit. No fixture emitter or experimental namespace is imported.

## Validation and remaining bridge

`Tests.PolynomialLayout` contains finite counterexamples for omitted storage
permutation, reversing the point after conversion, and collapsing the product
before extension. It also checks arity zero.

`Tests.CommittedSumcheck` checks foreign-point and substituted-original
counterexamples, first and second opening failures, early and later round
failure prefixes, adaptive state/replies, both sides of the joint bad event,
and a bad-opening run that fails terminal equality. Honest challenges include
non-Boolean field points. A transparent table-carrying reference scheme proves
zero opening loss for every adversary and a false sum attains the exact
committed acceptance probability `2/5`. This reference is not a succinct PCS.
All finite controls use kernel reduction; no native decision oracle is used.

`Tests.CommittedAudit` audits every declaration owned by the new library and
test modules, including generated declarations and transitive axioms, and
prints the main theorem assumptions. Regenerate exhaustive audit imports when
adopting these files so the normal main-package audit also includes them.

The actual portable example has a `ProductSumcheck` child and two invocations
of `FactorOpening`, followed by `CheckTerminal`. A future source/native bridge
must show that its admitted inputs and selected setup/key denote this
`Statement`; its immutable commitments and ordered point follow this layout;
its hostile replies and failures correspond to this runner; and its actual
challenge service has the stated tape law. The current proof supplies neither
that bridge nor arkworks cryptographic security, setup security, extraction for
arbitrary commitments, Fiat-Shamir soundness, or zero knowledge.
