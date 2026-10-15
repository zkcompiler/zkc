# Multilinear interactive Sumcheck

The optional `ZkcSecurity.ArkLib.Sumcheck.Multilinear` package connects the
[independent table and endpoint contracts](multilinear-sumcheck.md) to ArkLib's
actual interactive Sumcheck development. It proves complete soundness,
honest completeness and partial residual soundness for arbitrary round counts.
It does not import `libraries/sumcheck/lib.zkc` or establish native execution
correspondence. The existing imported two-round quadratic examples are separate.

## Representations and ordering

`Message.lean` interprets `(a0,a1)` as
`Polynomial.C a0 + Polynomial.C (a1-a0) * Polynomial.X`. The pair contains
values at zero and one. `messagePolynomial_degree`, `message_evaluate`,
`message_boundary`, `endpoints_evaluate`, `endpoints_message` and
`message_endpoints` prove a lossless degree-one representation over every
commutative ring. No division by two or odd-characteristic assumption occurs.

`Table.lean` applies upstream `MvPolynomial.MLE` to
`fun assignment => table (fun i => decide (assignment i = 1))`.
This converts `Fin 2` to `Bool` coordinate by coordinate and reuses the existing
MSB `Table`, `ofVector`, `extension`, `fixFirst` and `fixPrefix`. It never uses
upstream `MLE'` or assumes agreement with `finFunctionFinEquiv`.

- `statement_evaluate` proves equality at every field/ring point, including
  zero coordinates, over a commutative ring.
- `statement_degree` uses `MvPolynomial.MLE_mem_restrictDegree` to construct
  `oracleStatement`, an actual upstream polynomial of individual degree one.
- `statement_fixFirst` and `statement_fixPrefix` preserve the existing ordered
  concatenation of the challenge prefix and remaining coordinates.
- `statement_sum` and `statement_sum_ofVector` equate the upstream Boolean-cube
  sum with the ordered table/vector sum. The Boolean embedding requires only
  nontriviality of the ring, so characteristic two is included.

These are evaluation and degree laws, not an unnecessary equality between two
large polynomial encodings or an assertion about upstream flat storage.

## Causal interaction and the original oracle

`Protocol.lean` specializes `Sumcheck.Interaction.Native.Core.protocol` with
the existing endpoint type and interpolation function. `EndpointProver` is
ArkLib's ordinary `Prover.Strategy`, with arbitrary ambient computations before
message selection and in every public response continuation. There is no new
process IR, recursive interpreter or protocol kernel.

`execute_round` exposes the existing execution equation:

1. Run the prover computation that chooses a pair and its continuation.
2. Check `a0+a1 = current`.
3. On success, run the verifier challenge computation, then the prover's
   response to `some r`; append `r` and interpolate the target.
4. On failure, run the prover's response to public `none` and return rejection.
   The verifier challenge computation is not run on this branch.

`execute_transport` applies upstream `Core.execute_transport` to interpret
every pair as a degree-one polynomial. It retains private continuation effects
and public abort effects. Original interfaces and deterministic handlers may
differ provided their complete original-oracle behaviors agree. This equality
concerns the closed result and ambient effects, not raw message-query traces.

`oracle_realized` derives upstream realization from the concrete premise
`∀ point, original.eval impl ((),point) = extension n table point`.
`execute_preserves_original` proves that every supported returned claim retains
that entire behavior. The table and initial claim are fixed before the run;
soundness does not require any adversary-private table to agree with them.

`publicTable_observation` equates accepted-event computations with the core
raw-vector `check` when `ofList? n values = some table`. It preserves rejection
as a nonaccepting result and checks exactly the returned ordered point. ArkLib
exports a claim without querying the original polynomial at the final leaf;
this theorem describes the separate public-table discharge observation.

## Complete security and completeness

`soundness_of_oracle` in `Soundness.lean` (namespace
`ZkcSecurity.ArkLib.Sumcheck.Multilinear`) proves

```text
Pr[returned claim satisfies the original-table evaluation relation] ≤ n / |F|
```

Its premises are exactly:

- `[Field F] [Fintype F] [DecidableEq F] [SampleableType F]`;
- an arbitrary fixed `Table F n` and `claim ≠ booleanSum table`;
- an arbitrary ordinary causal endpoint prover using `unifSpec`;
- the all-point realization premise for the selected original oracle and
  deterministic `QueryImpl ... Id` handler.

The implementation executes exactly `n` rounds starting at zero. It uses the
injective upstream `boolEmbedding F`; every reached verifier challenge is the
fresh uniform computation `$ᵗ F`. Arbitrary prover oracle queries remain fresh
draws in the same probability semantics, and continuations can retain all past
answers. The prover cannot select the current message after receiving the
current verifier challenge. Uniformity here is VCVio's mathematical sampling
semantics, not a property inferred from a native service name.

The proof constructs the degree-one table polynomial and transports the actual
execution to `Sumcheck.Interaction.Native.execute_soundness`. Its false relation
premise follows from `closed_statement` and the false table sum. The resulting
bound is `n / |F|`, with no quadratic factor. It may exceed one for large `n`;
useful parameters ordinarily have `n < |F|`.

`experiment` supplies the canonical realized table oracle explicitly.
`soundness` proves the bound for this experiment without an oracle premise.
`publicTable_soundness` proves it for the checked raw-vector observation, with
the concrete false premise `claim ≠ values.sum` and exact shape decoding.
It also uses the canonical oracle. `publicTable_soundness_of_oracle` supplies
the general form under explicit all-point realization of a selected handler.
All results include zero rounds. A false singleton claim has acceptance
probability zero; a true singleton claim accepts.

`Completeness.lean` maps upstream's actual honest projected-polynomial strategy
back to endpoints. At the empty prefix, `projected_first_evaluate` equates its
polynomial with the ordered sum after `fixFirst`; `projected_first_endpoints`
identifies that first pair with `honestMessage`. An all-prefix identification
with the source's iterated prover is a separate correspondence obligation.
`support_completeness` proves truth of every supported
honest result for any table and any ambient challenge computation, over a
nontrivial commutative ring with decidable equality. `perfectCompleteness`
gives probability one for any normalized `ProbComp` challenge. Intermediate
truth is proved by upstream completeness, not supplied as an assumption.

## Partial residual security

The core `Zkc.Polynomial.Multilinear.Marginal` defines
`sumRemaining remaining count table`: retain the first
`count` Boolean coordinates and sum the other `remaining` coordinates of the
same fixed table. It uses the existing coordinate concatenation.

`booleanSum_sumRemaining` preserves the original total. `honestMessage_sumRemaining`
preserves the honest endpoint pair in the core round contract, and
`fixFirst_sumRemaining` commutes with restriction. These algebraic laws remain
available without ArkLib. The central law is

```text
extension count (sumRemaining remaining count table) point
  = booleanSum (fixPrefix count table point).
```

The optional `Residual.lean` defines `reductionExperiment`, executing the same
causal `count`-round endpoint tree
with the realized marginal oracle, observing the original table's
`ResidualClaim count table point target`. `reductionExperiment_eq` proves
equality with the complete experiment on the marginal table. Thus
`residual_soundness` proves `count / |F|` from a false original total claim,
against every causal effectful endpoint prover, including zero rounds.
`residual_perfectCompleteness` proves probability one for the marginal honest
strategy and the true original sum, by transporting the complete honest result.

This avoids a second partial executor or a new probabilistic induction.
The exported marginal oracle is a proved view derived from the original table;
it is not the original higher-dimensional oracle's raw interface. The theorem
observes residual truth. It neither pads the point nor asserts a complete
evaluation of the original table. It is not a native `Reduce` correspondence.

## Validation and remaining integration boundary

`TestsSecurity.MultilinearSumcheck` exercises endpoint/coefficient distinction,
characteristic two, MSB coordinate order, residual versus full evaluation,
zero rounds, arbitrary effectful strategies and abort preservation. It reuses
the core F97 early-challenge attack through the polynomial adapter. A separate
control proves that a constant zero challenge accepts a false zero-table sum
with the fixed causal pair `(0,1)`: guard order alone is insufficient.
An explicit `SampleableType.ofFintype (ZMod 97)` instantiation applies the
general soundness theorem to every one-round strategy with bound `1 / 97`.
It checks that all quantitative typeclass premises are inhabited together.
True singleton acceptance shows that the false-initial premise is necessary.
These controls use ordinary proofs and kernel reduction, never `native_decide`.

The exhaustive optional audit covers every owned declaration and its transitive
axioms. Unrelated upstream files contain `sorry`; selected proof dependency
closures must contain only `propext`, `Classical.choice` and `Quot.sound`.
The standalone client consumes both complete and residual bounds. Core imports
remain independent of ArkLib/VCVio, and existing quadratic/factor examples remain.

The next process adapter must connect a `PIR.Proc` contract to this causal
strategy/handler experiment. The actual source receives **two ordered scalars**;
it must preserve the intermediate state and possible stops, aggregate them
before the verifier challenge, and prove the selected observation equivalence.
It must not equate that source effect tree with an atomic pair receive.

Role-local received challenges remain distinct from sent/query values until
an explicit delivery theorem relates them. Public field, table, count, maximum,
service and role agreement, dynamic count failure, source shape guards and
native capacity belong to that boundary. Whole-function helper/vector/fold/
repeat lowering and original-oracle realization must be proved or explicitly
assumed there; no special Sumcheck kernel is provided. Native.Core in this
document is ArkLib's mathematical interface, not zkc native execution.

No result here establishes production field arithmetic, a CSPRNG/provider,
Fiat–Shamir, transcript encoding, retries/grinding, PCS binding, extraction or
knowledge soundness. Plain `ProbComp` is normalized; arbitrary strategies retain
their effects and the public rejection branch, but this does not model arbitrary
nontermination or a native timeout/retry policy.
