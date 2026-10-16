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

## Stop-aware joint execution and completion

`Causal.Phase`, `Causal.Completion` and `Causal.Soundness` connect finite joint
execution phases to the ordinary endpoint strategy. They reuse `PIR.Execution`
and `followM`; they are a proof-side family, not a source AST or second process
evaluator. LOW and HIGH are separate computations. LOW selects HIGH's
continuation and residual state, so acknowledgments and adaptive second-message
selection remain explicit. HIGH selects the following service/delivery work.

The order is LOW, HIGH, boundary guard, pre-draw work, fresh `$ᵗ F`, post-draw
work, challenge delivery, trusted advance, and the next round. Zero rounds run
a trusted terminal phase before the mathematical observation. Any inner stop
is nonaccepting, with its actual residual state and ordered observation prefix.
The phases describe joint execution, including trusted work, rather than only
adversary actions. A `ProbComp` always returns an Execution record; native
nontermination is not supplied by this finite model.

Bare participant rejection uses `publicAbort = noOp`.
`noOp_abort_is_bare` proves this equality through arbitrary probabilistic
prefixes. A runtime that exposes public abort can instead use the explicit
callback: `abortAfter_returned` retains both event prefixes and the callback's
post-state. The already failed guard stays the primary reject reason even when
the callback stops. `complete` runs that callback in the endpoint `none`
continuation. Public abort effects do not disappear from the open computation.

`domination` proves an unconditional accepted-event upper bound for arbitrary
finite n. On stopped branches `complete` supplies dummy endpoints. On completed
interaction phases it follows the actual computations. The endpoint leaf type
is Unit, so it cannot retain arbitrary terminal work. Completion therefore
promises acceptance domination, not equality of traces or of acceptance. The
chosen completion's strict inequality on a delivery-stop control demonstrates
this distinction; it is not an impossibility theorem about every completion.

The initial claim may be verifier-private. For each fixed claim the completion
can hardcode it, because existing soundness quantifies over every endpoint
strategy for that claim. No future challenge is available before its explicit
draw. `history_domination` integrates pointwise completion over outer histories;
it does not establish freshness or independence of a random outer claim.
Provider laws must hold at each reached history. No P-side table is identified
with V's table implicitly. `observer_capacity_exclusion` only intersects an
accepted event with a caller predicate. This differs from an explicit delivery
stop and never conditions or renormalizes probability.

`endpointGame_execute` proves equality with ArkLib's actual `Native.Core.execute`
observation. Together with the existing table oracle realization and soundness,
`phase_soundness` gives n/card(F). `phase_publicTable_soundness` gives the raw
public-vector form using `check_eq_true_iff`, `booleanSum_ofList?` and
`publicTable_observation`. `MSBChronology` identifies chronological challenges
with `List.ofFn` coordinates; its snoc law preserves order. `residual_phase_soundness`
gives k/card(F) for `ResidualClaim` of the original table, through the proved
marginal view. `residualTerminal remaining count table` takes both dimensions
explicitly because their sum alone cannot determine the split. All include zero
rounds; `zero_round_false_mass` states that case
explicitly. `malformed_raw_zero` gives zero raw-observation acceptance for an
incorrect vector length, without a freshness or false-claim premise.

## Local distribution and computed-value contracts

`ZkcSecurity.VCVio.Execution` owns reusable probability laws over existing PIR
execution. `SameDist` compares full distributions with every output set
measurable, including outcome, private state and event order. Its equivalence
and bind laws preserve arbitrary measured suffix observations. `Reaches`
restricts local laws to supported returned states. The pinned uniform oracle's
positive-singleton theorem proves `SameDist.support_eq` and `reaches_iff`;
this transfer is not claimed for arbitrary weighted oracle interpretations.
`reaches_follow` propagates explicit invariants. `follow_congr_of_reaches`,
`SameDist.follow_congr` and `replace_follow_prefix` compose local replacement
without invoking suffixes on stopped prefixes.

The upstream Stateful handler equivalence quantifies over OracleComp clients
and projects hidden state. These laws instead operate on full PIR Execution
records, reusing upstream evalDist/bind/support mechanisms without a new
interpreter. They compare the same state type; a different-state interpretation
needs its own correspondence.

`runM_bind_transport` transports returned values, not just Unit work.
`runM_bind_determined` handles effectful trusted work followed by a determined
value, retaining stops and events. `runM_determined_of_proc` derives the local
execution law from a Proc-level body equation. `checked_le_of_proc` composes a
Boolean checker through any prefix, requiring only that true implies the
mathematical terminal predicate. A conservative checker is sufficient.

`Examples.CausalSumcheck` is a canonical structured regression, not the imported
Sumcheck body. It uses the current `participantInterface F G`, root-local Nat
roles, service operands, ownership restriction/masking and explicit site/action
interpretations. Each operation supplies the actual typed empty callback tuple,
empty `ProtocolTable`, and identity root `ProtocolContext` to
`protocolOperationWith`. Self is fixed at root role 1 and its peer at role 0;
the context's immutable role map and absent application prefix preserve those
roles and the root site names. This fragment contains no protocol application
or repeat. Its calculated round consumes actual typed fieldAdd/fieldEqual,
vectorAppend and interpolation arithmetic results. The retained append helper
is hand-built and checked through the ordinary helper table, not recognized by
its name. Terminal work receives the computed point and claim.

`calculatedRound_cut` and `phase_at_cut` prove the exact local decomposition
through round mark, LOW, HIGH, guard and query mark. Given prefix reachability
and full local query `SameDist` against `freshQuery` on that invariant,
`calculatedRound_distribution` proves full round distribution equality.
`calculatedRound_soundness` and `checked_calculatedRound_soundness` derive the
one-round bound. Entire-game equality or domination is never a premise. The
original syntactic query law remains a stronger sufficient regression.

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

`TestsSecurity.CausalSumcheck` additionally checks stopped prefixes before HIGH,
after guard/query/delivery and during terminal work; adaptive HIGH after the
first acknowledgment; public abort effects; zero rounds; honest mass one;
constant-provider failure; and the early-LOW attack. In ZMod 2 that actual
structured handler has uniform query marginal and false-claim acceptance one,
so it cannot satisfy even the reachable full-distribution contract. A literal
fresh-HIGH-only sample has mass one half in this control. The bijective sampler
r ↦ 1-r satisfies the law on the reached false flag and composes through two
queries; an unreachable constant-provider flag violates the specified law.
Effectful determined values and Proc-level conservative checker contracts are
also exercised.

The exhaustive optional audit covers every owned declaration and its transitive
axioms. Unrelated upstream files contain `sorry`; selected proof dependency
closures must contain only `propext`, `Classical.choice` and `Quot.sound`.
Import and declaration guards keep the exact `ZkcSecurity.VCVio.Execution`
module independent of ArkLib, protocol applications, source syntax and examples;
the Causal module family cannot depend on source syntax or examples. The rules
do not restrict `ZkcSecurity.VCVio.Schnorr`'s existing Schnorr protocol dependency.
Enforcement controls check rejected type/body dependencies and permitted owners.
The standalone client consumes complete, residual and stop-aware phase bounds,
plus the local distribution composition API. Core imports
remain independent of ArkLib/VCVio, and existing quadratic/factor examples remain.

The next imported-source adapter must connect the admitted Sumcheck/Reduce
`PIR.Proc` bodies to these causal phases and handler contracts. The actual source receives **two ordered scalars**;
it must preserve the intermediate state and possible stops, aggregate them
before the verifier challenge, and prove the selected observation equivalence.
It must not equate that source effect tree with an atomic pair receive.

The next source-security gate must derive reached-state freshness for an
arbitrary adversarial receive/send handler composed with an explicit uniform
query service. The honest handler is only a positive regression. That composition
proof must retain private state, ordered events, stops and history invariants,
then discharge the full local query law and the actual terminal checker's value
law. Neither a uniform reply marginal nor an honest-only handler theorem closes
this adversarial gate. Compatibility with the retained application/repeat API
does not supply the imported Sumcheck source-security bridge.

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
