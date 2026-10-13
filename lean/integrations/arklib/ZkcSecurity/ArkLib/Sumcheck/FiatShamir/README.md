# Sumcheck restoration consumer

`ZkcSecurity.ArkLib.Sumcheck.FiatShamir` proves false-statement soundness for
finite-field, two-round, degree-at-most-two public-polynomial Sumcheck in the
pinned ArkLib cached state-restoration experiment. It also supplies a reusable
consumer of `Zkc.Protocols.Sumcheck.Common.VerifierContract`. The mathematical
contract is specified in [the formal model](../../../../../../docs/spec/sumcheck-restoration.md).

## Public interfaces

- `Knowledge`: generic `n`-round `extractor`, `prover_preserving`,
  `badChallenge_iff`, `badChallenge_card`, `locally_bounded`, and the fully proved
  `knowledgeCertificate`. Every authored prefix is covered, including prefixes
  inconsistent with an earlier guard or with honest execution.
- `Replay`: two-round `Statement`, actual native ArkLib `terminal` queries,
  `terminal_iff`, `outputLaw`, and `actualVerifier_accepts_iff` for the existing
  common imported-program contract.
- `Game`: `nativeGame`, `programGame`, `soundness`, `program_soundness`,
  `randomized_program_soundness`, and `soundnessProperty` / `soundnessConsumer`.
  `completion_queryBound` and `total_queryBound` charge final completion.
- `Observation`: `firstKey`, `secondKey`, `completedPath_eq`, `completion_log`,
  `secondKey_state_update`, and `reached_observations`. The last theorem exposes
  the early-stopping PIR state's effect count and challenge-site projection.

- `FullPrefix`: `soundness` and `program_soundness` for arbitrary public input
  and a fixed projection to `Statement F`. It consumes the separately proved
  `FiatShamir.Prefix` cached-oracle simulation; no cache equation is assumed.
- `EarlyStop`: `earlyVerify_acceptance` for every preexisting cache,
  `earlyGame_acceptance`, `early_soundness`, and actual query bounds.
- `Native`: `queryHandler`, `game`, `game_eq`, `game_observation`, `soundness`,
  `randomized_soundness`, and `game_queryBound`. The full process equation is
  transported before projecting acceptance from the retained execution record.

`Statement F` contains all nine public polynomial coefficients and the claim.
`Adversary F Salt` is a total `OracleComp` over ArkLib's restoration oracle,
returning a statement, both messages/salts, and a unit witness. It may adapt the
statement and proof after arbitrary queries, including prequeries, repeated
queries, and queries for second rounds before first rounds. `Salt` needs decidable
equality; it need not be finite.

For an all-branch adversary access bound `Q`, the quantitative bound is
`(Q + 2) * (2 / |F|)`, in `ENNReal`. The two completion accesses are charged even
when the adversary never queried its selected proof or ordinary PIR would reject
before either challenge. Cache hits count as accesses. The bound is informative
only at suitable field size and budget; the controls check `Q=3`, `|F|=101`, with
bound `10/101 < 1` and a nonempty false-acceptance event.

Private randomness can be sampled independently before selecting a family of
adaptive adversaries with one common all-branch bound. This does not claim a
separate normalization theorem for arbitrary interleaved private-coin effects.

## Full-prefix native consumer

The full-prefix keys are `(input, first message)` and
`(input, first message, first challenge, second message)`. Every well-typed key
can be queried, including inconsistent prefixes. The actual constructed model
uses `NativeConstruction.Binding Context F` as input: source identity,
construction identity, application context, exact receive/observe/challenge
schedule, all polynomial coefficients, and the claim are retained.

`Native.Selection` lets the adversary adaptively choose context, coefficients,
claim and both messages. The final game's source, construction and schedule are
fixed by theorem parameters; all other bindings remain queryable. `Native.game`
runs the actual selected process using `PIR.Proc.runM`, returns its complete
`Execution`, and shares the adversary's initially empty cached uniform oracle.
A generated `Imported.denote = NativeConstruction.experiment` proof instantiates
`Native.soundness`. The consumer does not accept local security as a premise.

For full-prefix games the bound is `(Q + 3) * (2 / |F|)`. The reduction reads the
first selected key once to select its second restoration salt, then charges both
completion accesses. The first completion access is a cache hit. The actual
early-stop game itself uses at most `Q+2` accesses. Acceptance equality with full
completion holds for every preexisting cache, but query logs and final caches
are not equated after an early rejection. A stopped process does not return its
local SSA transcript value; its handler state and reached event prefix remain
in the execution record.

The canonical umbrella remains usable independently; import `.FiatShamir.Native`
explicitly for the constructed-subject consumer.

## Validation

From `lean/integrations/arklib`:

```sh
lake build ZkcSecurity.ArkLib.Sumcheck.FiatShamir \
  ZkcSecurity.Examples.SumcheckFiatShamir TestsSecurity.SumcheckFiatShamir \
  ZkcSecurity.ArkLib.Sumcheck.FiatShamir.Native TestsSecurity.SumcheckFullPrefix
```

`Examples.SumcheckFiatShamir.sourceForms_soundness` covers the original, helper,
and Horner common-source imports. These are actual imported interactive verifier
bodies run in the named completion experiment, not the native constructed Merlin
participant. The standalone controls cover failed prefixes, a missing boundary
check, a missing final-completion budget, repeated/out-of-order queries, adaptive
statement choice, cache preservation, key binding, early-stop observations, and
why fixed-witness bounds cannot replace the existential bad event. The full-prefix
controls additionally exercise inconsistent prequeries, prior-challenge binding,
arbitrary prepopulated caches, early completion costs, and fixed native identities.

The integration declaration audit must import these modules. Their transitive
axiom closure permits only `propext`, `Classical.choice`, and `Quot.sound`; unused
upstream declarations bearing `sorry` are not evidence for this consumer.

## Trust and observations

The canonical first key contains `(statement, first message, first salt)`. The
second retains the first message/salt and contains the same statement, second
message, and second salt. Previous challenges are absent from both keys and are
reconstructed from the same table. The `FullPrefix` module provides the proved simulation for the distinct typed
full-prefix model; it does not identify a native byte provider with either oracle.

The ordinary PIR and completed replay have equal acceptance projections. Their
query logs and final states need not be equal: PIR reaches 0, 1, or 2 challenges
and stops after 3, 8, or 10 effects, while restoration completes both rounds. The
actual PIR execution record is retained by `programGame`; it is not substituted
with the completed native transcript.

There is no PCS, private polynomial, or commitment binding premise here. Native
export authenticity, parsing/rendering, Host initial-transcript and proof-buffer
wiring, field implementation, compiler/lowering, provider state, byte framing/codecs, sampling bias, concrete hash security, and
Merlin/STROBE conformance remain outside this mathematical theorem. Actual-body
normalization remains a required proved equation at the native
consumer boundary. The full-prefix/restoration simulation and all local security
premises are discharged. Native source/export authenticity and concrete provider
conformance remain separate even after a generated body equation is checked.
