# ArkLib and VCVio security consumers

This optional `zkc_security` Lake package contains `ZkcSecurity`. Its core
connection modules depend on generic zkc contracts; particular imported-program
clients live in `ZkcSecurity.Examples`. `lake build` builds every maintained
module, compatibility application, source-form client and declaration audit.
The manifests use the [shared tested baseline](../../docs/dependencies.md).

For Sumcheck, `ArkLib/Sumcheck` constructs native ArkLib messages, causal prover
strategies and a realized public polynomial oracle. Evaluation, degree,
Boolean-domain and accepted-event equalities are proved. `soundness` applies
ArkLib's native interactive theorem to actual PIR execution; `randomized_soundness`
allows an arbitrary private distribution of causal strategies. The bound is
`4 / |F|` for the selected two-round quadratic public-polynomial verifier.

`VCVio/Schnorr` proves perfect honest-verifier simulation of the public transcript
and actual verifier result. The simulator uses only the public key and a uniform
response. Challenges are fixed independently of nonces. It does not prove
malicious-verifier or Fiat–Shamir security.

`VCVio/Schnorr/FiatShamir` separately proves fixed-statement cached-RO game
correspondence and quantitative extraction for realized constructed Schnorr
verifiers. Its [feature reference](ZkcSecurity/VCVio/Schnorr/README.md) records
the exact adversary, final-query budget, actual constructed participant example,
consumer API, and remaining native/provider assumptions.

`TestsSecurity.Audit` checks every owned declaration's transitive axiom closure.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Unrelated upstream
`sorry` declarations are not claims of this package. `clients/ArkLib.lean` in the
core package exercises reuse from an independent Lake package.

`ArkLib/FiatShamir/Prefix` proves a two-round full-transcript classical-RO
simulation into ArkLib salted restoration, including inconsistent and out-of-order
queries, shared-cache completion, and the explicit `Q + 1` translated-adversary
budget. Its extraction bound is `(Q + 3) * error` under the protocol's all-prefix
knowledge premises. The [model specification](../../docs/spec/prefix-simulation.md)
records the exact supported keys and remaining native/provider boundary.
Run its standalone checks from this directory:

```sh
lake build ZkcSecurity.ArkLib.FiatShamir.Prefix.Security TestsSecurity.PrefixSimulation
lake env lean TestsSecurity/PrefixAudit.lean
```

`ArkLib/Sumcheck/FiatShamir` discharges those all-prefix conditions for quadratic
Sumcheck and connects actual constructed two-round verifiers to the full-prefix
false-acceptance bound `(Q + 3) * 2/|F|`. Its
[feature reference](ZkcSecurity/ArkLib/Sumcheck/FiatShamir/README.md) separates
complete execution correspondence, acceptance-only completion and oracle costs.

The Python [source proof-request bridge](../../bridges/common/README.md) and
[constructed-program requests](../../docs/spec/fs-verification.md) expose the
selected consumers through explicit requests. Neither successful sampling tests nor the
mere presence of a library dependency replaces the connection proofs.

`ArkLib/FiatShamir/Transcript` supplies a direct bound for a fixed finite list of
heterogeneous public-coin rounds. Full prefixes retain every earlier challenge;
VCVio's adaptive bad-query theorem yields `(Q + rounds.length) * error` under
ArkLib's all-prefix knowledge laws, without salt preparation. The generic
`Sumcheck/FiatShamir/FiniteRounds` consumer discharges these laws and connects
acceptance to the existing whole typed Sumcheck source for any finite `n`.
Its bound is `(Q+n) * 2/|F|`. The [model specification](../../docs/spec/finite-transcript.md)
separates this theorem from native loop import and early-stop cache equivalence.

`ArkLib/KZG/OpeningSum` connects a typed two-opening evaluation-sum verifier to
actual ArkLib KZG operations and a concrete t-SDH adversary. The
[composition contract](../../docs/spec/opening-composition.md) records the
registered-polynomial experiment and explicit hardness/resource boundary.
The reduction also accepts any verifier satisfying the common process contract.
