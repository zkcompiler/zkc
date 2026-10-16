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

[`ArkLib/Sumcheck/Multilinear`](../../docs/spec/multilinear-sumcheck-security.md)
separately connects the general MSB table and endpoint contracts to degree-one
ArkLib messages and its causal `Native.Core` interaction. It proves complete
`n / |F|` and partial residual `k / |F|` bounds for arbitrary effectful prover
strategies, plus honest completeness for arbitrary challenges. Its all-point
table-oracle realization and checked public-table observation are proved.
The `Causal` modules additionally prove unconditional acceptance domination for
stop-aware joint phases using existing PIR Execution records, including terminal
work and ordered LOW/HIGH receives. `VCVio/Execution` supplies reusable reachable
full-distribution replacement and value-returning transport. Canonical structured
round examples instantiate local query/checker laws; the actual imported
Sumcheck/Reduce bridge and zkc native correspondence remain separate work.

`VCVio/Schnorr` proves perfect honest-verifier simulation of the public transcript
and actual verifier result. The simulator uses only the public key and a uniform
response. Challenges are fixed independently of nonces. It does not prove
malicious-verifier or Fiat–Shamir security.

`Examples/StructuredSchnorrHonestView` derives the Interactive prover's public
messages from its actual checked source's ordered sends, then proves equality
with the existing `VCVio/Schnorr.honestView` and transfers its simulation law.
It uses fixed successful replies/send acknowledgements and honest delivery to
the actual checked verifier. The nonce is uniform in the VCVio experiment and
the challenge is fixed outside sampling; native providers and joint scheduling
are not modeled. `Examples/StructuredSchnorr` and the generic theorem retain
their handwritten honest strategy and imported verifier contracts.

`TestsSecurity.Audit` checks every owned declaration's transitive axiom closure.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Unrelated upstream
`sorry` declarations are not claims of this package. `clients/ArkLib.lean` in the
core package exercises reuse from an independent Lake package.

The Python [proof-request bridge](../../bridges/common/README.md) exposes the
imported scalar consumers through explicit requests. The multilinear API is
currently a standalone mathematical consumer. Neither successful sampling tests nor the
mere presence of a library dependency replaces the connection proofs.
