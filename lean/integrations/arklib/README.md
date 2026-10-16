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
round examples instantiate local query/checker laws and retain their explicit
reachable-state premises.

`VCVio.Execution.runM_sameDist` lifts per-operation distribution equality through
arbitrary value-adaptive processes, retaining outcome, state and ordered events.
It does not equate a handler's internal oracle-query cost. Query-sensitive security
consumers require their own resource connection.

`VCVio/StructuredUniform` constructs a
[uniform query service](../../docs/spec/uniform-query-service.md) around arbitrary
structured receive/send handlers. Its laws preserve complete executions at every
state and refuse unconfigured site/domain/handle tuples. The Sumcheck example
owns its source-qualified route and general-count full-distribution transport.
`Examples/CausalSumcheck/SourceVerifier` proves the complete admitted Sumcheck
returned-true bound and Reduction's external-table residual-observation bound,
both `n / |F|` for every count. The actual roots execute at most two and four
rounds respectively; excess counts refuse and contribute zero mass. The concrete
service discharges query and route premises for arbitrary network/callbacks and
all initial states. Reduction has no Boolean acceptance checker.
[Support](../../docs/support.md) records scope and validation.

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
The actual-root bounds use the empty parent context and verifier role 1;
the process transport permits arbitrary contexts and role mappings.

`clients/UniformComposition.lean` separately reuses the concrete service,
general-count process bounds and both actual imported-root bounds.
From the repository root, `python3 lean/checks/check_clients.py --with-arklib`
checks Main, ArkLib and UniformComposition as separate Lake consumers, including
their declaration audits. Without the flag it checks only Main.

The Python [proof-request bridge](../../bridges/common/README.md) exposes the
imported scalar consumers through explicit requests. The multilinear mathematical
API and its admitted-source uniform-service clients are Lean consumers; they are
not exposed by that scalar request interface. Neither sampling tests nor the
presence of a library dependency replaces the connection proofs.
