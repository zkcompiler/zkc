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
both `n / |F|`. The bounds are nontrivial up to the exported maxima of two and
four rounds; excess counts refuse and contribute zero mass. The concrete
service discharges query and route premises for arbitrary network/callbacks and
all initial states. Reduction has no Boolean acceptance checker.
`Examples/CausalSumcheck/LogicalResidual` states the Reduction residual request
through a port-independent [logical context](../../docs/design/logical-contexts.md)
and applies the same bound through the retained root and through a separately
exported repacked root.
[Support](../../docs/support.md) records scope and validation.

`VCVio/Schnorr` proves perfect honest-verifier simulation of the public transcript
and actual verifier result. The simulator uses only the public key and a uniform
response. Challenges are fixed independently of nonces. It does not prove
malicious-verifier or Fiat–Shamir security.

`Examples/StructuredSchnorr` applies this law to the imported verifier contract
with a handwritten honest strategy. `Examples/StructuredSchnorrHonestView`
transfers it to the public view derived from the Interactive prover's checked
sends; [support](../../docs/support.md#interactive-schnorr) states its premises.

`Examples/StructuredSchnorrFiatShamir` applies VCVio's fixed-statement
Fiat–Shamir extraction to the imported verifier's Sigma instance.
`Examples/CompiledSchnorrFiatShamir` runs the compiled `example::Proof`
verifier with a random oracle on all transcript histories, through the core
[transcript-construction](../../docs/spec/fiat-shamir.md) and
[participant projection](../../docs/spec/participant-projection.md) rules.
Injective routing of histories (`Oracle/Encoding`) makes the experiment exactly
VCVio's Fiat–Shamir verification run, which gives its knowledge-soundness bound
under named assumptions, for the relation retained by the Proof Entry's own
export. `Examples/ExecutableSchnorrFiatShamir` transfers that bound to provers
of proof bytes for the validator program the runtime admits, through the core
[lowering rule](../../docs/spec/executable.md).

`FiatShamir/Interface` and `FiatShamir/Typed` prove
[Fiat–Shamir soundness over typed query sites](../../docs/spec/fiat-shamir-security.md#typed-query-sites):
for any validator signature with a transcript interface whose query sites
decode key-dependent raw answers, possibly refusing, and a round-by-round
certificate with an error per site, by VCVio's weighted adaptive bad-query bound
applied directly to the oracle on all event histories, for fixed and for
adaptively chosen statements. `FiatShamir/Sampling` states realized sampling
laws (exact, exact with refusal, point ratio with the KoalaBear and BLS12-381
factors, additive loss), `FiatShamir/Grinding` gated and compound sites with the
KoalaBear query phase, and `FiatShamir/Roles` role separation at one key.
`FiatShamir/Soundness` derives
[multi-round Fiat–Shamir soundness](../../docs/spec/fiat-shamir-security.md#the-participant-transform)
of the core transform as their instance at the participant interface;
`randomized_soundness` adds private randomness drawn before the oracle
computation, and `FiatShamir/Decoding` bounds challenges reduced from wide
uniform samples, additively and multiplicatively.
`acceptance_le_of_image` carries the fixed-statement bound over to a compiled
verifier that is an outcome image of the transform, and `acceptance_bind_done`
and `adaptive_acceptance_bind_done` move a final projection of the validator's
result into the acceptance predicate. `Examples/SumcheckFiatShamir` instantiates
the theorems for the actual imported Sumcheck verifier, with ArkLib's
single-round successor bound as the per-round soundness, bounds the composed
Reduction root as a reduction to a residual evaluation claim, and states
composition theorems whose only premise about a compiled verifier is its
construction equality. `Examples/CompiledSumcheckFiatShamir` discharges that
premise for the compiled Sumcheck `example::Proof` verifier with the core
composed rules and states its
[fixed-statement and adaptive soundness](../../docs/spec/fiat-shamir-security.md#the-compiled-sumcheck-proof-entry);
the adaptive form keeps the determining binding as a premise.
`Examples/ExecutableSumcheckFiatShamir` transfers both bounds to provers of proof
bytes for the validator program the runtime admits, through the core
[lowering rule](../../docs/spec/executable.md#the-compiled-sumcheck-proof-verifier)
and `VCVio/Pruning`: host validation prunes the compiled verifier's acceptance by
rejections at every budget, so it accepts at most as often. Its adaptive form
uses a binding of the table values, claim and round count whose events
determine the statement, which discharges the premise.

`Examples/GkrFiatShamir` gives the plain GKR verifier a round-by-round
certificate composed per phase (`FiatShamir/Composition`), with ArkLib's
single-round successor bound at degree two for the layer rounds (`ArkLib/Gkr/Layer`)
and Schwartz–Zippel for the line restriction, and
`Examples/CompiledGkrFiatShamir` transfers its
[fixed-statement bound](../../docs/spec/fiat-shamir-security.md#the-compiled-gkr-proof-entry)
to the compiled GKR `example::Proof` verifier through the checked reading of its
exported instructions.

`ArkLib/Fri` models the verifier of the FRI library's low-degree test with
ideal commitments and proves its
[round-by-round soundness](../../docs/spec/fri-security.md). `Protocol`
transcribes the verifier, the prover's moves and the sequential position draws;
`Correspondence` shows that its acceptance is ArkLib's FRI query acceptance on the
committed trace; `Soundness` states the certificate, with the proximity premise as
a named hypothesis, and bounds acceptance for every adaptive prover;
`UniqueDecoding` discharges the premise with ArkLib's proved unique-decoding
results. These modules use the per-round lemmas of ArkLib pull request #992,
which this package applies to its pinned ArkLib revision as a declared patch
([`compatibility.json`](compatibility.json); see the
[dependency baseline](../../docs/dependencies.md)). Preparation applies it.

`VCVio/SigmaAnd` composes two VCVio Σ-protocols with one shared challenge.
Completeness and special soundness compose directly; zero knowledge composes
from special HVZK, a simulator given the challenge. It gives VCVio's perfect
HVZK with a challenge-first simulator, and over a finite challenge space it
follows from such a simulator. `VCVio/SigmaAndSchnorr` derives Schnorr's special HVZK from the upstream
simulator. `Examples/SchnorrAndSigma` and `Examples/ChaumPedersenSigma` connect
the imported Schnorr AND and Chaum–Pedersen verifiers to the composition of two
Schnorr instances and to Schnorr over `G × G`, and apply VCVio's fixed-statement
Fiat–Shamir extraction to both; [support](../../docs/support.md#sigma-compositions)
states the scope.

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
