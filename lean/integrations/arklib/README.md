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
VCVio's Fiat–Shamir verification run; its knowledge-soundness bound, under named
assumptions and for the relation retained by the Proof Entry's own export, is
the registered knowledge endpoint applied to the subject's evidence
(`Examples/Subjects/Schnorr`). `Examples/ExecutableSchnorrFiatShamir` transfers that bound to provers
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
`adaptive_soundness_public` discharges the adaptive form's determining premise
with one typed public-value binding event of the table values, claim and round
count (`FiatShamir/Binding`). That binding establishes statement determination
only; that the native transcript absorbs the encoded rows remains assumed.
`Examples/ExecutableSumcheckFiatShamir` transfers both bounds to provers of proof
bytes for the validator program the runtime admits, through the core
[lowering rule](../../docs/spec/executable.md#the-compiled-sumcheck-proof-verifier)
and `VCVio/Pruning`: host validation prunes the compiled verifier's acceptance by
rejections at every budget, so it accepts at most as often. Its adaptive form
uses the same typed public-value binding.

`Examples/GkrFiatShamir` gives the plain GKR verifier a charged round-by-round
certificate composed from one reduction per phase (`FiatShamir/Reduction`), each
challenge site charged its own error: ArkLib's single-round successor bound at
degree two for the layer rounds (`ArkLib/Gkr/Layer`) and Schwartz–Zippel for the
line restriction. `Examples/CompiledGkrFiatShamir` transfers its
[fixed-statement bound](../../docs/spec/fiat-shamir-security.md#the-compiled-gkr-proof-entry)
to the compiled GKR `example::Proof` verifier through the generated transform of
the admitted original and the reading of the original's verifier normal form as
the plain verifier.

`FiatShamir/Upstream` imports ArkLib's
[worst-case round-by-round soundness](../../docs/spec/fiat-shamir-security.md#imports-from-arklibs-round-by-round-soundness)
of a verifier with a guarded verdict as a typed certificate of the verifier's
process form, each challenge round charged its own error, with weighted and
uniform bounds for fixed and adaptively chosen inputs. `FiatShamir/Realization`
transports such a certificate to a participant validator that realizes the
process form, and `Examples/CompiledGuessFiatShamir` uses it to bound the
compiled verifier of the construction bridge's guessing fixture by a worst-case
round-by-round proof stated in ArkLib's framework (written for the example); a
query-free prover attains the bound.

`FiatShamir/Laws` states law records of decoded query sites, with five
constructors and the gated accepted-value decoder; `FiatShamir/Lifting` raw
answers by the last event and the lifting of uniform-sort certificates to typed
certificates; and `FiatShamir/Binding` binding codecs over typed public-value
binding events, which discharge statement determination, and statement
bindings from policy statements to model statements, with the coverage of the
application's false statements and the rejection of unmapped statements as
separate registered obligations.
`FiatShamir/Obligations` states formal readings of the
[construction obligations](../../docs/spec/fiat-shamir-security.md#construction-obligations),
which the model counterexamples of `TestsSecurity.Counterexamples` refute one by
one, and `FiatShamir/ProviderSimulation` the type of a provider simulation with
its query-cost relation.

`HashChain` instantiates that type for the native hash-chain suites
([provider simulations](../../docs/spec/fiat-shamir-security.md#provider-simulations)).
`Model` is the chain over an abstract hash with full-digest states. `Simulator`,
`Steps` and `Reduction` couple the concrete experiment with a lazily sampling
simulator over the history oracle until a collision or prediction in the joint
primitive-query trace, whose probability `Bound` bounds by `(q + V)² / |S|`.
`Provider` and `Bridge` give the simulator with a private tape and its law,
`Instance` the simulation and its composition with the typed engine, and
`Encoding` and `Bytes` the injective, prefix-free byte framing and the transfer
to a byte hash. `VCVio/UntilBad` (identical until bad, for two simulations with
different states) and `VCVio/Deferral` (deferred sampling) supply the coupling
and the law. These theorems are about the construction's byte-level chain
model; that the compiled transcript handlers and the installed Keccak-256
kernels implement it remains an obligation.

`ArkLib/Fri` models the verifier of the FRI library's low-degree test with
ideal commitments and proves its completeness and
[round-by-round soundness](../../docs/spec/fri-security.md). `Protocol`
transcribes the verifier, the prover's moves and the sequential position draws;
`Correspondence` shows that its acceptance is ArkLib's FRI query acceptance on the
committed trace; `Completeness` shows that the honest prover is accepted on every
codeword; `Soundness` states the certificate, with the proximity premise as a
named hypothesis, and bounds acceptance for every adaptive prover;
`UniqueDecoding` discharges the premise with ArkLib's proved unique-decoding
results; `GeneralizedJohnson` discharges the folding obligations with ArkLib's
generalized Johnson folding bound for lines up to the cube-root radius
`1 - (ρ + η)^(1/3)`, inside the Johnson radius `1 - ρ^(1/2)`; and
`Certificate` restates the certificate over the verifier's residual
processes after the first commitment, with an error per query site.
`Examples/FriFiatShamir` presents that verifier through a typed transcript
interface, with a block sampler for the query positions, and applies
`FiatShamir/Typed` for a
[Fiat–Shamir bound](../../docs/spec/fri-security.md#fiatshamir-transfer)
with commitments read in the clear. These modules
use the per-round lemmas of ArkLib pull request #992, which this package applies
to its pinned ArkLib revision as a declared, hashed patch
([`compatibility.json`](compatibility.json); see the
[dependency baseline](../../docs/dependencies.md)) until the pull request merges
upstream. Preparation applies it; the patch names its upstream source and keeps
ArkLib's Apache 2.0 file headers.

`Commitment` bounds verifiers that see roots and openings instead of committed
tables by the typed certificate of their ideal reading, in one random oracle
shared by the transcript keys and the hash calls
([verifiers with committed tables](../../docs/spec/fiat-shamir-security.md#verifiers-with-committed-tables)):
`Verifier` states the verifiers and their ideal and concrete readings,
`Extractable` the two laws of a straight-line extractor, `Merkle` and
`HashedLeaves` Merkle trees with raw and with hashed leaves as extractable
schemes, `Record` the good records of hash calls, `Replay` and `Escape` the
deterministic run of an accepting verifier, `Experiment` the joint experiment and
its bad keys, and `Soundness` the bound. `Examples/CommittedOpeningBound` proves
the committed-opening experiment's intended bound, and
`Examples/CommittedOpeningBridge` applies the general bound to the same
verifier. `Cost` charges the concrete reading by the charges on the verifier's
paths, and `Examples/CommittedFri` applies the bound to the FRI verifier with
committed words ([committed words](../../docs/spec/fri-security.md#committed-words)),
for acceptance together with a far initial word extracted at a verifier
checkpoint and completed with zero, with one field element per hashed leaf.

The shared interfaces connect these results through one probabilistic endpoint
and one composition rule. `FiatShamir/Keyed` states keyed bad-event
certificates over any key space of VCVio's lazily sampled oracle, with an
all-table resampling obligation and a trace obligation; its soundness theorem is
the endpoint, which typed certificates and the commitment bridge reach through
transformers. `FiatShamir/Reduction` states charged reductions, sub-validators
whose returned values satisfy a postcondition, composed by bind, bounded
repetition, union and receive; certificates of every other form become
reductions through the charged certificate. `FiatShamir/Budget` reads the typed
engine's query count, cost per occurrence and charged cost as path bounds of one
walk combinator, with conversions between the metrics. `Oracle/Keys` transports
executions, query bounds and weighted costs between oracle key forms through
renamings of cells, and `Commitment/HistoryKeys` applies it to the commitment
bridge's joint keys and history keys, checkpoints included.

`Stage/Relation` states quantitative stage relations between attack games:
composition transports budgets before evaluating the earlier stage's loss, and
a bound is against the worst adversary in a translation's support.
`Stage/FiatShamir`, `Stage/Provider` and `Stage/Commitment` state the
construction, projection and pruning equalities, the typed theorem, provider
simulations and the commitment bridge as stages. `Stage/Joint` states the
contract of a commitment and a transcript provider that share one primitive:
jointly injective namespaces, a checkpoint extraction that reads only the log
before a key's first query, the checkpoint event, and an implication from the
intended application event. Its frame records a provider simulation with the
obligations of a joint provider theorem: the simulator's namespaces, hash
answers through a fixed range equivalence, a provider-state projection that no
hash answer reaches at any later call, and a loss over the joint trace. The
contract composes. `VCVio/Memo` and `Commitment/Repeats` show that a simulator's
memoization of repeated calls does not change the bridge's event for extractors
that read through first matches. A frame is constructed for a tagged provider
whose tags are the joint key's summands (`TestsSecurity.JointSimulation`).
`HashChain/Joint*` constructs the frame of the hash-chain provider with the
commitment's row calls passed through on one byte hash, and bounds the abstract
committed-opening verifier over the Keccak-256 hash chain with byte tags
(`ZkcSecurity.HashChain.Joint.keccak_soundness`); no compiled Entry or native
transcript reading is connected to it.

`Endpoint/*` states the registered
[endpoints over artifact-indexed evidence](../../docs/spec/fiat-shamir-security.md#endpoints-over-artifact-indexed-evidence).
`Endpoint/Compiled` collects a compiled Entry's generated facts and states its
compiled verifier as the transform of the admitted original on every statement
of the published types. `Endpoint/Evidence` adds the model equation, the
family's charged certificate, the original validator's charge, binding evidence
that adaptive claims require (the policy-derived codec of `Endpoint/Binding`
and coverage of the application's false statements) and lowering evidence that
claims about program bytes require. `Endpoint/Soundness` proves ordinary
soundness for fixed and adaptive statements, ideal meaning and program bytes,
each as one composition of stage relations. `Endpoint/Sigma` is the generic
Sigma bridge and `Endpoint/Knowledge` gives fixed-statement knowledge soundness
for both endpoints. `Families/Schnorr` is the Schnorr family package over any
checked context and `Families/SchnorrVariants` the Chaum–Pedersen, two-proof
AND and Okamoto family packages; family packages import no compiled Entry.
`Examples/Subjects/<subject>` holds each subject's claim: a hand `Contract`
recovered from the admitted original's retained contract, a hand `Evidence`
applying the family package, and the driver-generated `Artifacts` and `Claims`
modules, whose applications the assurance reports check.
`TestsSecurity.Endpoints` relates the subjects' evidence to the earlier compiled
theorems and holds the Lean controls
([support](../../docs/support.md#endpoint-applications)).

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
