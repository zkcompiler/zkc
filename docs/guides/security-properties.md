# Protocol properties and their premises

A protocol property concerns an interpreted experiment, not an operation name
or a returned Boolean. This guide connects [property schemas](#protocol-properties),
[conditional evidence](#judgments-premises-and-use),
[probability laws](#probability-initialization-and-persistent-providers), and
[reductions with terminal verification](#relation-bearing-results-and-terminal-verification).

## Protocol properties

The [experiment specification](../spec/properties/experiments.md) owns experiment
subjects, quantifiers and transport; [relations](../spec/properties/relations.md)
owns reductions and terminal contracts. [Probability](../spec/properties/probability.md),
[disclosure](../spec/properties/disclosure.md) and [continuations](../spec/profiles/services/accepted-continuations.md)
complete those contracts. This chapter explains their use; the
[correspondence](../spec/correspondence/properties.md) gives their Formal scope.
A preserved property is claimed [for a stated observer](../rationale/target-contexts.md),
and a requested claim is [carried as its named experiment](../rationale/claim-scope.md).

A property is attached to an actual interpreted experiment: source, public
statement mapping, strategies and their information, joint initialization,
interaction, observer, conclusion and assumptions. A field name or source digest
cannot replace those operands. Backend implementation trust and cryptographic
assumptions are different parts of the argument.

### Property schemas

[PROP-01–02](../spec/properties/experiments.md#experiment-operands) distinguish
honest completeness, false-statement soundness, simulation-based zero knowledge
and extraction-based knowledge. Setup, auxiliary input, adaptivity, resource
limits and quantifier order belong to the selected experiment. The schema is
not a claim that the Lean package implements a universal framework for all four.
An adaptive statement experiment must include its selection step.

### What a compiler relation transports

[PROP-03–04](../spec/properties/experiments.md#observation-based-transport) require
compatible initialization and contexts and an event determined by the preserved
observation. A protocol-changing pass may need a strategy map, a reduction and
loss. A common reply-adaptive source law is narrower than linking arbitrary
hostile target code. Released artifacts also belong to the observation.

The [Sumcheck application](../../formal/Zkc/Protocols/Sumcheck/Security.lean)
proves ordinary interactive soundness and perfect completeness for its fixed
per-coordinate-degree-two polynomial. Its independent uniform tape and prover
information premises are explicit. The
[checked optimization](../../formal/Zkc/Protocols/Sumcheck/Optimization.lean)
uses actual received coefficients and challenge, and transports properties by
complete verifier equality. The
[table-source entry](../../formal/Zkc/Protocols/Sumcheck/TableSource.lean) adds
successful ordered-expression compilation and the original table-sum premise.
[PROP-07](../spec/profiles/sumcheck/interactive.md#complete-verifier-source) states
these limits, including the separate private-seed mixture.

The [framed profile](../../formal/Zkc/Protocols/Sumcheck/Framed.lean) binds the
statement and preserves actual query prefixes and arithmetic optimization.
[PROP-08](../spec/profiles/sumcheck/framing.md#typed-framing-and-construction-phases) explains
why that does not establish Fiat–Shamir security. Product-provider `2ε` and
correlated-service observation laws likewise retain their own subjects.

[Protocol maps](protocols.md) distinguish expression, mathematical,
wire and native coverage. The [security companion](../roadmap.md#4-the-security-companion)
connects one complete source/property/checked-transformation application to the
next native delivery. Its formal example exists; an optimized native artifact
and its correspondence remain implementation work.

## Judgments, premises and use

The normative [evidence judgment specification](../spec/verification/judgments.md)
owns conditional evidence, checking outcomes and caller requirements. This
guide explains how those judgments are used with actual subjects.

### 1. Conditional evidence

[JUD-01](../spec/verification/judgments.md#conditional-evidence)
requires propositions on the actual interpreted context. The
[Formal interface](../../formal/Zkc/Properties/Judgment.lean) retains both
producer and transport requirements. A proof at one source/input binding does
not automatically rebind to another with the same label.

[Local-code admission](../../formal/Zkc/Protocols/Sumcheck/LocalProver/Admission.lean)
joins source input checking with an actual handler relation and related
initial states. The source check produces the admitted body for the retained
input vector, while the handler/state requirements remain explicit.

### 2. Logical judgment and implementation trust

[JUD-02](../spec/verification/judgments.md#evidence-bearing-check-results) distinguishes
established, refuted and unknown evidence.
[JUD-03](../spec/verification/judgments.md#failure-boundaries)
separates decoding, unsupported meaning, resource limits, implementation
failure and actual protocol stops. A checker timeout is not a negative proof,
and a native process death is not automatically a returned verifier outcome.

A logical theorem, a correctly implemented checker, a correctly bound runtime
adapter and a cryptographic assumption contribute different evidence. The
[assurance map](../assurance.md) keeps those contributions visible.

### 3. Caller requirements and quantitative conclusions

[JUD-04](../spec/verification/judgments.md#caller-requirements)
separates a legal transformation from a usable one. Comparing upper bounds
alone cannot compare actual costs. The
[preparation law](../spec/profiles/compiler/factor-preparation.md#immutable-preparation-and-prices)
gives an exact criterion under supplied price functions, rather than a native
speedup conclusion. Optimality requires a defined comparison domain and
coverage of unresolved alternatives.

### 4. Theory and scope

Rationale records explain [semantic framing](../rationale/semantic-footprints.md)
and [candidate checking](../rationale/candidate-checking.md); conservative analysis
follows the [merge condition](../spec/verification/analysis.md#merging-descriptions). Additional proof
search or constraint solvers can produce evidence for the same judgment.
The [correspondence](../spec/correspondence/transformations.md) lists
current laws and negative controls; it claims no universal decision procedure.

## Probability, initialization and persistent providers

The [probability specification](../spec/properties/probability.md) owns the common
contracts; the [product-tape](../spec/profiles/providers/product-tapes.md) and
[correlated-service](../spec/profiles/README.md#service-components) profiles fix their instances.
This guide explains the actual product and correlated-source applications.
[Correspondence](../spec/correspondence/properties.md) separates root
proofs, optional ArkLib consumers and native assumptions.

### 1. Kernels over complete results

[PROB-01–02](../spec/properties/probability.md#normalized-discrete-distributions)
retain stopped outcomes, residual state and events under one joint initialization.
The generic monad supplies sequencing; a PMF supplies normalized nonnegative
mass. Rational finite calculations need those conditions when interpreted as
probabilities. Failure runs are not discarded or renormalized implicitly.

### 2. Reached views and conditional bounds

[PROB-03–04](../spec/properties/probability.md#reached-views-and-finite-masses) use the
full strategy information before the draw and mix hidden states by their actual
posterior. A selected finite bad set inherits a cardinality-times-point-cap
bound. Positive view mass is required for division; conditioning on eventual
success is a different experiment.

For independent uniform bits `S,R`, the disclosure `T = S XOR R` leaves `R`
uniform given `S` alone or `T` alone, but determines it given `(S,T)`. This is
why separate marginal facts do not establish a full-view law. Nor should a
useful tape law demand randomness after fixing every exact deterministic seed.

### 3. The proved product-provider interpretation

[PROB-05](../spec/profiles/providers/product-tapes.md#interface-and-product-initialization) relates a
persistent sampled suffix to online sampling plus reconstruction of its residual
suffix. The [actual theorem](../../formal/Zkc/Probability/ProductTape.lean)
covers every finite reply-adaptive source, tape length and local probabilistic
handler without future-tape access. Arbitrary local/setup initialization and
source selection are allowed with the stated conditional product law.

The [conditional laws](../../formal/Zkc/Probability/ConditionalTape.lean) use
a recoverable checkpoint containing the complete local result and suffix length.
The next returned-point numerator is view mass times `q(d)` on requesting
nonempty fibers and zero otherwise. The law is about the actual retained state;
no fresh independence assumption is inserted per request.

### 4. Source and acceptance consumer

[PROB-06](../spec/profiles/providers/product-tapes.md#actual-next-request-decision)
connects the optional [local-code provider](../../formal/integrations/arklib/ZkcArkLib/LocalProver/Provider.lean)
to its committed quadratic message, actual next draw and reduction against
`2r`. A false claim, injective finite challenge domain and point cap `ε` yield
the stated `2ε` bound. The guarded source requests only for committed cuts;
local abort and exhaustion cannot become acceptance or justify conditioning.

This proof includes source, provider, request and terminal consumption. It
still concerns its selected mathematical law, not a native entropy source,
PRG, hash transcript or arbitrary complete Sumcheck instance.

### 5. Correlated setup is a different law

[PROB-07](../spec/profiles/services/affine.md#joint-service-coupling-and-its-observer)
retains one issued source and captured setup, its `Good` condition and the
publication/history observer. The
[actual source law](../../formal/Zkc/Protocols/CapturedPrograms/Probability.lean)
transports the affine service coupling. The root
[selection laws](../../formal/Zkc/Protocols/CapturedPrograms/Selection.lean)
require actual environment agreement and connect selected code/captures to the
service mass. A witness-dependent setup tag or code selection is not justified
by `Good` alone.

This coupling does not turn correlated resources into independently fresh
ones. Repeated bits, urn depletion, joint XOR disclosure and postselection
controls distinguish the relevant assumptions.

### 6. Theory use and extension boundary

[PROB-08](../spec/properties/probability.md#attempts-and-extensions)
requires the actual enclosing experiment for retries and the appropriate laws
for computational or oracle-model claims. The [randomized release law](../../formal/Zkc/Probability/Disclosure.lean)
uses [one coupling of the whole released pair](../rationale/joint-release-coupling.md); it does not confer
ZK on a protocol or verify its native implementation.

## Relation-bearing results and terminal verification

[PROP-05–06](../spec/properties/relations.md#relation-families-and-instances)
own statement, reduction and actual terminal contracts. This guide explains why
a returned scalar or finished phase still needs its bound terminal consumer.

### 1. Relation instances and actual operands

A [relation family](../../formal/Zkc/Semantics/Relation.lean) has statement and
witness types and a satisfaction predicate. Validity means a witness exists.
Its application binds actual public values, domain and setup interpretations.
A residual result additionally carries its input/residual/terminal connection.
Factor order, challenge prefix, suite and source context matter where used;
a same-typed handle cannot reconstruct them.

### 2. Reduction and terminal contracts

The soundness-direction implication is `residual(result) → input(source) ∨ bad`.
Composition retains exceptional events at the actual intermediate instance.
A separate experiment bounds their probability. Completeness and extraction
have different obligations.

The terminal law applies to the actual verifier and the same residual predicate.
`scalarTerminal target actual` checks their equality. A complete scalar argument
must additionally connect the target to the bound original polynomial and actual
point. [The full Sumcheck/table-source profile](../spec/profiles/sumcheck/interactive.md#complete-verifier-source)
supplies that connection within its declared subset.

### 3. Discriminating cases

Over the field of order 5, a false sum claim 1 for the zero polynomial and
constant round polynomial 3 pass the boundary `3+3=1`. The round may finish
with scalar 3, but comparison with zero rejects. The
[actual terminal controls](../../formal/Tests/Integration.lean) distinguish
these cases. This identifies the deliberately missing terminal premise; it does
not attack a complete protocol that includes the check.

### 4. Scope and theory

Exceptional-event composition is useful for reductions and terminal checks;
ordinary arithmetic modules need not become claim graphs. [Property experiments](#protocol-properties)
supply probabilistic meaning and [authorized continuations](../spec/profiles/services/accepted-continuations.md)
supply live use authority. No universal linear graph, extractor or global
last-challenge ordering rule follows from this local contract.
