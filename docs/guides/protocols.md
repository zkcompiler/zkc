# Contrasting protocol interpretations

These six protocol contrasts exercise different semantic boundaries. They
distinguish maintained formal clients and native examples from illustrative
obligations; a family discussed here is not automatically implemented. The
[specification](../spec/README.md) owns common requirements; [PIR](protocol-model.md),
[Properties](security-properties.md) and [Realization](realization.md)
explain their use.

Short explanatory notes may stay beside a specification clause. A substantial
protocol interpretation lives here, with its incomplete adapters and security
obligations visible. An adopted normative protocol format or acceptance rule
lives in its specification, and the walkthrough cites it.

Additional [typed Sigma](../../formal/Tests/ProtocolGenerality/Sigma.lean) and
[public-height Merkle](../../formal/Tests/ProtocolGenerality/Merkle.lean) clients
check distinct scalar/group sorts, interaction order, retained logical path
operations, selective interpretation and complete execution. They include wrong
operand/root/coordinate and failed-node controls. Their role is abstraction and
algorithm validation; they add no extraction, binding or FRI security claim.

## 1. Scalar rounds and factor consumers

`AlgebraicRounds.EarlySource.source evaluate n claim` is a uniform finite source. The prover
supplies an arbitrary coefficient tuple. The verifier checks its boundary before
requesting a challenge. The handler retains prover and provider state; `send`
sees only prover memory, `react` additionally sees the delivered challenge,
and `draw` owns the provider state. Honest arithmetic is not a restriction on
received interface-valid messages.

The operations are message, challenge and rejection notification. Public `n`
supplies the call bound. A return is a residual scalar, whose use must retain
the original statement, factor/polynomial identity, variable order and delivered
point prefix. A next GKR layer or terminal polynomial check needs that relation
binding. The scalar alone is not an acceptance certificate.

[Rounds](../../formal/Zkc/Protocols/AlgebraicRounds/EarlySource.lean) proves conformance, the `2*n` bound
and exact execution against the early-stop interpreter for all supplied
endpoints. [Analysis](../../formal/Zkc/Compiler/FactorExecution.lean) and
[Mixed](../../formal/Zkc/Polynomial/Bilinear/Execution.lean) prove the actual factor/state/cache
compiler join. [SourceProvider](../../formal/integrations/arklib/ZkcArkLib/LocalProver/Provider.lean)
connects a selected false scalar verdict to the product-provider law.
[Relation](../../formal/Zkc/Semantics/Relation.lean) makes the terminal predicate
explicit. Those scalar results are not full protocol-security proofs.

The [table-expression specification](../spec/domains/polynomials.md) fixes actual cell
order, extension semantics and repeated factors. Its maintained
[table entry](../../formal/Zkc/Protocols/Sumcheck/TableSource.lean) compiles the
selected degree-two subset and connects the original expression to complete
checked execution, terminal evaluation and the false-statement premise.
The source meaning permits longer products; this compiler profile refuses
them before interaction. Dense coefficients are a reference bridge, not a
required native table layout.

The maintained [Sumcheck source](../../formal/Zkc/Protocols/Sumcheck/Source.lean)
adds an actual fixed polynomial input, ordered delivered challenges and terminal
evaluation. [Security](../../formal/Zkc/Protocols/Sumcheck/Security.lean) proves
perfect completeness and ordinary interactive soundness at most `2*n/card F`
for per-coordinate degree at most two over any finite field, with independent
uniform challenges in that field. The prover chooses
each message before its challenge; its private state is fixed independently of
the verifier tape. An additional theorem covers independent uniform finite private seeds.
[Optimization](../../formal/Zkc/Protocols/Sumcheck/Optimization.lean) runs the
checked Horner plan on the actual message coefficients and challenge, preserving
the complete verifier execution and transporting those properties. This does
not establish GKR, zero knowledge, extraction or Fiat–Shamir security.

## 2. FRI and Merkle openings

FRI queries combine a low-degree reduction with authenticated openings. Public
configuration fixes the field/domain, tree/path shape, codecs and primitive
interpretation. An opening binds the actual root, query coordinate, ordered path
and remaining input. Leaf and node operations consume their ordered inputs;
a coordinate cache hit cannot substitute for the root/path predicate.

The maintained [AIR/oracle examples](../../examples/protocols/air-oracle/README.md)
use explicit extension-field traces, FRI and authenticated queries. Their native
and reference evidence has the bounds stated there. A full emitted-FRI-to-`Proc`
or SSA-to-Rust theorem is not supplied by a local cache law.

The local cache relation stores only results for exact ordered primitive
inputs. It preserves logical requests and the selected result/event observation;
the cache state can differ while remaining valid. Byte cursor, malformed-input
failure, transcript order and challenge derivation remain source/adapter
obligations. A full emitted-FRI-to-`Proc` or SSA-to-Rust theorem is not supplied
by the local cache proof.

A useful cache benchmark compares the same verifier, wire language and query
algorithm with and without reuse, using the same optimized hash primitives.
It must report table storage as well as time. An upstream pruned-multiproof
verifier is a different algorithmic baseline and must be identified separately;
see the [benchmark guide](../../bench/README.md) for maintained campaigns.

Lossless outer encoding and pruned-proof reconstruction are separate
representation changes. Pruning can erase inconsistent redundant digests that
a full-wire verifier rejects, so it cannot inherit equality on arbitrary hostile
full wires from honest reconstruction.

## 3. ZKBoo and virtual views

A ZKBoo-style Boolean protocol can have one physical prover and verifier. Three virtual
party records are data within the prover computation, not three runtime network
roles. The circuit/statement and first message are fixed before the challenge
selects two ordered openings.

The interpretation receives first-message bytes, derives/receives a challenge
in its declared domain, and receives selected opening bytes. Decoding checks
lengths, bits, party order and circuit identity. Commitment checks bind opened
views to the first message; directed local-gate checks inspect the chosen
party's equations and successor inputs. Hostile interface-valid views are not
assumed globally honest or reconstructible from a witness.

Static check specialization must preserve verdict, failure phase and consumed
bytes for the same circuit, statement, first message, challenge and response.
Pure expression reuse may preserve occurrence-specific masks. Reusing a sampled
share or omitting an opening instead needs a joint-view/representation law.
Unopened virtual state remains private to the stated observer.

A finite native assessment and faulty-lowering controls would test a particular
compiler, not prove correctness for all circuits. An unsalted commitment to a
small-domain view can be enumerated, so an ideal view-simulation argument cannot
establish privacy of those concrete first-message bytes. This contrast motivates
the distinction between virtual data, physical roles, local checking and
concrete disclosure; it does not claim a maintained native ZKBoo implementation.

## 4. QuickSilver-derived setup/session service

The source here is the maintained captured-program setup/session service, with
its own stated scope rather than full QuickSilver security. A controller selects
`(star, challenge, cutAfterU)` from
fixed source, setup-authorized captures, publication and earlier permitted
history. The responder owns witness-dependent computation and the residual tape;
setup retains its original correlations.

A cut request returns only `U`; a full request returns `(U,V,tag)`. The cut is
selected before that response. Delivered values update history. Client stop
consumes no coordinate; exhausted tape is an outer stop for this client. A
returned history is service completion, not a proof acceptance judgment.
Interaction between `U` and `V` would require a different operation boundary.

[Installed](../../formal/Zkc/Protocols/CapturedPrograms/Inputs.lean) connects actual roles/inputs
and source issuance. [Services](../../formal/Zkc/Protocols/CapturedPrograms/Execution.lean) proves
exact common execution and retained history.
[ServiceProbability](../../formal/Zkc/Protocols/CapturedPrograms/Probability.lean)
transports the existing correlated setup/session mass law at its publication/
history observer. [Communication](../../formal/Zkc/Protocols/CorrelatedSetup/Communication.lean)
proves source-controller/library equality and complete cache execution for
arbitrary finite clients, including exhaustion. That stronger deterministic
state relation does not enlarge the privacy observer of the probability law.

This case checks that correlated resources, partial delivery and persistent
history fit the same execution model without pretending their laws are those
of independent product draws.

## 5. KZG opening transformations

One program checks two
individual opening proof slots. Another
fixes commitments, a common point and claimed values, derives `gamma`,
then receives one aggregate proof. This changes the interaction and challenge
order, so it is a protocol/property transformation. Optimizing a pairing
implementation is a different, potentially local transformation.

The interpretation binds SRS/suite, decoded field/group values, ordered member
descriptors, transcript point, aggregate proof and opening predicate. Pairing
success means that predicate under its arithmetic laws. Binding, knowledge,
fork collection, extractor efficiency and reduction loss remain distinct.
An accepting-fork decoder does not itself collect the forks or prove the
original witness claim.

For a field order that does not divide `2^256`, reducing a uniform 256-bit
digest modulo that order gives a biased pushforward. The selected property must use that actual distribution or a justified
bound. An informal "uniform" comment is not a probability proof. No new KZG attack is
claimed.

## 6. Accepted continuation and finite recurrence

The common [continuation](accepted-continuations.md) can consume a result of a
source-bound terminal interpretation. The mathematical atomic adapter joins
the actual source, installed authorization policy, fresh target, retained
decision, isolated consumption and no authorized export after arm failure.
It does not turn an arbitrary Boolean or receipt into an accepted relation.

Folding and recurrence expose different terminal objects: a folded witness,
a final random challenge, primary/companion checks or multiple decomposition
exports. The continuation interface must retain whichever object its actual
consumer needs. Naming a folding family does not supply a verified compiler
or establish that one atomic export covers its full interaction.

A folding/IVC property additionally connects the relation across steps and
justifies its security/adversary model. Multi-export custody, transferable
capabilities and native persistence need their own concrete adapters if exposed.
The selected single-export atomic law is complete at its stated interface;
those richer properties do not follow from it.

## 7. What the contrasts establish

The cases separate arithmetic from stateful communication, physical roles from
virtual views, independent draws from correlated setup, value computation from
claim reduction, local caching from wire changes, and terminal acceptance from
continuation completion. Common execution/contract/refinement infrastructure
applies across these boundaries with different premises. The purpose is to
test that abstraction, not to tailor the entire compiler to a small protocol.

Another family is useful when it exposes an unsupported construct or law;
the [research backlog](../roadmap.md#3-research-triggers) records those triggers.
