# A standalone protocol-proof framework

This package implements a top-level proof framework before connecting it to zkc's compiler or
existing execution model. Its acceptance object is a proved claim about a complete model game,
assembled from local facts. It does not certify an existing `.zkc` artifact.

## The proof structure

```text
Fixed request about a complete experiment
└─ UpperEvidence.establish / LowerEvidence.establish
   ├─ Subject binding: the request denotes this fixed system and client
   ├─ Connection: local operation couplings + initial-state coverage
   │  └─ VCVio's universal adaptive-client substitution theorem
   ├─ Mathematics: composed upper/lower contract + initial budget
   │  ├─ operation specifications and their local validity
   │  ├─ bind / branch / finite iteration / component substitution
   │  └─ mathematical invariants and terminal facts
   └─ Observation transport: actual bad ⇒ model bad,
      or model acceptance ⇒ actual acceptance

Optional security transformation
└─ a separately proved game reduction, explicit environment translation and loss
```

This is a dependency graph, not four sequential compiler phases. A component theorem can be
used many times; the same exact connection supports completeness and soundness. A mathematical
model may be proposed by automation, imported from another library, or written in a companion.
Its origin does not change any proof obligation.

## One execution and several judgments

The execution carrier is upstream `PFunctor.FreeM`. Its typed operation interface specifies
which operations exist and each operation's answer type. Arguments are part of the operation.
Ordinary Lean continuations express adaptive control and branches; finite iteration is ordinary
monadic iteration. We introduce no new protocol AST and no second interpreter.

The probability meaning is VCVio's `PFunctor.FreeM.runKernel`. An operation maps private state
to a *joint* law of answer and successor state. All calls share the threaded state. Sampling an
answer and sampling a state independently is a different kernel. Different service names do
not imply independence. The privileged semantic state is not automatically visible to an
adversary: a client/system instantiation supplies an adversary only the interface it is allowed
to observe. In the adaptive test the strategy sees only earlier challenge answers.

`System` adds normalized operation kernels and a normalized initial law. Its `experiment`
constructor proves that every complete client has mass one. Explicit rejection and abort are
ordinary observable terminal values. The lower-level contract theorems also apply to
subprobability kernels, but the request-facing complete experiments cannot silently lose mass.

There are three different judgments:

- **Installation:** exact joint-law coupling, with a relation on hidden state and common
  interface answers. It accounts for all outputs and has no security error budget.
- **Mathematical contract:** an upper or lower expected terminal potential. It can describe a
  bad event, residual obligation, iteration invariant, or a successful outcome. It is not
  restricted to equality tests or a protocol-family tag.
- **Game transfer:** a proved change of the security experiment/admissible environment with an
  explicit loss. It is not an extra instruction in the execution interpreter.

Upper and lower contracts are separate because the implication directions differ. Canonical
property meanings are separately typed: promise soundness, honest completeness, fixed recovery,
bounded extraction, statistical simulation, and selected-observer simulation. Their detailed
quantifiers and resource boundaries are in [CLAIMS.md](CLAIMS.md). They share execution and
mathematical proof infrastructure without pretending to be the same property.

## The common construction path

`opExpectation` interprets one operation as a transformer of continuation potentials.
PolyFun's existing `wpFold` extends it over the existing client. The new theorem
`wpFold_eq_runExpectation_of_measurable` proves that this fold equals the expectation of
VCVio's kernel execution. It supports measurable state and outputs; the convenient unrestricted
assertion specialization uses countable state/output spaces.

`UpperBound` and `LowerBound` are propositions over that fold. Their bind rules pass the
*reached* answer and state to the continuation. Their finite-iteration rules accept one
iteration-, accumulator-, and state-indexed invariant and one body theorem. Nested iteration
is a body instance of the same rule. Proofs use ordinary Lean theorem applications, not an
unverified collection of selected paths. The local-to-global adequacy theorems prove the
probability bounds from individual operation specifications.

For exact connections, VCVio already provides `KernelHandler.CouplingContract` and
`bind_state_laws`. The latter constructs a whole-client coupling from local joint kernels and
an initial coupling, for every adaptive client. We reuse it and prove event/expectation
transport corollaries. `freeHandler` installs an entire proved implementation as a component at
the next interface. Thus a component may consist of many calls or loops; protocol names never
occur in the common engine.

`Representation.contractOfMap` proves the coupling obligations for a total state map from one
local commutation law per operation. The map need not be injective. `Connection.ofMap` also
proves root coverage from the pushforward of the entire actual initial law.
`Connection.reflexive` handles an unchanged representation without an authored connection.

The common-answer interface is a substantive boundary: a runtime parser, polynomial encoding,
or answer decoder must first prove its full answer-and-state meaning, including failure. We
have not claimed that deleting an output field or matching a function name supplies this law.
A state map may erase a log only when the local operation laws and the requested observation
both permit it. A later call that reads an erased log invalidates the local law.

## Requests and assumptions

`Experiment`, each request's admissibility, its relation, observation and budget are fixed
before constructing evidence. `SoundnessRequest` computes negative-instance acceptance from
its output-selected statement and its fixed `PromiseProblem`. Positive and negative regions
are disjoint but need not exhaust all statements. Ordinary relation soundness uses
`PromiseProblem.ofPredicate`. A `WitnessRelation` optionally connects returned witnesses to
positive instances. `CompletenessRequest` computes the unconditional lower accepting-mass
claim `1 - error`; its admitted environments select the honest strategies and valid inputs.
The generic `UpperRequest`/`LowerRequest` remain mathematical reasoning interfaces beneath the
property-specific meanings.

Evidence is indexed by the request. It cannot replace the event, recovery algorithm, simulator
quantifier order, experiment or numerical budget. Assumptions appear as explicit theorem
premises or request-side admissibility conditions. The framework does not infer that an
arbitrary chosen relation or contradictory assumption expresses the user's intention.
Accepted examples therefore instantiate nonempty admission and nontrivial numerical bounds;
negative controls test specific weakened meanings.

`UpperTransfer` is statistical game transport. An efficient cryptographic reduction requires an
additional explicit computational model and resource theorem; a Lean function type alone does
not establish efficient extraction or an admissible reset interface. Such a theorem belongs in
a security-method library and can feed the fixed request boundary. Classical choice in a
mathematical proof is not an executable recovery algorithm.

## Authoring boundary

| Work | Owner | Reuse unit |
| --- | --- | --- |
| Typed execution/handler interpretation and normalization | Foundation | Every client |
| Structural substitution and exact installation | Foundation/upstream | Every client of the interface |
| Quantitative bind, branch and loop composition | Foundation/upstream | Every component contract |
| Raw representation-to-mathematical meaning | Component library or companion | Representation/interface pair |
| Polynomial root bound, proximity lemma, special soundness, residual algebra | Mathematical library or companion | Mathematical component/family |
| Loop invariant and meaningful state relation | Companion, often parameterized | Reusable mathematical pattern |
| Instance parameters and theorem selection | Author/tooling | Instance |
| Actual compiler subject binding | Future compiler adapter | Shared construction path, not ordinary companion plumbing |

No model companion traverses `FreeM` to re-prove the universal installation theorem. Some model
proofs induct on a *mathematical round count* or prove a state invariant; that is a mathematical
argument. Automatic structural application does not discover arbitrary invariants, representation
relations, or new cryptographic theorems. An automation engine can propose those and apply these
same checked rules later, without defining another security meaning.

## Why this architecture

[Abstract Cryptography](https://crypto.ethz.ch/publications/files/MauRen11.pdf) supports starting
with composition interfaces and then establishing concrete instances. We use that design
method, without asserting UC security from a kernel contract.

[Dijkstra Monads for All](https://arxiv.org/abs/1903.01237) motivates separating computation from
its specification interpretation. Here the actual connection is a proved equality between an
existing specification fold and an existing kernel interpretation, not an assumed abstract law.

[SSProve](https://github.com/SSProve/ssprove/blob/main/DOC.md) separates package composition and
relational reasoning about component implementations. Our common-answer local coupling is a
concrete Lean instance of this separation, with request-facing claim closure added above it.

The selected [VCVio kernel contracts](https://github.com/Verified-zkEVM/VCVio/blob/96754a37e739270ac5bb8fe7deaeafef6964b688/VCVio/ProgramLogic/Relational/KernelHandler.lean)
and [PolyFun specification fold](https://github.com/Verified-zkEVM/PolyFun/blob/a5edfe2dd24d9d76f9a13cc1f131b220617ad534/PolyFun/PFunctor/Free/WP.lean)
are reused as code, rather than credited only as inspiration. Their pinned sources and the new
proofs are checked by the same Lean package. No new theorem is claimed merely because an
existing library already has the appropriate interface.

A separate typed proof AST was considered and rejected for this package. Lean theorem terms
already share checked lemmas. A certificate format should be added only for a concrete tooling
need; it should index the existing client and fixed request, never supply another evaluator.
A new PMF-only interpreter was also rejected in favor of the existing kernel semantics.

## Protocol stress matrix

| Intended family | Shared framework | Mathematics or semantics not supplied by the framework |
| --- | --- | --- |
| Multi-round Sumcheck | dependent replies, finite iteration, residual potential, exact installation | degree bounds, root counting under actual sampling, residual invariant, terminal relation |
| FRI / proximity testing | stateful oracle calls, potential contracts, proximity bad event, hierarchy | proximity theorem, domain/sampling assumptions, folding relation; Merkle/PCS realization is a separate security step |
| Nested GKR | component installation, nested iteration, shared state | layer evaluation and reduction invariant, Sumcheck contract instantiation |
| Schnorr AND / Chaum–Pedersen | shared challenge, product state, common component interface | group relation and special soundness; a knowledge claim needs its fixed extraction experiment |
| Folding / accumulation | arbitrary residual outputs and terminal observations | residual relation preservation, public/private boundary, final discharge theorem |
| Stateful lookup / random oracle client | coupled initial laws, repeat calls, exact map-based installation | cache invariant and admitted adversary access |
| Zero knowledge | exact structural transport reused on each game/view | simulator construction, hiding theorem, correct observation; not one unary soundness contract |

These rows are design tests, not newly verified production protocols. The implemented complete
model clients and their exact proved claims are listed in the validation record. Before actual
integration, review this core and require the source adapter to bind the *fixed actual subject*
to this common path. Do not declare production success from a model-only theorem.
