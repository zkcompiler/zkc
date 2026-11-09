# A Process-facing protocol-proof framework

This package owns the top-level proof framework over the shared `ZkcProgram` foundation.
Its acceptance object is a proved claim about a complete model game, assembled from local
facts. Package 1 migrates that framework to canonical Process without importing concrete IR,
source readers or production protocol clients. It does not certify an existing `.zkc` artifact.
The selected architecture and current ownership limits are in [IMPLEMENTATION.md](IMPLEMENTATION.md).

## The proof structure

```text
Fixed request about a complete experiment
└─ UpperEvidence.establish / LowerEvidence.establish
   ├─ Subject binding: the request denotes this fixed system and client
   ├─ Installation: complete local operation couplings + whole initial-law coverage
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
used many times; the same exact installation supports completeness and soundness. A mathematical
model may be proposed by automation, imported from another library, or written in a companion.
Its origin does not change any proof obligation.

## One execution and several judgments

The public execution carrier is canonical `PIR.Process I A`, with typed `PIR.Signature`
operations, adaptive continuations and explicit `.halt` stops. `PIR.Outcome` distinguishes
returned values from stopped reasons; `PIR.Execution` retains outcome, reached state and
ordered events. These definitions come from `ZkcProgram`, alongside the generic
`Zkc.Source.Region`. Region preserves typed structure and nested bodies; `Region.denote`
produces Process. Concrete dialect meanings remain with the concrete IR owner.

The single probability interpretation uses `Internal.effects I` and `Internal.encode` to feed
VCVio's `PFunctor.FreeM.runKernel`. The internal reply type is `Outcome (I.Reply op)` and the
threaded state is `S × List L`. Encoding short-circuits stopped replies; ordinary FreeM bind
on an outcome value would incorrectly continue. Authors do not translate clients into FreeM.

`System E I S L` supplies normalized operation kernels returning full Execution and a normalized
initial law. `accumulatedOperations` appends events even for a stopped call;
`initialWithEvents` maps the whole initial law to an empty event prefix. `runFrom`, `run` and
`experiment` use this one interpretation, with complete records recovered by a measurable
bijection. Reject, abort, exhausted, incomplete and refused stops retain their mass and reached
records. The Process equations and Dirac agreement relate this meaning to canonical deterministic
execution; they do not define a second probability evaluator.

An operation samples outcome, successor state and events jointly. All calls share the threaded
state. Sampling answers and states independently is a different kernel; service names do not
imply independence. Privileged semantic state is not automatically visible to an adversary:
the selected client and interface determine access. The adaptive model's strategy sees only
prior challenge answers. Lower-level backend contracts can handle subprobability kernels,
but request-facing System experiments cannot silently lose mass.

Keep these proof boundaries distinct:

- **Installation:** exact joint-law coupling for the same client and typed interface, with a
  relation on accumulated state/log pairs and equal complete outcomes. It covers the whole
  initial law and has no security error budget.
- **Representation:** differing interfaces, programs or result encodings need a separate full
  meaning theorem, including malformed answers and stops. Same-interface state maps are a
  supported special case, not a general decoder theorem.
- **Security transformation:** a change of game or adversary access carries explicit environment
  translation, assumptions, loss and resource obligations. It is not exact installation.

A mathematical upper/lower contract is a reasoning method across these boundaries. Its terminal
potential can describe a bad event, residual obligation or successful outcome; it is not a
protocol-family tag. Broader representation and security-transformation APIs remain parent-owned
Package 2 work.

Upper and lower contracts are separate because the implication directions differ. Canonical
property meanings are separately typed: promise soundness, honest completeness, fixed recovery,
bounded extraction, statistical simulation, and selected-observer simulation. Their detailed
quantifiers and resource boundaries are in [CLAIMS.md](CLAIMS.md). They share execution and
mathematical proof infrastructure without pretending to be the same property.

## Contracts and exact installation

`OperationSpec I S L` transforms continuation rewards on complete outcomes and accumulated state.
`opExpectation` supplies exact local expectations. Public `wpFold` uses PolyFun's fold on the
stop-aware encoding; `UpperBound` and `LowerBound` reuse the existing backend contracts.
The backend theorem `Internal.wpFold_eq_runExpectation_of_measurable` identifies that fold with
kernel expectation. It accepts arbitrary measurable state/result spaces and a measurable
reward, with countable operation replies and measurable singletons. Only its unrestricted-reward
specialization additionally requires countable state/result spaces with measurable singletons.
Measurable events and relations remain explicit premises of transport.

The public `System.wpFold_eq_lintegral_runFrom` expresses exact expectation over full Execution
records; `System.lintegral_wpFold_eq_experiment` integrates over the whole initial law with
events. `System.runFrom_bind` retains stopped records and requires a countable intermediate
return type with measurable singletons. `System.experiment_eq_dirac` requires Dirac primitive
and initial laws. These laws reuse the same backend interpretation.

The Process bind rules pass the returned value and reached state/log to the continuation and
require a separate inequality for every stopped terminal reward. Finite-iteration rules use
one round-, outcome- and accumulated-state-indexed invariant, a body theorem and a stopped-branch
obligation. Nested iteration reuses that rule. A model that gives stops zero acceptance reward
must say so in its postcondition; it cannot remove their probability mass.

VCVio's `KernelHandler.CouplingContract` and `bind_state_laws` provide local-to-contextual coupling
for adaptive clients. The Process-facing `Installation` supplies those contracts over the
outcome-valued accumulated handlers and couples the whole initial distributions. Public
`UpperEvidence.establish` and `LowerEvidence.establish` reuse the existing internal roots through
`Execution.measurableEquiv`; the mathematical and terminal fields remain substantive obligations.
The additional public probability and contextual-transport laws are tracked in
[IMPLEMENTATION.md](IMPLEMENTATION.md), separately from final integration validation.

`Representation.contractOfMap` constructs a local coupling from a total measurable map on
accumulated state. The map need not be injective. `Installation.ofMap` additionally requires the
pushforward of the entire actual `initialWithEvents` law; `Installation.reflexive` handles an
unchanged representation. `Installation` replaces the old public `Connection` without an alias.

`PIR.OperationInterpretation` and `Process.interpret` substitute Process implementations for
operations. The shared-state model relates its deterministic multi-call implementations to
`System.run` by `run_eq_dirac`, and proves `component_inlining` using `Process.run_interpret`.
This retains shared state across calls; it does not establish arbitrary differing-interface
representation or the parent-owned service-wiring package.

A runtime parser, polynomial encoding or answer decoder must prove its full answer/state/event
meaning, including failure. Deleting an output field or matching a function name supplies no
such law. A representation may erase an audit field only when later calls and the requested
observation cannot distinguish it. Resetting an observable counter invalidates the local law.

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
| Actual compiler subject binding | Integration owner | Binding of the fixed concrete subject to shared execution |

No model companion needs to traverse Process or its internal encoding to re-prove universal
installation. Some model proofs induct on a *mathematical round count* or prove a state invariant;
that is a mathematical argument. Automatic structural application does not discover arbitrary invariants, representation
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
proofs belong to the same Lean package's build scope. No new theorem is claimed merely because an
existing library already has the appropriate interface.

The earlier standalone checkpoint used ordinary Lean theorem applications without a proof
constructor. The selected architecture adds a shared checked derivation over typed Region and
its proposer in a later package. It will reference these semantic contracts and reusable lemmas;
it is not implemented by the present Process migration. A separate PMF-only probability
interpreter remains unnecessary: the upstream kernel interpretation supplies the fixed meaning.

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

These rows are design tests, not newly verified production protocols. The validation record
separates the current Process proof-package gate from earlier complete-model evidence.
Actual integration must bind the *fixed actual subject* to this common path. A model-only
theorem does not establish production success.
