# Roadmap

This page owns the order of work. [Status](status.md) records what the
implementation supports today; the [specification](spec/README.md) owns the model
that work is measured against. Research reopens a specific contract when a
required law or client fails; broader capabilities enter through the triggers in
section 3 rather than through the sequence in section 1.

## 1. The remaining sequence

The compiler runs authored protocols through common source, participant
generation, physical lowering and Rust execution, with checked candidates in
between. The captured-project frontend and checked component/library foundation
are implemented at the scopes in [status](status.md). The next implementation
program should use them to complete contrasting protocol clients: BP+ component
composition and a zkVM proof path, with shared changes justified by both clients.
Existing archived BP+/OpenVM controls validate specific interfaces; they are not
complete implementations of either protocol.

Choose exact upstream revisions, accepted inputs, proof-byte compatibility and
verifier acceptance before expanding either client. First close the supported
client's blocking library/provenance and kernel gaps; then measure reusable
optimizations against the matching direct library. Reopen source or semantic
contracts only for a demonstrated expressiveness or correctness gap. Repository
packaging and publication do not settle these protocol acceptance criteria.

The capability work below is ordered by dependency, not by size.

1. **Broader backend coverage and resource guarantees.** Real Arkworks, Dalek
   and Plonky3 paths already execute. Extend the required kernels, layouts and
   resource accounting for the next supported clients; keep their actual
   adapter and memory/progress assumptions explicit.
2. **Shared demand and preparation reuse.** Discovered across contrasting
   clients, checked against retained source, and measured against an equally
   capable library that uses the same algorithms and cache policy.
3. **Broader endpoint admission and checked transformations.** Bounded phase,
   physical interpolation and linear-contraction routes exist. Extend their
   supported subjects and candidate checks without treating those instances
   as general endpoint or transformation coverage.
4. **Separately deployable role modules.** Participant lowering produces
   role-local instructions today and supported native routes execute them.
   Independent deployment and its coordination interface remain open.
5. **Verifier lowering, resource accounting and general relation-to-argument
   elaboration.** The AIR and oracle route is authored per protocol; arbitrary
   elaboration and host accounting for larger runs are not implemented.
6. **The artifact ABI and the authoring language.** Both stay deliberately
   unfixed until their consumers exist.

Component security correspondence, production hiding, sparse matrix commitments
and additional protocol families are separate programs. They enter this sequence
only when a specific obligation makes part of them necessary.

## 2. What closing a unit requires

These conditions apply to each unit above, and they are checks rather than
milestones.

- The supported source subset is stated. Unsupported syntax and missing evidence
  are explicit outcomes; implementation coverage never redefines the model.
- Each new extension boundary has a real consumer and its own controls. Adding a
  supported operation or domain does not replace generic source binding and
  control, and a new claim or execution kind cannot reinterpret prior evidence.
- A substantive analysis or transformation is exercised across two contrasting
  clients, at recorded scope. Expression, proof and native coverage are reported
  separately; more examples do not by themselves establish generality.
- Checking binds the actual candidate: a proved source-relative checker
  identifies the original, the final result and the remaining requirements, and
  rejects meaningful invalid cases.
- Differential validation covers the declared subset, its states, observations
  and failure paths, with reproducible artifacts and stated gaps. Remaining
  parser, FFI, primitive and toolchain trust is stated rather than implied; an
  optional native proof is reported separately.
- A maintained example reproduces compilation, checking, execution and theorem
  instantiation, and distinguishes compile-time evidence from the verifier's
  check of an individual proof and from runtime input guards.
- Measurements separate search, proof construction, replay, execution, memory and
  bytes. A speedup is not required for correctness, and an unfavorable
  measurement is retained.

## 3. Research triggers

The following are extensions, not definitions silently required by the finite
core. Each starts from its promised outcome and its exact obstacle.

| Trigger | Theory to examine | Required discriminating result |
|---|---|---|
| Automatically discover useful preparation and factor sites across source edits | Abstract interpretation, dependency slicing, staged computation, selective memoization | A reusable analysis law and source-edit examples where inferred safe reuse improves a meaningful baseline |
| Optimize richer branching and loops without full unrolling | Indexed types, abstract domains and fixpoints, partial evaluation, equality saturation or translation validation | A defined source interpretation, a sound finite checker and actual counterexamples to omitted premises |
| Change protocol batching or challenge placement | Game-based reductions, probabilistic coupling, algebraic and cryptographic binding, efficient strategy translation | An explicit property transport theorem with its loss, and an actual changed interaction |
| Support Fiat–Shamir or fixed logical oracles | Classical random oracle model, round-by-round soundness, duplex and transcript semantics, concrete instantiation; the quantum model separately | A source, provider and observer contract with a proof for the exact claimed oracle model; fixed-oracle consistency is not fresh independent sampling |
| Bound repeated or adaptive attempts | Conditional probability, stopping-time or martingale methods, composition | An aggregate experiment retaining failures and selection, with a proved loss rather than per-attempt folklore |
| Complete folding and incrementally verifiable computation | Relation reductions, invariant composition, knowledge extraction, scheme-specific algebra | Actual residual and terminal wiring, with a relation and security theorem across steps |
| Expose multiple or transferable exports | Affine and generative resources, capability semantics, separation logic | Issuance, target binding, partial failure and replay laws for the actual richer adapter |
| Support asynchronous or reentrant execution | Choreography projection, session types, concurrency and separation logic, scheduler observations | Implementability and progress, and trace and state correspondence beyond the atomic boundary |
| Strengthen confidentiality to native costs, cache or addresses | Information flow, relational cost semantics, probabilistic simulation | The declared stronger observer, and a positive law or a decisive leakage control |
| Preserve security after linking adversarial target code | Robust property and hyperproperty preservation, logical relations, capability isolation, strategy translation | An explicit allowed target-context class and a transport theorem covering it; common-program refinement alone is insufficient |
| Claim cryptographic soundness for an installed export | Relation reductions, joint initialization, conditional bounds, custody composition | One actual source, statement, verifier event and export decision joined under the same experiment; authorization alone does not prove the claim |
| Verify native backends or independent checkers | Data refinement, verified compilation, foreign-interface and memory semantics | Concrete correspondence to the shared contracts without changing their meaning |
| Offer a richer authoring language or higher-order modules | Staging, dependent and refinement types, session and resource typing, logical relations, elaboration correctness | Authoring benefit with source and context correspondence; higher-order callbacks need their own interpretation and relation |
| Claim optimality or complete search | Constraint semantics, lower bounds, proof-producing search, completeness certificates | A fixed candidate domain including unresolved alternatives, and a checked comparison argument |

Established theory is used where it supplies the needed law. A new theory is
warranted when the desired result has a precise gap those methods do not fill;
that gap, its assumptions and a testable target are recorded before another
open-ended survey starts. Honest-completion, knowledge and zero-knowledge claims
remain separately specified experiments even when a local compiler law is reused.

## 4. The security companion

The security companion is **interactive Sumcheck with per-variable degree at most
two**, parameterized by the public round count and a finite field, implemented in
the [Sumcheck security module](../formal/Zkc/Protocols/Sumcheck/Security.lean)
with its [checked verifier transport](../formal/Zkc/Protocols/Sumcheck/Optimization.lean).
It uses the shared fixed polynomial and Mathlib root-counting laws rather than
admitted stronger knowledge results. The
[optional integration](../formal/integrations/arklib/README.md) states separately
which upstream types, adapter theorems and assumptions it imports.

A security claim about a compiled protocol needs all of the following, and the
last is the one that connects it to execution.

1. The fixed polynomial, claimed sum, variable order, degree condition and actual
   input binding. The [table-source bridge](../formal/Zkc/Protocols/Sumcheck/TableSource.lean)
   proves this from ordered cells and original factor occurrences.
2. Honest execution and completeness, separately from arbitrary interface-valid
   strategies for soundness. Messages are chosen before their challenges, and the
   experiment states the joint initialization and sampling law. Honest completion
   states its availability and resource conditions.
3. The residual round claim and terminal evaluation of the same polynomial at the
   delivered point. An evaluation backend is governed by its stated contract;
   returning a scalar does not complete the argument.
4. A quantitative false-acceptance bound and a meaningful checked source change
   through the compiler interfaces.
5. The changed experiment's property and its connection to the executed plan
   under the declared realization, provider and system assumptions.

Identify which endpoint changes. Optimizing an honest prover can require a
completeness argument, while soundness already quantifies over dishonest provers;
a prover-only speedup is not a verifier-soundness result. Ordinary Sumcheck
carries no zero-knowledge property here, and commitment, Fiat–Shamir, knowledge
extraction and a complete SNARK are outside this companion.

## 5. Where the formal library and the implementation meet

The [architecture](architecture.md#6-code-and-checking-lifecycle) owns the
compilation/checking/deployment boundaries. The
[formal connection map](../formal/design/verification-map.md) specifies the
required propositions, premise producers and implementation obligations at each
join. These remain part of every relevant item above, rather than a second
sequence of work.

The [assurance policy](assurance.md#6-implementation-correspondence-policy)
requires bounded native differential evidence. Optional proofs target the
actual implementation and strengthen the named adapter at their stated scope.
