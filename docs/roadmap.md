# Roadmap

This page owns the order of work. [Status](status.md) records what the
implementation supports today; the [specification](spec/README.md) owns the model
that work is measured against. Research reopens a specific contract when a
required law or client fails; broader capabilities enter through the triggers in
section 3 rather than through the sequence in section 1.

## 1. The remaining sequence

The immediate program is the [mathematical protocol foundation](guides/mathematical-protocols.md):
shared typed mathematical graphs, checked placement, polynomial representations,
analyses and scheduling, connected to independent execution meanings. The
captured-project frontend, notation, component/library support and existing
native routes remain the migration base. All capabilities in the guide's
architecture table remain foundation requirements. The order below gets an
actual generated protocol running before completing every admission and proof
implementation. Engineering handoff and formal completion have separate gates.

1. **Mathematical contracts and independent meaning.** Define role components,
   total pure regions, capability identity, indexed control, polynomial/static
   shapes and canonical source/placement contracts. Exercise Sigma, Sumcheck and
   component reuse in Lean, and establish scoped VCVio/ArkLib connections.
2. **Bounded carrier handoff.** Exercise the actual serialized Sigma subject
   through the MLIR-independent carrier and independent byte/schema readers.
   Decode this subject in Lean and compare its used declaration identities,
   operand types, roles, roots and sites. Declare and enforce the development
   envelope before measuring it. Full typed-admission parity, the common work
   envelope and capacity-oriented Lean optimization remain named work. They do
   not block placement development; defects in the exercised subset block its
   integration handoff.
3. **First generated protocol.** Install the mathematical field/group operations,
   wires and nonce/challenge services required by Sigma, reusing existing domain
   and backend owners. Extend existing notation to produce the mathematical
   subject, place it into located inline pure regions, project both roles and
   execute them through the current runtime. Keep the verification equation
   inspectable through projection. Define the new meanings over actual carrier
   types and check the actual emitted candidate in Lean. Prove the representative
   fresh-receive/pure-effect law early; full checker closure follows integration.
   Consolidate the exercised declaration and pure-region responsibilities, and
   move the Sigma fixture to the canonical admitted mathematical language. Other
   example migrations and repository-wide cleanup are not entry conditions.
4. **Structured polynomial and component execution.** Add the serialized Sumcheck
   and shared-service clients and their operation slices. Preserve indexed loops,
   shared post-message updates, actual terminal evaluation and capability aliases.
   Add virtual/materialized polynomial views, residuals and kernel selection.
   Compare the same mathematical objects, canonical wires, failures and resource
   domains across these representations.
5. **Useful graph transformation and scheduling.** Implement pure sharing and
   rewrites, algebraic extraction with group/field normalization and an
   identity/ideal-membership certificate subset, and physical schedule selection.
   Demonstrate changed work on both
   scalar/group and structured polynomial clients. Include one justified movement
   of total pure work across an effect boundary and reject a partial movement
   that changes stopping. Measure against unoptimized and matched external paths.
6. **Formal consolidation and component coherence.** Consolidation starts when
   executable clients expose representation issues. Complete the deferred
   admission/parity work, placement and extended projection laws, pure outlining,
   selected polynomial/analysis/scheduling laws, and family/substitution and
   component replacement laws. Finish applicable VCVio/ArkLib correspondence.
   Finish migrating the initial small mathematical model's remaining consumers
   and retire its duplicate interpreter; retain useful notation as builders.
7. **Migration and foundation acceptance.** Lift maintained legacy clients
   conservatively, preserving ordered unknown operations. Remove duplicate
   semantic storage only after replacement coverage exists. Complete the selected
   executable examples and their promised formal laws before declaring the
   foundation complete. Detailed protocol-security research then builds on it.

These units describe dependencies, not a requirement to finish all formal work
before starting the next compiler change. Placement development can run alongside
the bounded carrier handoff. Initial general optimization is not a prerequisite
to the first Sigma execution. A handoff never relabels unfinished formal work as
complete. The [status page](status.md) records implemented coverage.

Follow the [integrated ownership design](architecture.md#integrated-ownership).
Migrate one client through existing frontend, contracts, IR and runtime owners.
Each such change records what it retains, replaces and removes, and which
consumer migration retires a temporary adapter. Share established primitives as
the client needs them; a new repository-wide abstraction is not a prerequisite.
Carrier changes may replace v0 formats, with all actual readers moving together.

After the first Sigma path, evaluate authoring changes on the same client before
expanding the owned optimizer. Record the metadata and implementation work needed
to preserve the independent semantic backend. Use direct libraries and the
existing compiler with thin notation as baselines when judging new machinery.

BP+ composition and a zkVM proof path remain contrasting downstream consumers.
Existing archived BP+/OpenVM controls validate particular interfaces, not full
protocols. Their next expansion first fixes upstream revisions, accepted inputs,
proof-byte compatibility and verifier acceptance. General relation-to-argument
elaboration, independently deployed role modules and a stable deployment ABI
remain later consumers of the foundation. Fixing canonical mathematical subject
bytes does not fix every runtime artifact ABI or frontend syntax.

## 2. What closing a unit requires

### Engineering handoff

A development handoff permits dependent implementation work. It does not grant
the formal guarantees listed below.

- The supported source subset is stated. Unsupported syntax and missing evidence
  are explicit outcomes; implementation coverage never redefines the model.
- Each new extension boundary has a real consumer and its own controls. Adding a
  supported operation or domain does not replace generic source binding and
  control, and a new claim or execution kind cannot reinterpret prior evidence.
- Each new carrier construct has an independent meaning over its actual typed
  representation. List the preservation proposition, premises, current evidence
  and counterexample controls in the maintained support/correspondence owners.
  A named proposition without a proof remains an obligation.
- An executable candidate check identifies the actual original and generated
  subject and rejects meaningful mutations. Before its soundness theorem exists,
  report it as an implementation check, with that proof obligation still open.
- Differential validation covers the declared subset, its states, observations
  and failure paths, with reproducible artifacts and stated gaps. Remaining
  parser, FFI, primitive and toolchain trust is stated rather than implied; an
  optional native proof is reported separately.
- Rebuild affected tools from the recorded source snapshot before handoff checks.
  A prebuilt focused executable is interim evidence unless its source/build
  correspondence is established; unchanged verification scopes may be reused.
- The first maintained path reproduces source elaboration, generated roles,
  candidate checking and execution. Sigma controls include honest acceptance,
  fixed tampered-message rejection, refusal of a verifier dependency on the
  prover's private witness, and
  preserved pure-operation identities/operand provenance in the generated
  verifier. Nonce and challenge are distinct occurrences at distinct roles.
  A separate minimal two-nonce control queries the same capability twice and
  requires distinct occurrences and two handler steps; sampled values may coincide.
  The selected challenge service refuses replies outside its declared `F*`
  domain, with a fixed failure-path control at the verifier's handler boundary.
- Measurements separate search, proof construction, replay, execution, memory and
  bytes. A speedup is not required for correctness, and an unfavorable
  measurement is retained.

For the initial unoptimized projection, compare pure operations against the
placed subject and record a per-node difference. Pruning is allowed only for
total pure operations with no data path to a projected role's guard, control
condition, send, return, or effect/call/service operand. Duplication is allowed
only with the same declaration identity and operand provenance. Any other
missing, added or re-sourced pure operation fails this inspection. Later algebraic
rewrites need their own checks and laws; this rule does not prohibit them.

The development envelope names packages and limits for every potentially large
input or derived structure on the exposed path. Derive it from the client's needs
with stated headroom before testing. Enforce it at the entry point and before
the expensive work it bounds; test exact-limit and over-limit behavior. A crash
inside it blocks handoff. Changing the envelope requires a recorded reason and
rerun, and cannot silently narrow an existing consumer's contract. Input bounds
alone do not prove a bound on callback work or full execution cost.
Record required runtime resources, including stack and thread configuration,
for each consumer. Supported entry points establish or check those requirements,
and boundary controls run under the declared configuration.

Shared-format changes still update every actual consumer together, including
affected Lean typed decoders. Enumerate source codecs/admission, MLIR import/export
and verifiers, projection, runtime/plan consumers, independent references, printers
and fixtures as applicable. Schema correctness, capacity and proof completion
are distinct obligations. Independent readers do not delegate admission to each
other. Limits claimed as a common profile must agree across its consumers.

### Formal closure and final acceptance

Keep core mathematical definitions and difficult representative laws early.
Detailed proofs and efficient proof-producing decoders follow representations
exercised by actual clients. Existing proofs remain maintained; semantic changes
update their owners immediately. No axiom or `sorry` substitutes for an open law.

- A claimed checked transformation has a proved source-relative checker law that
  binds its actual source, final candidate and remaining requirements.
- Pure outlining has its introduced-call folding law. Polynomial and physical
  changes have their stated representation and complete-outcome relations.
- A substantive reusable transformation is exercised across two contrasting
  clients before the foundation claims that generality. Bounded size tests do
  not replace family laws.
- Maintained examples instantiate the promised selected-profile theorems, with
  the actual source/candidate and explicit native/provider premises. Security of
  individual proofs and protocol experiments remains a separate claim.
- All adopted authoring, graph, extraction, polynomial, algebraic-analysis and
  scheduling capabilities have executable evidence. Their required formation,
  transformation, family and adapter laws are closed at the declared scope.

Each implementation unit should deliver a compiler capability on the next client
path or repair a named semantic defect. Capacity work outside that path is
separate unless it blocks an existing published claim. Reopen a core design only
for a concrete counterexample, failed client/law, or measured simpler alternative;
update the adoption and obligation maps with that decision.

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
join. Record these when introducing a boundary and complete them under the
engineering/formal gates above. Moving proof work later never grants its claim
earlier.

The [assurance policy](assurance.md#6-implementation-correspondence-policy)
requires bounded native differential evidence. Optional proofs target the
actual implementation and strengthen the named adapter at their stated scope.
