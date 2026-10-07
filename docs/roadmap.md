# Roadmap

This page owns the order of work. [Status](status.md) records implementation;
[the specification](spec/README.md) owns semantics. A counterexample or simpler
validated design can reopen a specific boundary. There is no fixed calendar.
Detail each package immediately before implementation.

## 1. The remaining sequence

The native IR foundation is complete at its declared scope, with bounded
implementation and execution evidence in the [validation map](compiler/foundation-validation.md).
Frontend migration and the native Lean connection come next. The target remains one mathematical compiler path and one
general interpreter with installed primitives.

Start from `protocol → participant → exec → physical` and one mathematical SSA
program. Revisit a responsibility boundary when a concrete counterexample or simpler
validated design warrants it.
Direct MLIR programs and small generators exercise the foundation before frontend
migration. Independent noninteractive proof production and validation, including
selected transcript constructions, belong to the foundation. Rust code generation
and general network transport remain later work.

### Completion milestones

| Milestone | Completion condition |
|---|---|
| Foundation capabilities implemented | Every required capability and composition in the declared executable profile has ordinary compiler/runtime support, executable controls and explicit limits. Another program within that profile needs authored IR, inputs and declared installations. It requires no dispatch on a protocol name or separate executor. |
| Foundation stabilized | The whole-foundation validation requirements have been met. Semantic and implementation owners, actual checking boundaries, failure behavior, extension paths and retained consumers are explicit; final integration controls and independent review cover the resulting implementation. This adds no native correspondence or security theorem. |
| Native migration complete | Required frontend, library, host, checker, optimization and public-tool consumers use the new model with their required behavior and evidence. Defaults have moved, and superseded compiler paths, carriers, internal adapters and dependencies are removed. |

The [completion contract](compiler/ir-foundation.md#completion-tests-and-limits)
and [validation map](compiler/foundation-validation.md) define the completed
foundation scope. [Assurance](assurance.md#6-implementation-correspondence-policy)
requires native Lean differential evidence before full migration closes. The
[migration inventory](compiler/migration.md) records the remaining consumers;
foundation completion alone does not retire them.

### Target and reuse policy

Use the native mathematical pipeline as the target for migrated capabilities.
The fresh `.zkc` source path covers mathematical helpers, nominal products/variants,
static components/generics, permissions, bounded naturals, ordered local control,
messages and selected Entries with independently checked MLIR emission. The next
package, **Protocols and specifications**, has implemented services, composition,
distributed control and formal polynomial authorship against the existing IR.
Typed predicates and attachments with an independent reader remain next. Follow it with **Entries and Host** for
construction selection, trusted inputs and typed CLI jobs. Finish with integrated
stabilization, consumer migration and removal of superseded paths.

Detail each package before implementation. Relation targets remain distinct from
input/output conditions. Dynamic data access, additional native primitives and
broader inference enter through their owning contracts when a concrete library
requires them; they are not protocol-specific executor exceptions.

Use existing implementations as references when their contracts fit. New source
code belongs to the Language component and emits native mathematics directly.
The `.pir` route retains its current consumers until their required behavior and
checking obligations have migrated.

Classify each requirement before deciding where to implement it:

| Requirement | Owner and treatment |
|---|---|
| Round order, witness calculations, verification equations and subprotocol composition | Author a library program in the general IR. |
| A new mathematical or cryptographic primitive | Add a reusable operation contract, realization and backend installation where required. Scheme-specific arithmetic and encoding keep their exact contracts. |
| Shapes, resource flow, provider/key binding or message handling needed across programs | Complete the general IR/runtime boundary, even if one protocol first exposes the need. |
| An external file/proof format or application deployment convention | Use an explicit adapter and compatibility contract. Defer it when outside the current foundation scope; retain any existing migration obligation. |

Compiler and interpreter control must follow operations and contracts. A hidden
whole-prover/verifier callback does not close a foundation requirement. Installing
a new primitive can require code; authoring another program from already admitted
primitives must use the existing machinery.

### Capability baseline and design method

Before changing a capability, capture its supported behavior, exact affected
ranges, consumers and comparison evidence from the [baseline](compiler/migration.md).
Follow the [migration design procedure](compiler/migration.md#research-and-redesign-for-each-capability):
derive the required contract, choose its owner in the new architecture, compare
reuse/redesign/removal, and move consumers with their checks. Preserve required
meaning and external behavior while allowing internal formats and organization
to change. Features outside the supported baseline need an explicit adoption
decision.

Write representative protocol compositions during design and implementation:

```text
author a required composition → identify the missing general contract
    → research and compare designs → implement
    → check a contrasting client and failures → retain regression coverage
```

Use the [protocol corpus](compiler/ir-foundation.md#using-the-corpus-to-choose-abstractions)
throughout this cycle. Each component client completes its actual computation and
terminal checks. Keep complete Schnorr and Sumcheck clients as regressions; full
BP+, Groth16 and zkVM libraries need not all be authored to close the foundation.
Research and review precede each implementation package. A counterexample can
change its design or bring a dependency forward. Later packages remain coarse
until their own starting point.

### Next package: protocols and specifications

The `.zkc` compiler path and types/local computation are implemented.
Managed services, static protocol composition, distributed repetition and
conditional participant completion now connect to their existing IR contracts.
Catalog-backed data/kernel bindings now cover vector, matrix, sequence and
iterative folding clients. Mathematical helpers now retain one mathematical body
when called from local code, using checked realization and existing execution
recipes. Bounded power-of-two shapes support generic multilinear library types.
Formal polynomial authoring and explicit R1CS/AIR asset capture are implemented.
Next, complete typed predicates and attachments. Preserve actual receives,
service roots and aliases, draw occurrences, ordered guards/stops and resource
flow through nested applications and control.

Before enabling syntax, check source-to-IR mappings with contrasting protocol
clients. Resolve conditional service queries and the data access needed by those
clients under their owning contracts. Fixed source arrays currently offer static
numeric indexing; dynamic data uses installed native containers. General source
records in runtime-length collections still need layout-preserving packing. Add member-specific generics only if a concrete library requires them.
Private input validation and setup authority must connect to the later Host
boundary before those inputs are admitted.

Then define typed predicates and a versioned attachment schema with an independent
reader. Keep relation targets separate from input/output conditions and runtime
guards. Check both runtime-parameter and captured-definition relations, plus
continuation targets bound to exact component results. Unsupported mappings must
remain explicit. Entries and Host follows with construction selection and typed
jobs; integrated stabilization then moves consumers and removes superseded paths.
Native Lean correspondence remains required before full migration closes.

### Foundation completion and later migration

The foundation scope is defined by the [structural requirements](compiler/ir-foundation.md#protocol-corpus-and-structural-requirements)
and [acceptance criteria](compiler/ir-foundation.md#completion-tests-and-limits).
The [validation map](compiler/foundation-validation.md) maps these criteria to
compiler/runtime support, composed execution checks and explicit limits. Writing
a complete library from supported mechanisms has its own migration milestone.

With stabilization and cleanup complete:

1. Connect frontend elaboration and native Lean/checking as consumers of the
   stable contracts. Detail their dependency order when each package starts;
   retain direct MLIR input. Preserve source identity, requirements and actual
   settings, operands and service/key authority. Inventory `.pir`, R1CS/AIR,
   generic/static libraries, diagnostics and checking consumers as the fresh
   Language path expands. Define each exchange boundary before
   adding an independent reader; avoid another editable mathematical IR. Require
   source-to-native equivalence at its stated scope and installed API checks for
   contrasting vertical clients. Remove their superseded paths. Existing proofs
   must connect to the actual new representations and propositions.
2. Redesign and migrate remaining libraries, construction and optimization
   consumers, table execution, host preparation and external integrations.
   Preserve required behavior and comparisons from the migration inventory,
   including existing Groth16/snarkjs, machine and AIR clients. New full BP+ and
   lookup libraries retain separately selected scopes.
3. Move CLI/SDK/default entry points and validate installed users. Remove each
   superseded compiler path, carrier, internal adapter and package dependency as
   its last consumer moves. Remove unused private helpers within their package.
   Independently useful mathematics and formal models retain their own purpose.

Every temporary adapter needs named consumers and a removal condition. Deferring
an existing external compatibility consumer can keep its adapter live; foundation
completion alone cannot satisfy repository-wide retirement. Full transition
requires all retained consumers and evidence to move, defaults to use the native
model, and no active path to depend on a superseded internal compiler route.
Independent external adapters can remain with explicit contracts.

Native Lean semantics follow the frontend exchange design. Shared readers remain
correct and refuse unsupported formats explicitly. Source/candidate checking,
structural admission, reference execution and formal correspondence retain their
separate claims throughout migration.

The [migration inventory](compiler/migration.md#capability-owners) records required
behavior and checking for authoring, libraries, local computation, interaction,
mathematics, applications, public interfaces and independent consumers. Its
[comparison rules](compiler/migration.md#evidence-and-comparison-rules) govern each
slice; difficult migrations remain explicit obligations.

### Research after migration

Preserve existing analyses and transformations during migration. New research
then extends the stable foundation:

- Affine observation, algebraic completeness, extraction and richer security
  analyses, with a named fragment, observer/continuation and independently
  supplied premises. Their required mathematical inputs are retained now.
  An independent research lane can implement an analyzer earlier without making
  it a prerequisite for frontend, placement or foundation completion.
- Broader automatic Fiat–Shamir and new challenge-derivation profiles, with
  explicit fixed inputs, encoding, domain/occurrence identity, sampling and
  security premises. Authored transcripts, selected native constructions and
  existing construction functionality are earlier foundation/migration work.
- Useful optimization: shared-factor strategies, fusion, storage, caching,
  parallelism and bulk-kernel tuning, measured against meaningful baselines.
- Formal compiler/property correspondence and proof reuse at the actual adapters.
- Full Monero BP+ compatibility, full production/recursive zkVMs, new relations
  and protocol families, and general concurrent interactive transport. Independent
  noninteractive participant execution is an earlier foundation requirement.

Private PCS/oracle terminals needed by the foundation corpus are brought forward;
new schemes and their security results are later. Factor fixing versus caching,
larger interpolation, and transformations beyond structural recognition retain
separate evidence obligations. A required client exposing a semantic gap takes
priority over this nominal order.

## 2. What closing a unit requires

Close a unit at its declared evidence level. A selected design, tested native
implementation, proved checker and cryptographic theorem are distinct results.
In particular, deferring native Lean work does not authorize claiming its
correspondence theorem from tests or a structural recognizer.

- State the supported source subset and the exact remaining gaps. Unsupported
  syntax and missing evidence are explicit outcomes; implementation coverage
  never redefines the model.
- Give each extension boundary a real consumer and positive/negative controls.
  Adding a domain does not replace generic binding/control, and a new claim or
  execution kind cannot reinterpret earlier evidence.
- Exercise a general architectural change across two contrasting clients, at
  recorded scope. Distinguish expression, execution, analysis and proof coverage.
- Bind any check to the actual source/candidate and retained requirements. Name
  its stage, recognized grammar and permitted pass set. A proved checker claim
  additionally requires the corresponding soundness theorem; structural checks
  and existing postconditions retain their narrower claims.
- Cover states, observations and failure paths in bounded differential
  validation. State parser, FFI, primitive, connector and toolchain trust. Record
  optional implementation proofs separately.
- Check executable boundary coverage separately from IR formation: each mapped
  external input needs an installed codec or host constructor, and unavailable
  mappings refuse at deployment admission. Preserve valid internal types for
  other uses. Structural limits and encoded/input/work budgets remain distinct.
- Mutation controls must target actual operands, including source coordinates,
  transcript observations and acceptance guards. Metadata agreement alone is
  insufficient. Separately validate the authored algorithm's terminal predicate
  against an independent reference or its declared formal evidence.
- Maintain examples reproducing the claimed compilation, checking and execution.
  Add theorem instantiation when a formal connection is claimed. Keep compiler
  evidence, per-proof verifier acceptance and runtime guards distinct.
- Separate search, proof construction, replay, execution, memory and byte costs
  when measuring them. A speedup is not required for correctness; retain an
  unfavorable measurement.

## 3. Research triggers

At the start of every package, inspect the checkpoints below and record which
triggers apply. A triggered item receives a concrete decision or a stated
blocker before the dependent feature is admitted. Untriggered items remain
deferred. This keeps later choices visible without implementing them in advance.

### Design checkpoints

| Decision | Revisit before / when | Required result |
|---|---|---|
| Shared polynomial carrier versus specialized operations | A migrated or new consumer exceeds the implemented formal polynomial vocabulary | Retain formal meaning and sharing; compare projection, execution and known bounds |
| Tensors, nominal aggregates and nested collections | A required type or codec exceeds the implemented structured-data profile | Checked shape/arity, explicit logical messages, encoding and complete failure behavior |
| Structural recognizer versus named relation/terminal operations or preservation certificates | Initial native check, then any useful rewrite it cannot recognize reliably | Accept legitimate forms and reject changed subjects, requirements and edges without building a general prover |
| Explicit region captures and ui64 indices selected; `compute`/located types unneeded by current clients | The first useful map/loop or component rewrite that flat operations cannot serve cleanly | One dependency query covers operands and captures across all consumers; totality, bounds and role availability are preserved |
| Authored `linalg` and bufferization | A real fusion or memory consumer after foundation execution works | Measured benefit and explicit aliasing, storage and failure contracts; dynamic shapes are already foundation work |
| Helper summaries, degree refinements and opaque polynomial boundaries | Inlining cost or a real opaque boundary becomes necessary | Body-derived or independently checked summaries; unknown degree/meaning never passes through annotations alone |
| Shared-factor representations, recomputation, parallelism or e-graphs | A correct baseline exposes actual work/storage or scheduling cost | Fair comparison and preservation of interaction, state, resource and failure observations |
| Broader external relations, composition and private terminals | A selected R1CS/AIR adapter, composable reduction or PCS/oracle client needs them | External encoding adequacy, role mapping, actual residual connections and the relevant terminal/opening contract |
| Broader automatic Fiat–Shamir and transcript ownership | A client exceeds the selected native derivation profiles | Exact sent/received challenge and transcript bindings, provider/observer model and the claimed sampling/security law |
| Dynamic origins and draw selection | A new construction exceeds supported static paths, loop coordinates or attempt scopes | Explicit original paths and dynamic coordinates, checked per-role event order and selection, compact execution, and no reliance on generated helper names |
| Public witnesses and commitment replacements | A required construction intentionally exposes an assignment or replaces it with a commitment | An explicit policy and actual terminal semantics; preserve the flat profile's refusal of verifier-available witness inputs until that extension is selected |
| Algebraic completeness or special-soundness analysis | A selected algebraic fragment and interpreted source requirement | A derived solver view, explicit premises, accepted/refused examples and evidence at the exact claimed scope |
| Frontend migration and removal of legacy paths | Frontend exchange design and each subsequent consumer migration | Complete coverage inventory; generated execution and required outcome/format parity; retire each replaced path with its last consumer |
| Native Lean semantics and proof reuse | Exchange design, then each checker/formal consumer migration | Precise meanings, independent checks and actual theorem instantiations at their stated scopes; general new proofs remain separately tracked |
| Lean/Mathlib and ArkLib/VCVio upgrades | A coordinated stable toolchain update | Port adapters from `probOutput`/`probEvent` to the upstream measure API and rerun dependency/axiom audits before changing the pinned graph |
| New dialects or higher-order abstractions | A real semantic responsibility lacks a coherent existing owner | A concrete client, ownership boundary and simpler alternatives considered; dialect count is not a target |

Direct MLIR input is already an independent authoring API. Its compiler library
still links shared source/frontend workflows. Split that link closure when a
native-only embedding or measured dependency cost requires it; preserve installed
components and shared compilation diagnostics. Before an independent frontend or
Lean reader consumes mathematical source, choose a versioned exchange contract
and bind the actual source/toolchain identity. Neither trigger introduces another
editable mathematical IR.

The broader research triggers below are extensions, not definitions silently
required by the finite core. Each starts from its promised outcome and exact
obstacle. They apply when its associated claim is selected.

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
