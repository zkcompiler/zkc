# Architecture

zkc has a typed source frontend and a C++/MLIR compiler, Rust execution tools
and backend adapters, and an independently usable Lean semantic library.
They connect through explicit source, artifact and operation contracts.

The [roadmap](roadmap.md) owns sequencing. Concrete dialects, interfaces and
lowering are developed in the [compiler design](compiler/design.md); ownership and
artifact admission in the [runtime design](runtime/design.md). The
[layout](development/layout.md) fixes directory and build conventions.

Supported routes connect source, checking and execution, with selected physical
optimizations. [Status](status.md) identifies those routes; this architecture
also states obligations for extensions that are not yet implemented.

Component connections, exposed acceptance outputs and construction sequencing
have selected semantic contracts. The [target design](compiler/targets.md)
selects physical-plan and acceptance-target responsibilities;
[call admission](compiler/calls.md#6-integrated-admission-responsibilities)
assigns evidence producers.

The system separates four responsibilities: a Lean semantic and verification
library, a compiler engine using MLIR/C++, Rust host/build tools, and a
separate Rust runtime with backend adapters. They share explicit data contracts
and mathematical interpretations. Language boundaries, representation levels,
proof boundaries and deployment units are different architectural choices.

Keep compilation as one cohesive C++/MLIR subsystem: analyses, cost models,
optimization search, planning, transformations and their supporting algorithms
belong together. Rust owns execution, backend integration and product tools,
connected through complete compilation requests and artifacts. Lean owns formal
definitions, proofs and proved checking algorithms. Choose languages for whole
subsystems, considering shared state, change patterns and boundary costs; the
absence of MLIR calls in one helper is not a reason to move it to Rust.

## 1. System map

~~~text
.pir source projects and captured relation assets
                    |
          C++ frontend: resolve, type-check, instantiate
                    |
          common PIR source and construction selection
                    |
          C++/MLIR: participant projection and physical lowering
                    |
          candidate participant/plan artifact
                    |
          independent checking/reference tools <--- Lean libraries
                    |                               (supported profiles)
          Rust host: bind source, artifact, policy and inputs
                    |
          role runner / proof producer / proof validator
                    |
          selected backend adapters and cryptographic libraries
~~~

The [specification](spec/README.md) owns the semantic contracts used throughout
this architecture. The [rationale records](rationale/README.md) explain the
choices a reader could have made differently.

Checking receives the retained original source and the selected consumer policy
through the relevant host entry point. Its input is not limited to the optimizer's account
of what was transformed. The runtime uses the exact admitted plan and bound
implementations. The [checking dossier](../formal/design/compiler-connection.md)
details the implementation connection required by the
[transformation specification](spec/verification/refinement.md).

This map describes the native route. The [target design](compiler/targets.md)
also branches from retained verifier meaning to acceptance constraints and
exposed outputs. A relation artifact has its own adequacy checker and consumer;
it need not inherit a physical allocation schedule. The finite table prototype
demonstrates only its scoped direct logical-plan route. Generated code has its own source-to-code
and downstream execution obligations. Both routes can use the same kernels and
contracts; a proof about a plan interpreter does not cover code that bypasses it.

Researchers can use the formal library without building MLIR. An application
can use a precompiled artifact without installing Lean or the MLIR toolchain,
subject to the artifact-admission policy in section 6. Library applications can
also consume checked plans; code generation is not the only product interface.

## 2. Shared meaning and representation levels

The reference distinguishes protocol interaction P, participant algorithm Aρ,
and execution plan Lρ. P constrains a participant algorithm; it is not simply
an earlier representation of that algorithm. A supplied endpoint needs an
admission connection. Automatic choreography projection is a separate
capability, not implied by accepting a protocol description.

| Representation | Information it retains | Intended work |
|---|---|---|
| Structured authoring source | Protocol and role declarations, statements, typed inputs/captures, public shapes, algorithm bodies and module requirements | Authoring, composition, elaboration and source admission |
| Structured compiler IR | Algebraic/domain structure, SSA/regions, loops, branches, calls and interpreted effects | Demand and fact analysis, specialization, rewriting and protocol-aware optimization |
| Realization plan / OIR carrier | Chosen algorithms and kernels, materialization, storage, schedules and input/error interfaces | Resource planning, execution or further code generation |
| Native implementation | Actual buffers, values, encodings, state, errors and foreign calls | Execution and implementation correspondence |

These are responsibilities, not a commitment to one dialect per row. MLIR may
mix high- and lower-level operations while progressively lowering selected
regions. Preserve each semantic distinction until its consumer has checked it
or a law justifies its erasure. Protocol contracts and property dependencies
remain bound to the transformed subject after computational lowering.
This use of progressive lowering follows [MLIR's design](https://mlir.llvm.org/docs/Rationale/Rationale/).

Proc supplies an effect-tree meaning beneath these structures. It is neither
the serialized source nor the optimization graph. Formal models of source and
plans define their interpretations; adapters connect their actual encodings.
Do not make the mutable C++ object layout, or an independently invented Rust
AST semantics, the authority for those interpretations.

The maintained Formal carriers have narrower, explicit roles:

| Carrier | Role | Relationship |
|---|---|---|
| `PIR.Proc` | Typed effect-tree denotation | Common complete execution meaning |
| `Source.Program` | Finite typed tree source | Interpreted into `Proc` |
| `Source.Region` | Finite source with one shared continuation | Direct interpretation and proved tree correspondence; flattening can duplicate syntax |
| `Compiler.Plan` | Constructor-level direct reference plan | Proved lowering from `Program`; does not select buffers or schedules |
| Physical plan / OIR | Selected kernels, representations and participant control | Supported interactive physical artifacts exist; broader storage/schedule planning remains open and requires value/state/outcome laws |

These are not five mandatory compilation stages. In particular, compact region
checking uses its direct interpretation without first expanding a tree. Similar
constructors do not justify either a second physical-plan clone or automatic
removal of a reference model that has proof consumers.

Use finite, versioned source/plan/certificate data at tool boundaries. A shared
schema can generate mechanical bindings, but generation does not prove decoder
or interpretation correspondence. Transport data need not become a second full
optimization framework. Exact schemas, serialization and reusable Lean SSA
infrastructure are implementation decisions to test on real clients.

## 3. Formal: reusable meanings, laws and executable checking

The Lean component has three connected uses:

| Use | Owns | Client |
|---|---|---|
| Semantic foundation | Execution, roles, effects, observations, contracts, source interpretation, probability and relation-bearing properties | Protocol researchers and all proof components |
| Compiler and realization reasoning | Analysis meanings, transformation laws, heterogeneous source/plan/native relations and sound checking algorithms | Compiler/checker and runtime implementers |
| Protocol-security applications | Actual experiments, source adequacy, completeness/soundness or other selected properties, and appropriate transport | Protocol libraries and certified compilations |

The checking executable is a client of these libraries. Lean checks the proof
that its supported checking algorithm establishes the claimed source-relative
relation. The current table tool runs that compiled algorithm; it does not
reconstruct a proof for kernel replay on every input. Its execution therefore
retains compiler, executable, IO and deployment trust. A separate proof-producing
route can reconstruct each application and replay it in the kernel. These are
distinct assurance policies, as specified in the
[runtime checking policy](runtime/design.md#3-artifact-and-checking-boundary).
Neither route needs to rediscover the optimizer's search. A simple
stable transformation may instead be implemented and proved directly in Lean.
Choose proved transformation or result validation per component, using the
same source-relative relation.

Keep the main formal library independent of MLIR's native libraries and Rust
tooling. Models extracted from actual Rust, and their correspondence proofs,
are maintained adapter clients. External game/protocol libraries such as
VCVio and ArkLib enter through optional integrations that use their actual
definitions and tools. A property using them has those real proof dependencies;
ordinary compiler clients need not acquire the whole protocol-security stack.

The [formal design](../formal/DESIGN.md) owns package and module organization.
The [verification map](../formal/design/verification-map.md) distinguishes
semantic laws, transformation checking, native correspondence and protocol
security. Theorem reuse requires the actual subject and hypotheses, not a
protocol or backend name.

## 4. MLIR and C++: one compiler engine

MLIR is the compiler infrastructure; C++ is the primary implementation language
for its zkc extensions. They are not two pipeline services. Put dialects,
structural verification, analyses, cost models, optimization search, planning,
rewrites, lowering and evidence production in a reusable compiler library with
thin command-line entry points. The engine owns its mutable MLIR contexts and
graphs as well as the decisions that transform them.

Domain structure should be exposed through operation interfaces and meaningful
module summaries. Generic passes should ask for demand, effects, shapes and
applicable laws, rather than branch on protocol names. MLIR interfaces support
this style of extensible analysis and transformation; zkc must supply the
semantic interpretation of each interface. [MLIR interfaces](https://mlir.llvm.org/docs/Interfaces/)

Keep a complete optimization in this subsystem even when some of its algorithms
use immutable data and no MLIR APIs. Separate C++ libraries and interfaces can
make those algorithms reusable and testable without a language boundary. For a
preparation optimization, demand analysis, strategy and cost selection, rewriting
and evidence production all stay in the compiler. This avoids an extra summary
schema, snapshot/invalidation protocol and cross-language debugging within the
optimization loop.

An existing solver or specialized library can justify a foreign-call boundary
when its functionality outweighs the integration cost. Do not preallocate a
Rust analysis or strategy service. Directly proved algorithms can use Lean;
protocol-property reasoning belongs to the formal/property integrations. Any
external result used to justify a transformation still needs source binding and
the relevant checking or proof.

Two kinds of invalidation matter: changing compiler IR can invalidate a cached
analysis, while a represented runtime call can invalidate facts about protocol
state. MLIR's analysis manager addresses the former; zkc's transfer/framing
laws address the latter. Preserving a C++ analysis object does not prove its
runtime-state facts. [MLIR analysis management](https://mlir.llvm.org/docs/PassManagement/#analysis-management)

Preserve field/index distinctions, input and capture order, role availability,
transcript/randomness dependencies and outcome-specific effects. Generic
side-effect and speculation interfaces are mechanisms for expressing such
constraints, not proofs of the protocol laws. Unknown operations require an
interpreted contract or explicit unsupported status.

The engine can spend substantial compile time on specialization, schedule
search, counterexample search, e-graphs, solvers or cost-guided selection. It
exports the supported final result and evidence covering all changes that led
to it. A structural verifier, cost estimate or candidate-search result alone
does not establish semantic or cryptographic correctness. Exploratory results
retain unresolved obligations; certified results follow the checking boundary.

Target-specific code generation belongs to this compiler responsibility even
when emitted code is Rust. Keep the emitter with the compiler; its implementation
language need not match its output language. Artifact packaging and loading
belong to the product tools and runtime. Avoid a hidden second optimizer in the
runtime or an emitter whose transformations escape validation. Internal
optimization by a contracted kernel stays within its declared implementation
boundary.

## 5. Rust: tools, execution and backend adapters

Split Rust responsibilities by deployment and ownership:

| Component | Owns | Dependency boundary |
|---|---|---|
| Host tools and build integration | Consumer policy, tool invocation, diagnostics, input/setup preparation and artifact jobs; broader SDK/build caching is an extension | Source project resolution belongs to the C++ frontend; hosts submit complete jobs |
| Artifact loader and runtime | Admitted plan/configuration binding, actual inputs, state/resource/cache lifetimes, ordered execution and error handling | Does not depend on MLIR or Lean installations for ordinary execution of previously admitted artifacts |
| Backend adapters | Concrete fields/groups, codecs, transcript/random providers and accelerated kernels with explicit implementation contracts | Independently selectable dependencies; external kernels may be Rust, C/C++, assembly or accelerator code |

The driver selects a compilation configuration and submits a complete request;
the compiler owns the internal optimization loop. Experiment automation may run
and compare complete compilation/execution jobs. This does not require moving
cost evaluation or optimization strategy selection out of the compiler.

Rust is useful here for ownership and resource management, integration and a
native library interface. Its type system does not establish a randomness law,
transcript convention or arithmetic contract. These belong to the operation's
meaning and its proved or explicitly trusted implementation connection.

Start with coarse plan operations that perform useful kernels or module actions.
Do not mandate interpretation overhead for every field multiplication. Keep
algorithmic decisions visible to the compiler while letting the backend supply
efficient implementations. Measure granularity against an equally capable
library and, when available, the generated route.

The runtime's formal connection includes actual values, residual state, failures,
observations and allowed progress behavior. The [assurance policy](assurance.md#6-implementation-correspondence-policy)
uses differential testing as the default implementation validation. Optional
native proofs begin with the real zkc-owned binding/cache/state/error core;
primitive contracts can remain trusted.
The [native dossier](../formal/design/native-correspondence.md) owns this scope
and the Aeneas/hax comparison. A new backend satisfying the same sufficiently
strong contract reuses the generic compiler/protocol theorem; its own adapter
connection and assumptions still have to be supplied.

### 5.1 Runtime language

The Rust workspace directly integrates the selected native backends and owns
execution resources. The [runtime language rationale](rationale/runtime-language.md)
compares it with C++ and states when to revisit the choice. Language selection
alone establishes neither a speedup nor native correspondence.

The maintained `.pir` parser and the implemented [common typed source model](compiler/source-model.md)
stay in C++ beside common checking and elaboration. Distinguish this model from
a frontend's syntax tree. For a future independent DSL and editing subsystem,
Rust is the preferred implementation direction, to reassess with its actual
language requirements. That frontend should submit the common source contract;
it does not take ownership of the compiler's optimization loop or MLIR objects.
The maintained frontend now captures multi-file projects before checking, resolves
exact declarations with owner-local environments, and elaborates checked library
selections before lowering to common source. Syntax, resolution, typed analysis,
static selection and PIR lowering remain separate compiler subsystems; tools
query the retained analysis rather than creating an alternate checking pipeline.
See [source projects](language/projects.md) for the implemented boundary.
This does not implement a separate SDK language or move MLIR ownership into Rust.

## 6. Code and checking lifecycle

The logical components can live in one repository with separate Lean, C++ and
Rust build targets. Initially the Rust driver invokes the compiler and checking
executables as local subprocesses, exchanging finite data. This exposes exact
inputs and permits independent builds and reproduction without requiring
network services or calls across languages for each IR operation.

Later embedding can use a narrow C ABI for complete compile/check requests.
Keep MLIR objects and their lifetimes inside the C++ engine. Do not expose its
full mutable graph as the public Rust API merely to share a process. MLIR's
own C API is useful for integration, but is intentionally low-level and currently
provides no stability guarantee. Our product boundary must be chosen separately.
[MLIR C API](https://mlir.llvm.org/docs/CAPI/)

| Boundary | What crosses it | What establishes the connection |
|---|---|---|
| Authoring → compilation | Original finite source, configuration, module bindings and selected claim | Actual elaboration/admission, with the original retained independently of the optimizer |
| Compiler → checking | Candidate plan, intermediate witnesses and premise evidence | Source-relative checking of the complete exported result |
| Checking → packaging | Exact conclusion, subject and retained requirements | Declared policy: per-artifact kernel replay, or execution of a proved checker under explicit build/execution trust |
| Packaging → deployment | Plan/code, concrete configuration and associated evidence | Rechecking or an explicit trusted-build policy, followed by binding the admitted result to what is loaded |
| Runtime → backend | Actual arguments, state/resources and operation results | Implementation correspondence or explicit trust in the selected contract instance |

A file saying verified, or a digest alone, cannot establish the checking to
deployment connection. Deployment must obtain its assurance from proof checking
or a specified trusted build source. Ordinary execution then enforces retained
dynamic guards and bindings; it does not rerun every Lean proof. Individual
protocol proof verification remains a runtime protocol operation.

Reusable compilation evidence quantifies over permitted runtime witnesses and
random choices. Public specialization is identified. A future secret-dependent
specialization stage needs its own observation account. The optimizer cannot
weaken the consumer's observer, replace its original source, or choose a different
security claim in order to obtain acceptance.

## 7. Extension units and dependency direction

Deferring a capability does not defer every decision needed to support it, and
[deciding everything now is the alternative that was rejected](rationale/deferred-boundaries.md).
Resolve a boundary in the first implementing component when a later change would
alter source/plan encodings across languages, erase needed semantic information,
replace resource ownership, reinterpret existing evidence, or couple a protocol
to generic compiler algorithms. Implement the shared contract with the first
real consumer and exercise a contrasting use.

An interface description alone is not implementation evidence. Before declaring
that component complete, demonstrate the promised extension without rewriting
its generic binding, sequencing or checking machinery. This does not require a
second complete protocol stack or backend. New semantics still require new
interpretations and proofs; preserving a place for them does not prove them.
Avoid empty plugin systems and unconstrained metadata bags: add only the small
contract exercised by the selected clients.

A protocol library normally composes source algorithms and interpreted modules.
It should not require edits to the engine merely because another protocol uses
the same operations. A new domain abstraction may add a semantic contract and
laws, compiler operations/interfaces, and native implementations. These related
pieces form one documented extension even when they reside in different language
trees. Mathematical imports must not depend back on native implementation code.

Expose a module body when optimization needs its structure; expose a sufficient
contract where the implementation remains external. Wrapping an entire protocol
in one opaque call does not validate compiler expressiveness. Conversely,
reimplementing every FFT, MSM or pairing inside the IR is not required to make
their callers meaningfully analyzable.

Do not make the core depend on a specific protocol, Arkworks, or a final DSL.
Python, Rust, Lean and standalone-language frontends can target the same finite
source boundary. Native runtime distributions should include only the selected
adapters and execution support, not the compiler or every formal integration.

## 8. Alternatives and confidence

The [subsystem rationale](rationale/system-boundaries.md) compares this structure
with a Lean compiler, a Rust compiler, a C++ product and a library planner.
The chosen responsibilities are implemented at the bounded scopes in
[status](status.md); broader interfaces described here remain design contracts.

Schema/decoder correspondence, checking cost, foreign-call interfaces and
execution granularity need evidence from their actual consumers. Read
[assurance](assurance.md) for what each kind of evidence establishes and
[roadmap](roadmap.md) for the remaining work.
