# What the implementation supports

The native implementation is `.zkc` frontend → Protocol IR (PIR)
(`protocol`, `participant`, `exec`, `physical`) → `zkc.program/0` → the Rust VM and
interpreter with Entry/proof/joint Hosts. Direct MLIR enters the same compiler.
[Specification](spec/README.md) defines contracts; this page records support.
Links identify maintained checks, not a claim that they ran for this revision.
The [EVM verifier target](spec/targets/evm.md) branches from checked closed Exec
to typed EVM operations, Yul and pinned solc bytecode.

## Native selected-control boundary

Registered `protocol.branch`, `protocol.participant_branch` and `data.branch`
retain closed typed arms, captures and selected yields. Native admission checks
all arms, exact role containment and affine usage. Participant `if` and `match`
records bind every capture as an explicit `[local, parent]` row, as participant
loops do, so Copy captures aliased by expanded applications keep distinct
formals and storage; the C++ and Rust byte readers share the
[program byte controls](../common/tests/fixtures/program/bytes.json). Bounded interaction edges,
resource-origin joins, common-input requirement derivation, participant
projection and actual-candidate comparison consume the registered forms.
Participant mathematics outlining and its independent reader recurse through
each Protocol arm, retaining selected control in the native `exec` profile.
Selected `data.branch` mathematics now lowers through recursive computation
recipes into the existing scoped conditional/match execution. Independent readers
check helper expansion, arm-local normalization, demand extraction and actual
scoped recipe bodies. Native fixtures cover nested helpers, enum payloads,
structural products and installed finite work. Program/CPU execution coverage is
recorded by the [selected Math integration tests](../common/tests/protocol/test_selected_math.py).
Selected polynomial observations retain their existing admission restriction.
Checked source-selected Math emission, actual native comparison and CPU
execution are covered by the [selected source tests](../common/tests/protocol/test_selected_source.py).
Common-input requirements remain obligations on entry admission; no public bit,
availability set or native formation result supplies input agreement.
[Native control fixtures](../compiler/test/protocol_control.cpp) exercise this
boundary independently of source emission.
The [native recurrence controls](../compiler/test/common_control_recurrence.cpp)
exercise demanded base/transition induction, separate tag/payload/extent
requirements, nested invocation identity, zero/one paths and exact work
exhaustion. The [source recurrence tests](../compiler/test/language_common_recurrence.cpp)
independently derive source requirements and compare complete inventories with
the emitted native original. Actual completed send components now forward their
sender's immutable subject on the normal continuing path, including private
configuration, helper results and delivered opaque Local/service results.
Congruent total computations and typed projections preserve that agreement
without inventing external common inputs. Nonreceivers, changed values and
distinct opaque occurrences retain their separate subjects; selected joins and
initial/step/zero-trip checks remain in force. This native control coverage adds
no formal correspondence, statement authority or adversarial-honesty result.
The selected-source Host tests also exercise fresh service draws and delivery
inside zero- and multiple-iteration loops, including exact service transitions,
wire counts, carried-result agreement and cleanup.
Recursive schema/component mapping and actual
SDK input admission are covered separately below.

Oracle capacity, observation and storage inventories retain alternative arm
coordinates. The existing oracle realization recipe refuses selected control
with `oracle-realization-control-profile`; native transcript construction,
reverse requests and codecs likewise refuse their unsupported selected Protocol
profiles before mutation. Checked source syntax, emission, structured-source and
application-map carriers retain selected arms. Common-input derivation,
publication and native SDK admission are integrated for the supported profile.
The integrated Program and Rust runtime execute the selected native forms;
independent formal interpretation remains separately owned. This boundary does
not establish complete 4.1 control support through oracle/security realization.
The [contract](spec/ir/control.md#selected-protocol-and-mathematical-regions)
keeps the intended semantics separate from these limitations.

## Current public interfaces

Artifacts use one current schema with exact tags, record shapes and unknown-field
validation. All owned formats remain at version `0`; the foundation changes their
contents together with native producers, readers and fixtures. The
[format policy](development/maintenance.md#format-versions) and
[interface change list](spec/formats/foundation-interfaces.md) define this cutover.
A matching `/0` tag does not establish compatibility between development builds.

The [common-input binding utility](spec/formats/input-bindings.md) checks externally
pinned exact Program/entry inventories and actual value, tag or extent observations.
The SDK strictly requires a canonical inventory on every retained Protocol and
derives mapped requirements from the authenticated selected original and actual
Program. Portable participant checks precede Runner loading; named RunEntry
checks every prepared joint input before issuance. Native publication derives
every closed concrete Protocol inventory; independent reading compares the actual
original through its recursive schema/component map, and source comparison
separately replays the complete source inventories. The
[inventory tests](../compiler/test/common_interface.cpp) cover exact mutations,
typed conditional paths, collection axes and bounded normalization.
Inventory work accounting covers borrowed declaration setup, nested semantic
layout queries, repeated Protocol inventories and native component mapping with
one enclosing allowance, including charges preceding refusals. Natural operations
admit work before normalization; placement and alias helper errors retain their
performed debits. Coherent
fresh compiler/SDK pairing covers Boolean, tag, payload, role permutation and
extent admission, including zero and multiple loop iterations. SDK/package hashes alone cannot establish source
coverage or detect omissions chosen by an attacker editing both package and
context. No new formal authority is claimed.

The [native foundation](spec/ir/native-foundation.md) uses the landed checked
frontend and Common-export retirement. Checked Entry bodies lower directly to
Func/CF, Data operations and explicit Exec outcomes. Host schemas, captures and
control are reconstructed from actual SSA. `HostPlan`, `entry.body`,
`entry.signature`, generic operation-descriptor JSON and per-contract executable
wrappers are removed. Recursive typed layouts use MLIR attribute aliases without
changing semantic depth limits. Native values, field literals, parameters,
source origins, resource identities and aggregate alternatives retain structured
attributes; diagnostic locations provide no semantic authority.

One neutral catalog generates C++/ODS and Rust declarations. Typed catalog
interfaces and kinded attributes drive native type and logical signature
formation. `runtime.binding` retains the complete callable scope/outcome ABI;
`exec.apply` uses the standard call interface and checks exact native agreement.
All represented children, including inactive alternatives, are checked directly.
CPU installation remains separate from logical formation. Internal target
selection and oracle/collection recipes retain native types. Neutral byte
conversion occurs at explicit boundaries through one canonical type exporter;
the old print/parse cache and synthetic Program admission route are removed.
The independent Program and runtime admission/comparison remain mandatory.

`admitStage` performs bounded structural preflight, ordinary MLIR verification
and complete stage admission, including dormant declarations. Module formation
alone is not stage admission. Production and textual pipelines share stage
builders and typed target intent; imports, direct APIs and optimizer ingress and
egress use the same admission. Pass-managed symbol and mathematical facts are
scoped to the stable symbol-table owner with explicit invalidation dependencies;
budgeted semantic queries still account for each request.

Common `ZkcCompiler` and `ZkcTransforms` expose logical proof construction,
checked original/interface admission, closed Exec formation and selected endpoint
closure independently of `ZkcCpuTarget`. CPU compilation/publication and
physical selection live in that target component. Operation-specific native
compilation consumes the checked endpoint candidate while retaining complete
source correspondence records separately. The [endpoint controls](../compiler/test/endpoint_closure.cpp)
cover nested dependencies, producer pruning, metadata and source/candidate
mutation refusal; they do not establish another target's lowering semantics.

The module-owned [interaction view](spec/ir/interactions.md) retains actual
Protocol functions, virtual definitions, applications and symbolic repeats.
Oracle observations, query capacity, batch scheduling and native source-origin
association share this extraction while keeping separate transfer rules.
Successful-continuation analysis interprets
same-participant guards over exact unsigned comparisons at an actual point,
including participant-selected assembly and invariant captures. It checks SSA dominance, preserves zero-trip and
stopped paths, and supplies reached bound queries independently of batching.
Unchecked Booleans, foreign participants, carried initializers and unexpanded
callee guards supply no such evidence. Dynamic query windows use answer-free
discovery, whole-prefix authentication and ordered replay. Their independent
reader checks the actual generated bodies, complete source query order and
failure prefixes. General local success summaries remain outside this profile.

Source, constructed-participant and realization exports share complete
[logical type data](spec/formats/logical-types.md) and typed catalog bindings and
parameters. Source declarations use inherent arrays. The fixed primitive export
profile is catalog data; membership does not supply executable or formal meaning.
The [application map](spec/formats/application-map.md) has native producer and
independent checker APIs and commands for unsimplified preparation. It retains
applications, actual SSA producers, roles, zero-storage ports, nested regions and
dormant definitions. Unsupported rewrite rules refuse rather than gain authority
from auxiliary metadata. Written links remain null without a checked frontend
association. The original is retained through preparation and realization.

`zkc.program/0` bytes, reached invocation order, outcomes, stops, charging and
cleanup keep their existing meanings. The foundation changes internal carriers
and shared export schemas, not the execution backend. Native support and formal
interpretation remain separate. The maintained Lean readers and retained subjects
use the current source, declaration, numerical and participant contracts; their
exact supported profiles and connection theorems are recorded in
[formal support](../lean/docs/support.md). Native admission does not establish
formal correspondence, and these selected connections do not prove the whole
native compiler correct.

| Interface | Contract |
|---|---|
| Executable program | [`zkc.program/0`](spec/formats/program.md), a physical participant program |
| Source Entry | [`zkc.entry/0` and `zkc.language-interface/0`](spec/formats/entry.md#published-entry-package), authenticated source, input/result schemas and selected artifact |
| Joint execution | [`zkc.run/0`](spec/runtime/joint.md), participants, schedule and invocation policy |
| Native proof | [Policy, descriptor, deployment, construction map and invocation binding](spec/formats/proof.md), with `zkc.native-origin/0` occurrences |
| EVM verifier | [`zkc.evm-source/0` and `zkc.evm-artifact/0`](spec/targets/evm.md), canonical `verify(bytes[],bytes,bytes)` ABI and authenticated artifact directory |
| Installed declarations | [`zkc.contract-declarations/0`](compiler/operation-contracts.md), declaration inventory; the language catalog contributes an opaque compiler fingerprint |

Use `zkc run`, `prove` and `verify` for named Entries, and `bundle run`,
`bundle prove` and `bundle verify` for lower-level artifacts. In the C++ SDK,
`Zkc::Compiler` owns common checked construction; `Zkc::CpuTarget` owns native
compilation and packaging, and `Zkc::EvmTarget` owns EVM source lowering.
`Zkc::Driver` composes these APIs and owns CLI parsing. Request `Tools` for installed commands.
See the [SDK reference](../compiler/README.md#components-and-ownership).
Rust package, run and deployment admission take trusted 32-byte SHA-256 pins;
CLI adapters own hexadecimal spelling. Backend service installation uses
`service_support` returning a named `ServiceSupport` signature and reply bound.

## Execution foundation

The EVM foundation uses separate ODS operations, shared typed native origins
and full dialect conversion of the original executable regions. Its checked
layouts expand values and callback state into physical lanes; a final positive
legality check precedes Yul export. It supports installed prime/binomial-extension
arithmetic, checked indices, finite folds/collects and typed structured value transport on
Cancun, Prague or Osaka (the default). One declaration,
[`zkc.evm-target/0`](spec/targets/evm.md#target-declaration), states the forks,
solc pin, verifier ABI, deployment ceilings and revert classes. The compiler,
SDK and CLI read its generated tables, and the deployed runner and harness read
and check the declaration itself. SDK `evm::Limits` and CLI
`compile --target=evm --evm-limits=FILE` select lower ceilings from those rows;
the driver requires a complete inline object and the SDK checks the returned
effective selection before source adoption or artifact reuse. Authored empty transcripts and managed
constructions over a transcript suite whose facts the target realizes, the BLS
Fr and KoalaBear quartic/octic Keccak hash chains among the installed suites,
use the common framed proof format. Managed index requests and native index
blocks, including verifier grinding checks, retain the shared request bytes;
nonce search remains native prover work. The maintained
[Sumcheck project](../examples/projects/sumcheck-keccak/README.md) uses the native
prover and EVM verifier over identical framed proof bytes. The
[deployed tests](../common/tests/evm/README.md) compare complete primitive traces
and failure frontiers. Target source now includes typed single-row Keccak
authentication for installed base/quartic/octic KoalaBear schemes, exact installed
coset roots and points, internal normalized univariate polynomials with Horner
evaluation, and index selection. Common oracle realization retains query history,
anchors, extents, packet deduplication and repeated authentication semantics.
Focused row, polynomial and backend-require controls compare native outcomes
and complete deployed hash traces; malformed ODS controls protect normalization.
The Direct quartic Keccak FRI reference independently replays the shared library.
Its original eight-query scalar fixture needs 122 transitions, above the target's
64-transition ceiling; wide helper signatures also expose solc stack pressure.
Native/reference FRI success does not establish deployed FRI or STARK support.
The small FRI geometry is a closure control, not a security profile.
Every path envelope remains bounded by the declared path ceiling. Other Merkle
schemes, multiproofs, additional curve operations, transcript families and decoders other
than the realized ones and full STARK verifier deployment need additional
target support. Conditional participant completion
in the verifier refuses with `evm.completion`. These checks are bounded
execution evidence, not a formal lowering or cryptographic theorem.

The target-local [BLS G1 adapter](spec/targets/evm.md#bls12-381-g1-adapter)
adds typed add/scale/equality operations and strict native compressed frames
on Prague/Osaka. The explicit
[Keccak Schnorr project](../examples/projects/schnorr-bls-keccak/README.md)
selects the existing generic library and installed BLS Fr suite. Native/deployed
controls cover 37 cases on Prague and Osaka, including valid proofs, false
results and malformed frames, with complete ordered hash and physical
precompile traces. This is bounded execution evidence, not a formal lowering
or security theorem.

`zkc-cpu` composes the five compiled providers through an immutable
`CpuInstallation`. Reduced installations restrict operation, layout, codec,
setup and service support; the compiler's `--cpu-target` applies matching
restrictions without changing physical identities. See the
[CPU guide](../crates/zkc-cpu/README.md#provider-composition).

The [browser engine](../crates/zkc-web/README.md) runs the common SDK and VM
through a bounded promise-based Worker client. Files and project integration
are optional SDK features. Portable and SIMD modules share provider support;
browser numerical execution is inline. Numerical threading, whole-heap memory
accounting and compiled provider pruning are not provided.

Logical variants use Data-owned types; runtime capabilities and exact physical
representation wrappers use Runtime-owned types. Their independent binding
adapters preserve current native descriptors and installation checks. Runtime
also owns the shared `runtime.binding` declaration for logical and physical
ordered execution. Local, Plan and Kernel are not registered dialects. See
[native MLIR value owners](spec/domains/values.md#native-mlir-value-owners).

The Match and outcome branch interfaces support independent mutation of every
edge's forwarded operands, including standard dead-argument elimination and
block merging at the structural level. Host and native execution admission
still require common source captures and explicit scope/outcome structure;
generic CFG rewrites do not by themselves establish executable correspondence.
Numerical schedule comparison reads actual native SCF and CFG associations,
including dormant definitions, without passing through the byte-export model.

Standard Func/CF with explicit Exec outcomes and Runtime scopes is the default
route for source emission, participant preparation, numerical realization,
physical selection, publication and artifact comparison. The reconstruction
reader checks actual conditional, variant and loop bodies, reached instructions,
cleanup, carry transport and logical/represented ports, then independently
admits the native model. A separate record-directed comparator checks current
SSA against admitted native local definitions without reader or emitter replay.
Both checks inspect the complete immediate execution inventory, including
dormant definitions; surrounding protocol associations remain the enclosing
profile's responsibility. Native program records and runtime kernels retain
their own contracts. The [represented arithmetic profile](#represented-arithmetic-development)
adds independently checked word and private-buffer candidates consumed through
physical numerical plans. General writable-buffer programs remain outside it.

Source preparation has one service with polynomial recipe, protocol application
and participant mathematics stages. Numerical recipes emit scoped operations
and checked SCF schedules directly. Finite computations are Algebra expressions
or actual scoped Exec requests, with no separate callable declaration wrapper.
Participant guards stay in Protocol through projection, retaining their owner;
demand formation passes the condition separately from total mathematics and
emits scoped rejection. Source/candidate readers reconstruct actual bodies and
operands rather than relying on producer choices or copied metadata.
See [scope and transfer views](spec/ir/execution.md#runtime-scope-and-transfer-views).

The logical source-scoped API additionally retains ordinary helper calls,
checks their complete acyclic closure and independently compares current actual
callees, occurrences and ordered operands. Source helper return packaging is
distinct from charged native completion; outlined control yields retain their
tick. Plain mathematical functions can share that source table; all are checked
by the mathematical owner with their actual finite-domain and bound premises.
Their equations still need separate source correspondence. Ordinary source
emission and independent comparison now use this scoped profile. Protocol
repeat analysis now reads exact continuing affine roots from actual native
SSA, closed control captures and catalog successor facts. Its summaries preserve
zero-trip behavior, distinguish stopped paths from unknown results, and share
work/depth bounds across calls. Scoped closure admission now checks affine data
use, actual helper/finite callback cycles, match history and exact finite state
roots directly from this view. Scope ownership remains a separate check.
Native control admission no longer inherits the Program JSON nesting limit;
byte export still checks that limit independently. Participant admission now
checks actual SSA data use, service ingress and representations, instance-scoped
message schemas and entry targets directly. Exported value names cannot collide
with service identities. Native Copy capture aliases remain distinct bindings;
export refuses shapes the current byte grammar cannot represent, preserving
resource accounting. The scoped reader now returns only actual SSA/control and
computation occurrences. Byte records are built by an explicit export adapter;
format-local private computation declarations belong to structured export.
Finite dependency summaries retain stable storage across predicate-helper cache
growth. Finite and scoped resource checks count actual cached path heights and
each callback edge once. Selected computation closure preflight bounds nesting
before recursive verification. Native readers and comparison accept ABI-sized
empty call dictionaries while refusing uninterpreted nonempty annotations.
Numerical import avoids cascading symbol substitutions when reusing a binding;
direct realization loads the same dialect dependencies as its pass entry.
Native binding installation checks, physical candidate choices, numerical
recipes and storage permissions inspect native types and kinded attributes.
Neutral declaration conversion occurs only at explicit program boundaries.
Compiler source analyses now read bounded native views of admitted MLIR.
Checked originals retain an emitted or imported module and exact textual
associations, with independent clones for analysis and no shared mutable module
handle. Direct frontend admission transfers the emitted module without a print
and reparse cycle; imported canonical bytes retain their independent admission.
Native source indexing checks the full profile under its own work allowance.
Structured-source publication and per-operation report descriptors are explicit
projections with separate encoding limits. Application
maps, oracle obligations and component provenance no longer decode structured
source JSON. Realization checking accepts typed proposals; native observation,
request counts and event origins use facts derived from the actual-body reader.
External reports compose owned data and retain their strict record readers.

Neutral types and variants now retain structured identities, alternatives and
payloads. Native MLIR and neutral type adapters share policy traversal;
Language layouts, oracle construction and Program admission consume those
structured facts. Portable spelling is required only at explicit interfaces,
reference identities and execution-byte boundaries. Unsigned range inference
covers total wrapping add/subtract, AND and logical right shift, including
actual helper arguments. Bounded-read formation consumes the inferred range
only against an exact extent. Generic optimizer controls check preservation of
reached instructions under CSE, canonicalization and loop-invariant motion;
they do not establish a new executable profile or a formal correspondence.

The structured-source and application-map ingress accepts MLIR assembly or
upstream bytecode. Equal IR in different encodings has different byte identities;
bytecode carries no fabricated original-text offsets. Canonical authenticated
originals remain assembly. The input ceiling and post-parse admission bounds do
not bound every allocation in the upstream parser. Independent runtime and
semantic formats remain `/0`; bytecode does not replace their meaning. See
[compiler serialization boundaries](compiler/serialization.md).

Structured export preserves actual SSA binding positions and checked control.
The independent formal reader must separately adopt the foundation's changed
structured contracts; native checks do not establish that adoption. Preparation and
participant projection retain the complete scoped/mathematical helper and
domain closure, with actual-body preservation checks. Projected local calls
remain Protocol actions and must match their participant's role. Participant
mathematical preparation now expands scoped helpers and creates scoped
calculations with typed mathematical requests and explicit guard outcomes.
Ordinary role components can be joined by `protocol.assemble_roles`; preparation
retains exact ordered role/operand selection and projection selects each role's
own operand without communication. Independent native comparison and the Lean
structured participant normalizer cover the operation. It excludes service,
affine and logical oracle values; it adds no claim of agreement between roles.
The normalization frontier now shares polynomial-generated coefficients across
those scoped calculation cuts through actual participant ports. Its independent
reader checks original data prefixes, exact imports, outcome packaging and
unchanged guard/failure control, while preserving concrete numerical occurrences.
Fully resolved scoped bodies now feed physical port selection, actual-use
conversions, diagonal contraction checks, storage release scheduling, native
publication and independent artifact comparison. The planner indexes semantic
payload definitions and uses across administrative CFG blocks. Captures retain
their producer layout; body-only conversions execute in their reached body.
Resident field/group controls exercise explicit entry and return ABIs, outlined
branch and loop ports, helper expansion, and variant payloads on this path.
Native execution checks retain zero-trip behavior, reached conversion failures,
and the original resource allowances. Aggregate controls also cover nested
sequences, independent variant payloads, inactive payloads without a default
representation, and resident dense arrays and fixed vectors. Their native
fixtures retain complete carrier layouts and reached conversion order. Layout
requests resolve semantic results in their actual outlined owners, excluding
administrative operations with the same diagnostic site.
Mathematical and retained finite requests are realized through this same scoped
path. Scoped callback analysis substitutes exact total pack projections and
removes unused pack descriptors from its private view, retaining scalar work
and the unchanged source for independent comparison. Packed callbacks therefore
participate in bulk selection with the same shape, failure and work controls.
The physical transaction keeps the actual prepared and selected modules
for independent checks of both edges. See the
[source helper profile](spec/ir/execution.md#source-scoped-helper-profile).
Numerical transformation controls now exercise scoped recipe fragments, exact
closures, retained policies, forwarding ports and repeated invocation origins.
Fragment admission rejects data ports on either outer owner; capture mutations
remain checked after coherent scope-entry and outlined-call rewiring.
Structured collection/computation controls retain actual domains, callbacks,
unused row checks and full logical data signatures. Export depth includes the
derived declarations in the emitted graph, with exact boundary controls checked
by the independent Lean reader. The native CFG observer retains separate
operation, definition and reached invocation capacities.

Checked scoped helper expansion substitutes actual SSA bodies, preserves
uncharged helper returns and charged control yields, and normalizes aliased
immutable capture ports together. Its separate reader checks virtual source
substitution against the actual candidate and recovers full occurrence paths.
Exact-limit and overflow controls retain separate 4,096-entry binding and
Func/domain inventories during expansion; profile metadata consumes neither.
Transitive dependency checks keep the scoped substitution, finite, polynomial
recipe and numerical readback consumers separate from producer recognition and
recipe interfaces. Shared callback signatures carry no selected recipe.
Default participant preparation consumes this checked edge before outlining
mathematical demands. Logical participant admission also checks retained finite
callback edges and affine state roots; unresolved requests cannot be published.

Typed `exec.compute` formation resolves actual private source mathematical
helpers or sibling computation entries, checks logical ports, and borrows the
active scope with an explicit outcome. Symbol rewriting and malformed-target
controls cover that boundary. The finite-premise checker maps actual data
operands separately from the scope and retains entry-argument assumptions in
CFG bodies. Mathematical closure, invoking the premise checker and realization
comparison remain consumer duties. Source-closure admission checks actual
mathematical bodies, selected modules, call premises and logical affine
ownership before realization, including malformed dormant definitions. The
shared expanded-helper ceiling counts each actual computation request, even
when repeated requests reuse one helper summary. Source and selected-module
controls retain the oversized refusal and bounded realization cases before
dead mathematics can be erased. Independent closure and recipe controls also
cover changed polynomial operands, shortened arrays, inserted stops and partial
operations, and changed result coordinates. The execution readers refuse
unresolved mathematical requests. This is the sole mathematical invocation.
The Kernel dialect, its registration
and its alternative readers have been removed. Computation-unit admission and
scoped invocation controls cover the retained contracts. See
[mathematical invocation](spec/ir/execution.md#typed-mathematical-invocation).

Retained `exec.fold` and `exec.collect` have checked scoped callback ABIs,
actual domain/capture premise discharge, zero-state outcomes, and scoped
ownership formation. Source-closure admission checks every actual callback and
retains callback dependencies for cycle and control-effect checks, including
history transitions hidden behind finite requests in matches. Multi-block
callbacks remain distinct from single-block
expression views. Internal source adapters construct and independently compare
scoped occurrences, array materialization, product/Unit packing and callback
CFGs with bounded work. These controls isolate adapter correspondence; the
enclosing source checker owns ordinary helper bodies and complete inventory.
Default source emission retains these requests until checked finite
preparation. Ordered execution and supported bulk alternatives both produce
scoped execution. The independent reader checks actual callbacks, complete
domain admission, source policies and fixed implementations.
The scoped source-closure API admits affine fold state only after the shared
native execution analysis checks exact state-root preservation over actual callbacks.
Controls distinguish fresh replacements, exchanged slots, stopped paths, primitive
successors and cached analysis limits. Protocol repeat consumers use that shared
analysis. Scoped vector-reduction controls exercise
checked helper substitution, numerical lowering with pending collections, and
explicit physical selection. They retain large depth, copy and origin workloads;
old phase-state tokens are replaced by transactional source/candidate and shared
account checks. Map consumers now use the shared scoped collection fixture, including
eight native field families, complete malformed/admitted mutation controls,
large formula and wide-capture workloads, cumulative required allowances, affine
repeat helpers and physical pipelines. Optional Ring limits retain ordered
execution; actual retained/generated callback admission remains bounded.
Late-selection consumers now check the retained finite and numerical stages of
physical plans, provider and per-occurrence fallback, explicit callback policies
and implementation pins, admitted physical mutations, cumulative work boundaries
and identity-map capture canonicalization through scoped control. These are
affected-suite checks, not validation of the complete base.
Unresolved requests are refused by
executable extraction. See [ordered finite requests](spec/ir/execution.md#ordered-finite-requests).

`zkc_runtime::vm::Program` owns structurally admitted code independently of a
backend. Loading links one owned backend before entering frames. The internal
VM instance owns complete invocation admission, frame identity and nesting,
installed calls, retained values and budgets. Participant loop frames reuse
typed input layouts retained during admission. Return handoffs carry owned
values and their backing obligation; VM recording snapshots retain preparation
accounting. Primitive value checks also reside in the VM;
`zkc_runtime::interpreter::Runner` owns control evaluation and pending actions.
Hosts use that interpreter for Entry, proof and joint execution.
`zkc-runtime::host::{joint,proof,wire}` owns reusable ordered drivers and framing
without native or kernel dependencies. Runtime-only controls use a separate
backend and Value through joint and proof paths; native integration implements
the closed wire profile. Application identity, setup, public inputs and prepared
computation authority remain in `zkc`. The
[VM contract](spec/runtime/vm.md) defines authority, failure and accounting.

Participant Programs also admit selected Boolean and ordinary-variant arms
through closed `if`/`match` records. Independent C++ and Rust admission checks
all arms; the interpreter enters only the selected frame and retains its actual
resource tuple. Compact joint schedules retain explicit arm scopes and compare
all reached selectors before arm work, including event-free branches; enum tag
agreement supplies no payload agreement. Reports retain actual arm paths.
Source requirement derivation, canonical inventory publication and exact Entry
component binding feed SDK input admission. Generic independent execution
supplies no peer agreement. Selected native transcript request/codec reconstruction explicitly
refuses its unsupported profile; these execution checks establish no formal or
security coverage.

C++ source/function Entry producers and strict Rust readers share recursive
placements, components and complete field metadata. The
[fresh compiler inventory tests](../crates/zkc/tests/common_inventory_compiler.rs)
exercise actual source-derived value, tag and extent requirements through named
CPU runs, including role permutations and zero/multiple loop iterations. The
[fresh Entry component tests](../crates/zkc/tests/entry_components.rs)
execute current C++ packages through Run, Proof and Host, including transport of
a home-constructed sealed witness. These checks establish the supported native
producer/consumer connection; they add no independent formal correspondence.

Logical [numerical units](spec/ir/computation.md) use named `builtin.module` with
`exec.computation` and standard functions. Stage admission checks every retained
definition; the marker alone is not admission evidence. `exec.compute` retains
ordered scoped invocation. Preparation and participant demand lowering form
units; the physical plan retains the mathematical source and actual finite
preparation alongside the selected scoped candidate until independent numerical
and physical checks permit publication. Export receives the resulting physical
program without unresolved mathematical requests.
Normalization and numerical recipe checking consume these standard
functions directly, with separate structural facts and call-specific selection
restrictions.
Existing installed backends execute the resulting operations. The checked physical
schedule records optional binding releases, including conversion temporaries;
materialization performs no lifetime selection. Private numerical schedules use
scoped `scf.while`/`scf.execute_region` loops. The source reader checks their
actual state, callbacks and custody; a separate CFG comparator checks their
consumption before executable publication. Finite recipe, provider and conversion choices share one bounded
search; actual emitted uses identify which eligible occurrences may change.
Explicit requests remain fixed, and semantic comparison failures are terminal.
Retained row-bearing native maps and selected sums use a private
[Tensor/Linalg profile](spec/ir/mathematics.md#structured-tensor-computations)
with exact field scalar regions, upstream map/reduction fusion and CSE/DCE, independent candidate
readback and execution through the current native handlers. The structured
reader and source comparison are in IR Analysis; proposal and optimization are
in Transforms. Numerical pass options preserve representation choices through
copied and textual pipelines. Products use the pointwise tensor stage; their
aggregate remains native. Row-free fills and explicit vector selection remain
outside the tensor profile. The later represented pointwise stage checks private
buffer ownership separately; general tensor and buffer transforms remain outside
these profiles.
Owned [quotient-ring kernels](spec/domains/quotient-rings.md) support canonical
negacyclic arithmetic, exact centered norms and natural-order transforms through
ordered native contracts. Coefficient and evaluation values have distinct kernel
APIs; evaluation operations retain the exact basis. These arithmetic capabilities
do not provide a complete signature verifier. Formal `!poly.quotient<q,n>` values
and source intrinsics retain exact modulus/degree until checked coefficient
realization; helpers may carry them, executable ports and messages may not.

[Prepared quotient matrices](spec/domains/quotient-matrices.md) use immutable
Runtime values and exact chunked RNS reconstruction. Source clients prepare once
and reuse matrices with separately checked digit vectors, including even and
composite protocol moduli. The selected compute-prime profile, declared digit
bound, canonical inputs and current invocation limits are enforced independently
by the native path. This does not implement a signature verifier or a general
formal-matrix rewrite.

Native [numerical calls](spec/runtime/numerical.md) have typed immutable storage
views, private initialized destinations and scoped construction/work limits for
dense vector arithmetic and reductions, matvec/split, BLS table fold and
opening quotients over the
[registered residue fields](spec/domains/values.md#registered-residue-fields).
Weighted sums of selected off-domain column quotients use the same scope
on BN254 Fr and those residue fields.
Compiler-generated pointwise expressions pass
borrowed columns and scalar captures through ordinary installed bindings.
The represented pointwise stage uses upstream vectorization and bufferization,
then checked resident storage plans. It does not emit object code or provide
JIT/AOT engines. These execution boundaries do not establish formal native
correspondence.

## Source and application boundary

The installed `Zkc::Source` and `Zkc::Syntax` components provide the new
[layout syntax](spec/language/layout-syntax.md) without MLIR or Lean. They retain
source bytes, parse headers/bodies under supplied notation environments, recover
incomplete editor buffers and format complete syntax with a reparse check.
`compiler/test/source_syntax.cpp` covers the selected example corpus, notation,
positions, mutations and refusal budgets. The source/syntax installed-consumer
fixture exercises static/shared linkage and Unicode dependency discovery.
The explicit development entry `--source-format=zkc-layout` now connects the
[new syntax to native execution](spec/language/layout-execution.md). It reuses
name/type/role/resource/effect checking, specialization, actual IR comparison and
the Rust Host. Project manifests and explicit SDK and CLI module maps state their
source format, so a `zkc-layout` project builds through `zkc.toml`; the Lean
bridges take a package's format from the SDK's project inspection. Nominal home-module methods, including generic aliases, use the
ordinary invocation binder and resolved mode/effects. Imports do not extend
method eligibility. Protocol methods derive their complete role substitution
from an exact fixed-roster receiver map; legacy direct logical families still
require a unique complete roster. Managed service constructors and methods
resolve through installed catalog declarations in the same index.
Named Math and Local references are accepted at expected static callback
arguments, including inferred/explicit statics, imported/reexported providers and
generic module members. One selected-callable record feeds existing summaries,
effects, finite obligations and declaration specialization, with immutable source
and independent closure witnesses. Runtime function values and callable
descriptor families remain outside this support; no formal correspondence is
claimed for this native unit.
Invocation checking now reconstructs source child values, named destinations,
protocol roles and exact managed-service roots from immutable source occurrences
in every body and callback. Coordinated action/binding swaps and balanced
equal-type record-inspection swaps are rejected; specialization rechecks the
source and preserves its lexical authority and value mapping.
Source replay now inventories reachable control and data binding occurrences
before accepting candidate representations. Missing, duplicate or misplaced
controls and erased or relocated alias definitions refuse, including coordinated
Oracle/Protocol query redirection. Native controls cover one and two aliases,
position aliases, ordinary calls and returns, unused bindings, selected helper
regions and exact reachable stop outcomes. The inventory shares lexical region
mapping and bounded work with existing replay; it adds no formal correspondence.
That relation also checks ordinary control headers, retained repetition maxima,
mandatory continuing control/block result maps and exact root/arm/callback tails,
including Math/Local result inference, named Protocol ports, tuple/Unit/placed
results and mutable carry. Native mutation controls cover omitted maps, redirected
selectors/bounds/counts/returns/yields, omitted joins, stale state and equally
typed captures; selected Host controls exercise distinct branches and
zero/nonzero-trip loops.
Expected snapshots now use authored evaluation events independently of candidate
operation order, including header assignments and eager callback captures.
Scalar decimal replay retains the resolved type and canonical payload, including
unused constants and erased hints/maps. Administrative carriers validate tuple
arity, field and projection types through the same indexed relation for explicit
results, state tuples, direct state and Unit. Native controls cover coordinated
stale-state reordering and malformed literal/carrier mutations. Resolved finite
recipe snapshots retain their eager operand identities separately from ordinary
entry-generation captures, including across nested protocol repetition. Frozen
usage results authenticate exact live state membership even for unused joins,
while consumed states can be restored by continuing source assignments.
These are bounded native checks, not full source-language or formal verification.
The maintained new-syntax Schnorr fixture executes valid and
invalid witnesses, extra unused random draws and reached guards. Optional specs
retain their authored source and resolved protocol attachment, with assurance
reported as open and unresolved. Explicit target acceptance, grouped and anonymous
security requests, and formal site selectors survive written-source export;
every declared postcondition and request remains in the required obligation
inventory. Native checking does not prove them. The ordinary
project/SDK default remains the existing syntax. Shortened implementation
signatures, complete mathematical control, schemes and typed formal projections
remain outside the development execution profile. The integrated
[oracle projection](spec/language/oracles.md) supports custody ports, shape
attributes, ordered delivery/query, holder/shape views and bounded sequences
through checked original comparison. Oracle calls and returns also use the
existing checked component ABI. Virtual definitions and restricted logical
records still need their typed source integration. The FRI-layer and KZG
syntax fixtures exercise design coverage and formatting, not execution or
full FRI/STARK acceptance.

The optional [source LSP](spec/language/authoring.md) provides diagnostics,
symbols, resolved definitions, native type/role hover, visible-name completion
and checked-syntax formatting. Its single worker uses immutable whole-project
generations, bounded queues, explicit cancellation and stale-publication guards.
Imported notation, private bodies and spec additions invalidate the active
analysis. Invalid projects retain recovered syntax and independently valid
semantic facts. Body failures preserve valid neighboring bodies; signature
failures currently prevent global body checking but preserve valid signatures.
Only an error-free project yields executable `CheckedProject`. Persistent
caches, rename, Lean proof actions and production
language cutover remain open.

`entry fn` exposes typed application control; `proof` configures independent
proving and verification. Entry functions statically call numerical helpers,
other Entries, protocol runs and proof operations. Numerical execution retains
the existing computation realization pipeline and VM.
Concrete protocols also expose a default run Entry under their protocol name,
using the same generated Host operation and Entry function path. Explicit generic
selectors such as `Schnorr<G>` close the same path with source-checked static
arguments; no wrapper is required. Generic instances are not enumerated during
discovery. Proof declarations remain explicit.
`zkc.toml` supplies the module/asset map; the CLI discovers the nearest manifest.
Explicit local workspace catalogs select leaf packages alongside path
dependencies, preserve capture identity, and report selected-edge provenance in
`inspect --view=api`. The installed package includes the catalog and library sources.
Batch coset extension is installed on BN254 Fr and the registered residue
fields. It constructs one private column-major output and retains non-base
shifts; shrinking checks each column's actual normalized degree. Compiler,
runtime admission and native signatures independently check the shared declaration.
The single-word domain analysis does not yet transfer flattened batch facts.
Batched coefficient evaluation is installed on the same fields. It shares
one ordered output domain and constructs one private column-major vector;
coefficient blocks may have zero or non-power-of-two height. Shrinking admits
only zero discarded tails. AIR quotient splitting retains source interpolation,
capacity and padding checks before invoking the batch operation once.
Direct coset point evaluation is installed on the same fields, sharing
weights across columns without reconstructing coefficients. It handles on-domain
points and arbitrary evaluation words; neither path proves a degree bound or
authentication. Source controls check independent integer expectations and refusals.

Polynomial opening APIs bind canonical cosets, column batches, descriptors and
accumulators in private checked views; row evaluation derives its point from
the admitted query index. These are mathematical context checks. Column reduction uses one private weighted
quotient result with reusable call-local denominator/prefix arrays. AIR witness
reads select the same core reduction in read order; known reads consume no weights.
Commands accept unique short or qualified Entry names. Execution filters omitted
names by function/proof kind; inspection and compilation require a single Entry.
`new` and `init` create an Entry function with an argument template;
`prepare` creates missing maps while preserving existing values. Manifest-relative
paths supply omitted inputs, proof files and run results. Joint children obtain fresh
sessions unless explicitly configured in the application context. `run --dry-run`,
`prove --dry-run` and `verify --dry-run` share native input validation without
execution. Source execution compiles in memory; pinned package mode is explicit.
The public Rust `project` API owns project/compiler access, path layout and
preparation plans. Commands print human summaries; automation uses `--json`.
`zkc check` reports canonical Entry names and checks definitions without selection; a positional Entry selector also checks closure
and mathematical correspondence. `zkc check` and `compile` accept explicit
[project manifests](language/README.md#project-inputs) or module/asset maps.
Language resolves explicit modules and R1CS/AIR Assets, checks generic libraries
and closes selected Entries. It supports scalar mathematics, Boolean formulas,
nominal products/variants, static parameters, unified file/inline/external modules,
explicit interface conformance, capabilities and
permissions, lexical scopes and patterns, mutable bindings with inferred region
state/captures, statement-scoped participant inference, nested ordered calls,
helper result inference, expression-wide structural type constraints, partial
static arguments with positional or named binding, named value/service arguments,
Unicode 17 NFC names, scoped mathematical operators and paired-delimiter calls
with import activation, explicit fixity and local module bindings, catalog-checked
primitive definitions and a scalar prelude read from catalog declaration rows,
selected Boolean operators in Math, Local and pointwise total Protocol expressions,
total ordinary enum construction with payload availability, inferred usage, catalog
and natural preconditions with explicit contract checking, derived boundary admission, unified data/service arguments,
source rejection with `require`, formal polynomial intrinsics, checked
pointwise `map` of scalar helpers over vectors, general finite reductions,
statically bound scoped Math/Local callbacks with generic apply/forward and
module wrappers, local control,
messages, services, static protocol composition, bounded repetition and conditional completion.
Independent source comparison checks emitted MLIR against checked definitions;
[source semantics](spec/language/README.md) owns exact limits.

Selected Math arms preserve source domain and whole-item origins. Native
mathematical fact extraction forwards immutable `data.branch` captures to their
actual outer operands, so enclosing index-bound premises reach helper calls and
direct reads in either arm and nested selections. Captured constructor results
retain their derived cardinality. Payloads, selected results, branch conditions
and another same-typed container or index supply no implicit bound premise.
Oracle query plans still refuse authored Boolean selection; explicit total
`bool.and`/`bool.or` intrinsics remain eager.

Source checking and closure retain diagnostic work ledgers with exclusive
subphase counters, separately bounded scoped checks and selector work, and
explicit Host child attribution. The source driver publishes `source_work` in
compilation observations and diagnostics. The
[work observation regressions](../compiler/test/language_work_observation.cpp)
cover sums, nested allowances, real checking refusals and child totals;
[driver controls](../compiler/test/language_cli.py) exercise the diagnostic
output. This surface grants no admission or formal evidence. See the
[accounting contract](spec/language/definitions.md#bounds-and-scope).

The frontend uses recorded implementation edges and one declaration index for
source paths, installed methods and provider routes. Invocation-local dependency
and common-control summaries retain exact contexts and caller limits; closed
Entries retain their common-input inventories for publication while native
comparison derives them independently. Independent source witnesses reconstruct
headers, exact construction occurrences, managed query roots and authored lexical
regions. The [construction controls](../compiler/test/language_construction_witness.cpp)
and [region controls](../compiler/test/language_managed_source.cpp) cover candidate
mutations and source compatibility. These checks do not establish a formal
source-correspondence theorem or complete the later language migration.

The total Math operation `multilinear.restrict_prefix` is available through
both `primitive` and `intrinsic` authoring, original structured export and the
strict Lean reader. Its Kernel recipe and native field-family implementation
cover arbitrary vector lengths and points, subject to native resource guards.
The [relation fixture](../compiler/test/fixtures/structured-source/restrict_prefix.zkc)
exercises the operation without migrating a protocol library. The shared
[meaning](spec/domains/polynomials.md#total-vector-prefix-restriction) and
[formal scope](../lean/docs/spec/structured-source.md#shared-mathematical-and-component-meaning)
keep relation shape premises separate from native execution limits.

An authenticated `zkc.entry/0` package retains the original, source interface,
compilation choices, selected artifact and the expression assets the artifact
references. The Host binds named logical inputs and results to the independently
admitted program and checks every reachable asset reference before any
invocation. It trusts compiler publication
for source correspondence; it does not interpret retained MLIR. Maintained
[Schnorr and Sumcheck projects](../examples/projects/README.md) exercise this path.

Rust Entry admission reconstructs exact ordinary Product role intersections,
semantic zero-storage public coverage and indivisible setup-bearing variants.
Supply reconstruction and public classification share a bounded work allowance.
Proof operation admission checks the consumed participant; retained Host calls
can transport typed ordinary values with private constructors, including whole
sealed values under their export policy. External construction and projection
remain restricted. Native closure distinguishes checked Host invocations from
external Entry selection and semantic subject closure. Independent generated
signature validation admits whole typed opaque data while preserving split
ancestor and setup authority. Fresh compiler/SDK controls exercise home-constructed
sealed witnesses through Prove, Verify and Run, including verifier rejection,
empty ordinary fields and external child-admission refusal. These are native
artifact and execution checks, not a formal security correspondence.

Member-generic Math, Local and Protocol contracts compare universally quantified
member binders after owner specialization. Alpha-renamed parameters, associated
domains, roles, services, callback contracts and effects retain one selected
implementation through closure and independent authored replay. Stronger hidden
formation or boundary-admission requirements refuse; unsupported implication is
not delegated to optional formal intent. The [connected 4.1 clients](../compiler/test/fixtures/layout/library-contracts/README.md)
exercise Schnorr, a fixed two-variable Sumcheck/full-table opening control and
distributed linear custody through actual native execution. These controls do
not establish cryptographic security or complete the maintained-library migration.
Protocol interface members use the layout reader; the retiring brace reader
has no new Protocol interface syntax.

Fixed source arrays use static numeric indexing. Private ingress without an
admitted validator and zero-leaf messages refuse. Associated types cannot
introduce member-specific static parameters.
Implicit role remapping, natural equation solving
and inversion of associated types are outside the source profile.
[Scoped computations](spec/language/definitions.md#scoped-computations) use the
ordinary checked Body and type solver. Projection-aware Copy+Drop captures,
mutable snapshots, static scoped captures and lexical module resolution close
to ordinary private helpers with explicit environment inputs. Independent
capture and specialization checks reject mapping and coverage mutations before
source-to-MLIR comparison. Compiler and native tests cover fixed modes, effects,
owner inference, forwarding, aggregate captures and authored evaluation order.
Runtime function values, escaping computations, outer writes and captured
services are unsupported.
[Finite domains](spec/language/definitions.md#finite-domains) support registered
constructors, composed factories, module selection, static helper arguments,
callback captures and nested local/protocol control. Joint closure retains
immutable operand aliases and independent witnesses check closed recipes and
capture layouts. Source checking and native tests cover forwarding, zero trips,
participant availability and specialization mutations. Registered finite folds
and collects now reach retained finite IR through independently checked adapters.
The layout frontend also supports fixed `view def` mode with independently
checked ordinary forwarding and installed Finite descriptor results. Family
identity and complete ordered typed parameter contracts remain separate from
callable mode. The source graph, child edges, sole declaration result,
inference/conformance, specialization, identity and independent replay retain
full contracts. Finite native conversions check the family and one-parameter
arity before extracting an item; native finite semantics are unchanged. Descriptor
aliases cannot enter ordinary types or placed/service ports, including through
zero-length arrays. Authored View replay checks exact constructor graphs,
operands, statics and argument order. The layout finite client reaches actual
Math and Local native consumers; packaged Host controls cover shared/unused
constructors, zero cardinality and repeated admission. Ordinary abstract View
members retain an implicit empty effect contract through generic owner/member
dispatch from Math, Local and scoped bodies. Source replay, exact conformance,
native comparison and packaged Host truth tables cover ordinary View calls in
both operand positions of Protocol `and` and `or`, including methods and Math
callbacks; Local and descriptor operand refusals remain checked. The maintained
library still uses the legacy source adapter until the parent source cutover.
Construction descriptor families, Constraint Views and independent Lean readers
remain separate integration work.
An internal installed structural declaration slice adds exact Product/Sequence
head and six bounded View scheme rows, independent Python/TableGen/Rust catalog
validation and typed projections. Installed shells enter the ordinary frozen
declaration index without a concrete data signature or body. Focused native
checks cover constructor formation, association identity, aliases, visibility,
foreign homonyms, Nat parameters and installation drift. This is not complete
public aggregate or Constraint View support. Parent scheme/fold/closure/native
consumers and strict Lean reader migration remain publication requirements.
The public checked-Type source-term encoder and strict C++/Rust wire readers
support exact structural descriptor products and sequences, including empty
products and distinct unsized/zero extents. Shared producer fixtures and bounded
reader controls cover this codec boundary with unchanged Finite/ordinary bytes
and limits. These checks do not establish structural source-to-native formation,
full protocol acceptance, future Constraint leaf schemas or formal support.
Static natural constructor configuration, callable payloads and heterogeneous
checked descriptor lists are not implemented by the graph foundation; their
actual family formation and consumers remain required.
Native source tests cover ordered and Unit state, mixed state dependencies,
filtered stops, strict zip admission, packed record sequences, repeated calls,
dependent inner ranges and mutable capture snapshots. Fixed source arrays now
adapt through independently checked sequence construction, including records,
empty arrays and Unit items. Source item-provenance checks
now cover callback-local `where item_from(input, domain)`, optional input labels,
arbitrary slots, multiple independent origins, generic restricted forwarding,
named argument order, nested captures and invariant local-region inputs. Native
named callback formation also substitutes selected generic and inherited module
statics throughout the body, including nested callbacks and fixed collection
cardinality. Concrete and abstract selections retain unused/zero-trip formation
and exact data conditions. Both source syntaxes reject bare static arguments on
lexical data, domain and callback bindings with `source.static-argument`. Native
controls include exact normalized module conformance, independent authored
selector reconstruction and mutation refusal. Inner conditions preserve outer
catalog/natural inference. Labels and canonical maps are exposed separately in
declaration inspection; they add no runtime closure or finite IR attributes.
Retained witnesses also check formal callback slots and authored invocation
identities through nested regions. Filtered notation preserves distinct predicate
and term parameter identities at shared written binder spans; source and closure
controls cover nested patterns, captures and dormant call mutations.
Total index literals, static natural index construction and comparisons now
support mathematical ranges and filters through ordinary realization. Total
access now uses exact item/container bounds, declared Math input conditions and
callee-first closure requirements. Native checks independently discharge each
call and finite callback, including equal-extent captures. Closed source checks
cover all retained zip/matrix-view formation and exact fixed collection sizes;
sequence constructor evidence preserves fixed-array lengths across adapters.
Source fact extraction follows aliases, full projections, literal indices,
declared input conditions and results of concrete checked Math helpers. Exact
forwarding preserves identity; unfiltered collection construction preserves
shape through wrappers and record projections without identifying new values.
Result dependency walks are iterative and memoized. Unfiltered finite
collections retain their domain's known count
and leaf extent; filtered collections provide upper counts, with zero also exact.
Direct Math calls to finite definitions remain finite computations at their
call occurrence during specialization, preserving actual range endpoints and
container evidence. The independent specialization reader checks the domain,
callback and capture substitutions. Local declaration formation and ordinary
domain-parameter helper boundaries retain their generic formation requirements.
Collection cardinality can cross those boundaries; successful Local guards,
arbitrary computed scalar results, control-flow joins and loop invariants do
not acquire source summaries.
Fixed field-array output follows the installed BLS12-381.Fr contracts; other
field backends may lack that realization. The [shared libraries](../libraries/core/README.md#finite-computations)
now expose ordered and total folds, collection, explicit combiner modules,
field/group accumulation, filters and materialized vector reducers. Ordinary
collection arguments share one checked conversion at scoped-domain parameters;
matrices require explicit views. Source/native tests exercise records, group
commitments, nonassociative order, nested domains, skipped inverse failures and
reducer failure order. [Finite binders](spec/language/definitions.md#finite-reduction-binders)
now use that same path: Local and total Math targets, filters, independent products,
dependent nesting, aggregate captures and direct protocol/module use. One
lexical binding is selected before body/result inference. Shared source/domain/
scoped witnesses replace the old ring-only extraction checker. Library-owned indexing now uses the same typed callable selection and retained
binding checks. Standard vector, matrix, group, sequence, index and field-array
modules expose total access; checked Local access requires explicit rebinding.
Static source-array projections retain their existing capture paths.
The layout surface uses one `notation` declaration head for all bounded forms,
with each ordinary hole used once in written order. Bare descriptor imports
refuse ambiguous positions or index arities; explicit position/arity selectors
resolve those cases. Filtered and unfiltered reduction forms select independent
ordinary finite consumers. Layout reduction projection uses the existing scoped
callback and ordered product machinery. The public capture format still applies
to every source: scoped layout consumer declarations and View target admission
remain computation-package integration work. Legacy library closures retain the
brace reader. The catalog has no installed scalar exponentiation target for `^`.
The staged parser resolves
notation environments after imports and before bodies. Callable notation uses
ordinary signature constraints and authored evaluation order, with descriptor
arity and scope checked by the independent binding witness. No formal
elaboration-correctness theorem is claimed.

Local effect contracts use `effects(...)` before `where`. Open helper bodies
retain bounded callback dependencies, including forwarding and literal captures;
closure and independent witnesses reconstruct selected effects. Callback ceiling
omission allows the tracked Local universe, while truly abstract Local outputs
require an explicit contract. Local finite admission remains stopping and finite
callbacks remain stop-only. This is compiler effect checking, not a totality or
protocol-security result.

Source/native boundaries retain exact source/public JSON names while encoding
symbols as UTF-8 segment hex and role/setup/case labels as roster ordinals for
ASCII and Unicode alike. Both Entry setup authority and material keys are
translated. Generated Rust bindings use injective UTF-8 escapes and allocated
names, preserving source keys. Artifact and transcript bytes therefore change
even for ASCII source; version `0` retains one current schema and no legacy
readers. The [source/native contract](spec/language/translation.md#source-and-native-names)
and [SDK dependencies](../compiler/README.md#installed-package-discovery) own the
encoding and pinned Unicode/NFC boundary.

Checked public API inspection is available through `inspectPublicAPI` and
`zkc inspect --view=api`. Its compact export graph covers aliases, types and notation
routes; captured source references retain the selected provider and canonical
target. Private field names and associated representations are omitted from
public type contracts. The bounded diagnostic view supplies no linking authority
and changes no source or executable identity. The
[language specification](spec/language/definitions.md) owns its format and limits.

The [written-source AST](spec/language/source-ast.md) is available through
`inspectWrittenSource` and `zkc-compile language-check --source-ast`. It retains
captured and installation syntax before elaboration, including written omissions,
finite binders, inline relations and structural source-claim addresses. UTF-8 spans
and capture/installation identities bind its inputs. It is an input for independent
source correspondence; retaining it does not establish elaboration or remove the
source/exporter trusted links. `inspectSourceBindings` retains local read, call
and assignment associations in written AST coordinates, including shadowing,
combined input order and finite binders. Generated syntax without a written
association is reported explicitly. The remaining elaboration proposals and
their independent correctness checks remain open. `exportSourceCorrespondence`
and `language-check --source-correspondence` join the written syntax, binding
proposals and closed instances to the exact structured unit using its own row
producer. `inspectSourceInstances` retains static substitutions, selected
callbacks, closed domain graphs and callable alias layouts; it does not yet
cover call-edge or scoped-extraction correspondence. The artifact
shares source claims' existing admission association and reports missing source
matches explicitly; its native publication check is not a Lean proof.

The Protocol dialect registers checked [logical oracle kinds and handle
carriers](spec/ir/protocols.md#logical-oracle-kinds-and-handles), including sized
tables and bounded handle sequences. They have no ordinary native codec.
Common IR formation checks ordered oracle sends/queries, exact kind associations,
role availability, kind-owned named dimensions, initially bound shapes through
recurrence edges and static refinement erasure. Sends carry the exact dimension
list; input and virtual bounds name every dynamic dimension. Shape maps and
reads have the same strict independent wire contract. Invalid queries are
enforced at the occurrence against the actual stored shape by the checked
realization. Checked preparation remaps oracle roles
through applications and preserves sends/queries under upstream CSE. Projection
refuses unresolved oracle events before publishing participants. Holder-only contents and bounded,
append-only sequences preserve role restrictions, dynamic anchors and ordered
bounds failures through checked preparation. Virtual query declarations check
answer-independent position maps, closed total helpers, actual polynomial bounds,
explicit admissibility references and fresh occurrence anchors. Their generated
condition templates and ordered query footprints have native export/check
commands. The independent Lean derivation is supplied for Lean-owned integration,
with the logical wire reader and recursive handle exclusion. The main Lean
profile does not yet accept these oracle rows or the new assembly operation.
These proposals retain exact occurrences and actual operands; they do
not discharge their predicates. A conservative scheduling analysis reads actual
prepared bodies and role substitution, separates participant-local stops, and
summarizes counted repetitions without unrolling. It identifies a possible query
before a later random-service query. The requested `after-final-draw` policy is
now checked for every logical query owner, both during emission and independent
readback against the frozen source. It includes index and field draws, keeps
participant continuations separate and uses one bounded analysis budget. This
permits authentication after the last draw. Authentication granularity is a
separate requested policy. Checked atomic blocks traverse consecutive dynamic
base and virtual queries through answer-free discovery. Unknown positions remain
eligible. Runtime discovery retains the valid request prefix at a failed domain
check; source barriers end the static batch. The controller retains every logical
query, authenticates the complete response prefix, then replays the source answers
and any pending domain failure in order. It does not authorize
cross-guard sharing, omitted siblings or a different refusal order. A formal
simulation theorem remains a separate obligation. Private
anchor-storage planning retains fresh constructor/instance references, actual
repeat coordinates and role-specific payloads as ordinary sequences and records.
Independent readers check generated append allocations and reference-tagged
lookups, including actual SSA inputs and outcome propagation. Native controls
exercise fresh instances, equal payloads, empty tables and invalid references.
Pure virtual-query lowering emits total position and answer functions; its
independent reader checks actual helper bodies and every ordered child query,
including unused answers. Structural query capacity follows prepared SSA,
loop carries and handle sequences, preserving duplicate queries and zero-trip
alternatives. Exact uniform repeat counts tighten declared maxima; unknown or
differing participant components do not. The same bounded scalar observation
serves observation ordering and successful continuations without erasing
checks. Overflow and analysis work limits refuse compilation. The
private table continuation controller now emits ordinary scoped control over
actual anchors, with explicit suspension, typed answers and bounded advancement.
Its independent actual-body reader covers the complete transition closure.
Exact request counts are derived from actual child anchors at construction and
stored in the same immutable record. Independent count-body checks preserve
query multiplicity without evaluating domains or answers. Local evaluation requires custody of every base table; a Merkle receiver has no
local evaluator. The common-stage realization connects those
primitives to actual root bindings, deliveries, virtual constructions, bounded
handle sequences and queries. It threads each role's immutable stores through
common repeats and checks complete generated SSA, local bodies and declaration
custody against a source-derived recipe. Root input components remain distinct;
realization does not assert their equality. Its current integration profile covers
every prepared entry, including paired oracle results. Each oracle entry owns independent
stores and checked helpers; ordinary siblings retain their exact bodies. Shared
virtual declarations leave only after all entries are converted, and the reader
checks the complete entry and generated-declaration inventories. Named shape views read the actual record.
Holder contents use a custody-specific controller, so unrelated received commitments
cannot disable held data or expose another party's data. Base contents return stored
values; virtual contents materialize at demand through the same ordered query
controller, under the retained admissibility obligation. Component views preserve the
actual reference through checked rebindings without fresh allocation or eager
materialization. Independent readers share one immutable formation/execution view
within each check; mutations always require a fresh check. Returned oracle results
keep their original reference positions and append mapped immutable stores only at
their receiving roles. Aliases share support stores; nested calls and recurrence
retain actual anchors and final store snapshots. These private interface maps do
not enable cross-entry graph import. Logical anchor-clause interpretation remains
pending; the supported Merkle communication profile is described below.
The private realization owner consumes a prepared source, validates the complete
serialized record against both modules and retains the frozen pair. Inspection
returns independent clones; changed snapshots do not inherit checked authority.
Joint run and proof compilation consume this same owner before projection and
keep the complete edge in the final Compilation. Native scheduling reads the
represented common interface. Proof construction independently checks the
realization and any reconstructed verifier requests; it has no second oracle
realizer.
Ordinary modules pass through an exact identity edge with an empty oracle inventory. The independently checked table-read primitive
stops before an out-of-domain read for field, group, index and sequence-backed
rows. Its generated clients enter the physical pipeline; native controls check
actual row counts and observable prefixes when a later query fails. Logical
claim transport and the independent semantic realization bridge remain pending.
Private Merkle helpers now compile ordinary scoped position mapping, commit
preparation, opening and guarded answer selection. The independent reader checks
actual helper bodies, exact field/scheme signatures, grouping, leaf permutation,
shape and query guards. Native primitive controls cover all four grouping/order
combinations, KoalaBear quartic Poseidon2 openings, invalid shapes/queries and
hostile root/row/proof delivery. Common realization now accepts externally
requested per-root schemes/layouts and uses these helpers for root construction.
It checks holder Data, delivers only the selected commitment, retains private
opening state and binds receiver shape to the stored root. Dynamic input roots
append explicit receiver-owned shape ports; fixed extents need no extra input.
The record reader rederives these associations under the caller's requested
policy. Native controls exercise fixed/dynamic input/send roots, independent
receiver shapes and exact antipodal root bytes. Immediate receiver queries now
suspend, exchange actual constructor/instance/position requests with one holder, authenticate
complete rows against the suspended anchor's root and expected shape, then resume
that exact continuation. The profile admits multiple remote base constructors at
one holder, including different answer kinds and selected schemes, multiple
instances and recurrent virtual ancestors. Closed response variants are checked
against the suspended constructor before authentication. With virtuals, the
queried handle must already be available at both roles so no future-count message
is invented. The [record contract](spec/formats/oracle-realization.md#common-opening-communication)
specifies this capability boundary. Native controls cover input/send queries,
every valid position, corrupted requests/roots/rows/proofs, duplicate and unused
openings, equal-typed constructor substitutions, heterogeneous scheme dispatch,
and trailing zero-query domain failures. Dynamic virtual packets preserve exact
constructor, instance, shape, position and response alternatives. Mixed
local/remote or multi-holder routing remains outside this communication profile.
The private whole-stage reader consumes a version-zero
[realization record](spec/formats/oracle-realization.md), the prepared original
and the actual candidate. It reads independently parsed candidates, checks exact
pure helper recipes, and rederives interfaces, stores and symbolic generation
slots. Logical input/result pairings use Protocol admission's shared typed reader;
original anchor/data ports, kinds and role families remain distinct from native
representations and their support stores. The same Protocol owner supplies typed
contracts, distinguishing anchor selectors from role components and retaining
continuation residuals and exact named target selections. The realization record
rederives the complete clause inventory, including anchor input/output clauses,
continuation residuals and selected targets. Those annotations remain on the
frozen original, not on the candidate's changed signature. Controls distinguish
logical target changes even when native code is identical, and refuse clauses
inserted into the native candidate. This does not yet interpret logical anchor
predicates on native representations. The record is rechecked at the native publication boundary; possession of its
bytes grants no authority. It is not a Lean simulation.
Empty sequence observations need no allocated anchor. Unreachable queries and
shape views have a complete refusing controller without an invented store;
indexing still stops at its original occurrence and preserves earlier delivery.
Controller roles must belong to the original entry roster. Native proof
publication retains generated origin associations, selected schemes/layouts and
the independently checked request-reconstruction relation.

Common oracle ports pair actual holder data and receiver handles through inputs,
returns and applications, with explicit shapes and independent preparation checks.
The native [structured exporter](spec/formats/structured-source.md#logical-oracle-vocabulary)
and independent wire vocabulary retain kinds, paired ports, virtual bodies,
query order, shapes and sequence bounds. Formal semantic admission still refuses
the oracle profile; decoding does not extend participant soundness. Native
anchor contract selectors retain the associated logical data without a
participant read, including selected logical proof statements. Source whole-port
selectors infer this association and retain the complete Data schema; executable
statement projection and formal semantic consumers still refuse the profile. Source
kind/handle aliases, static kind parameters, forward associated types and closed
logical layouts are checked, including specialization and ordinary-data boundary
refusals. Source oracle ports retain their explicit holder, receivers and static
maximum through paired input, call and return elaboration. The independent
source interface readers check logical kind descriptors, restricted record and
sequence metadata, exact component slot counts and actual input pairs. Native
Entry binding accepts transparent distributed roots made entirely of admitted
ordinary fields through exact field-and-role selections. Units and empty products
retain supply obligations independently of native slots. Selected public fields
expand to the existing flat native proof indices. Private or sealed assembly,
custody, and unprovided handles or anchors refuse. Setup-key selections preserve
ordinary siblings. The [component boundary controls](../compiler/test/language_entry_components.cpp)
and [source/native comparisons](../compiler/test/language_entry_components_translation.cpp)
cover these rules; [fresh source fixtures](../compiler/test/fixtures/entry-components/README.md)
support independent Rust Run, proof and generated Host-family checks. Public
classification and availability do not establish common-value agreement.
No closure claims external supply: the SDK's Entry admission judges it per
operation and supply mode, so Verify admits a proof whose sealed prover witness
it never consumes. Source correspondence checks the complete role substitution
and result mapping. These native checks establish no Lean correspondence.
Protocol rosters and record role telescopes are separate contracts with
separate catalog limits, `protocol.roles` and `record.roles`, both 1,024 roles.
The source checker refuses a longer roster or telescope, including a
role-abstract alias, with its own `source.limit` diagnostic, and the C++ and
Rust interface readers each refuse a longer roster or schema telescope by its
own limit ([role bound controls](../compiler/test/language_role_bounds.cpp)).
Both readers keep a nominal record's role arguments in telescope order. The
Rust supply reconstruction decides role membership by schema category, through
one sorted index of each telescope substitution, so a permuted telescope of any
length supplies each field at its substituted role. The structured-source
export accepts the full `protocol.roles` roster within its 1 MiB file ceiling
and refuses a larger publication with `structured-source-limit` "publication
exceeds 1 MiB"; its measured roster profile is the
[structured-source publication row](spec/contracts.md#current-producers-and-consumers)
([structured-source controls](../compiler/test/structured_source.py)).
Application maps, oracle obligations, source correspondence and source claims
read the exporter's source view, so they accept the same rosters and refuse a
subject that exceeds only that ceiling
([contract register](spec/contracts.md#current-producers-and-consumers)).
The independent Lean structured reader accepts rosters through the same
`protocol.roles` bound of 1,024 and rejects the next value in both decoding
and semantic admission ([formal reader status](spec/contracts.md#formal-reader-status)). Retained
declaration telescopes accept up to `record.roles` names, and their
participant lists and placements up to `protocol.roles`; product arguments keep
telescope order.
Published schema identities, custody slots and nominal descriptor preimages
bind each nominal's defining source authority
([nominal authority](spec/language/definitions.md#nominal-authority)): equal
paths from different library bytes, a changed private dependency and a comment
edit in the defining closure change them, while an unrelated client declaration
does not, and lookup keys, instance symbols and companion keys stay unchanged
([transport controls](../compiler/test/language_record_source_transport.cpp)).
Across every maintained package and compiler fixture the largest canonical key
is 398 bytes, at most 202 bytes longer than its lookup key, against the
131,072-byte preimage bound.
The source correspondence export publishes emission's record of every generated
definition, with its purpose, part and origins, and one occurrence row per
published site with its written nodes; the producer refuses a definition row
outside the instance and generated inventory
([correspondence controls](../compiler/test/source_correspondence.cpp)).
Application maps take that correspondence with `--source-correspondence`:
each root and expansion gets the written link of its occurrence, null for an
occurrence with zero or several nodes, and the check reports the links as
conditional on the supplied bytes, or checked when the checked original's own
export is those bytes
([application-map controls](../compiler/test/application_map.cpp)).
Generated Entry families walk their roster once per phase and each port only at
its placed roles, so a trivial 1,024-role Protocol closes and publishes its
interface within the 32,000,000-unit phase work ceiling, with work growing
linearly in roles ([roster capacity controls](../compiler/test/language_roster_capacity.cpp)).
Work limits and output-size limits are separate: an admitted roster size does
not guarantee that every program of that size fits every output budget. The
generated Host package of a direct Protocol selection restates its role-indexed
families at each signature, block argument and child deployment; its carrier
node ceiling admits the full roster
([Host control artifact](spec/formats/entry.md#host-control-artifact)). Its Host
structure validation needs more interface work than the default allowance
([Host allowances](spec/runtime/capacity.md#host-allowances)), so a Rust Host
admits it by raising its interface work selection within the maximum, and the
CLI by `--interface-limits`; under the default it refuses with
`entry-interface-work-limit`. A distributed record's fields are expanded once per instance and
each placed role visits only the fields placed at it, so a 1,024-role record
with one field per role checks in about 16.9 million units, growing linearly
with its fields. Mathematical participant projection separately bounds roles
times SSA nodes per common body ([limits](spec/ir/limits.md)). The common-input
inventory has its own frontend-owned bounds, refused with `source.limit`
"common inventory limit exceeded" ([Entry carrier](spec/formats/entry.md)).
The rosters each bound admits, including where mathematical admission's
common-control allowance refuses before the inventory limit, are the measured
profiles of their
[register rows](spec/contracts.md#current-producers-and-consumers).
Source send/query/data/rows/refinement actions preserve the explicit holder,
ordered query events and packed answer layouts through independent comparison.
Layout role assembly explicitly selects existing components of ordinary shared
data. It lowers to the IR-owned assembly operation and participates in actual
source comparison, role substitution and participant projection. Unsupported
expression role suffixes refuse instead of being ignored.
Checked oracle inspection exposes one bounded `oracle-admissibility` companion
address for the complete generated Formula, retaining authored clauses and
generated source bounds. Closed source instances retain template/instance lookup
addresses and every construction's typed actual substitution, custody and nested
body path, independently of optional security selection. These unresolved
occurrences are checking proposals; lookup does not supply proof evidence or
extend formal oracle admission. See the [companion contract](spec/language/companions.md#virtual-oracle-admissibility).
Bounded source sequences retain explicit families, persistent loop state and
dynamic selected anchors. Both explicitly selected source formats check virtual
definitions and instantiations through one typed query plan; lowering and
independent comparison retain total maps, ordered queries, shapes and predicates.
Checked native realization implements the admitted communication profile above.
Admissibility proposals still require independent semantic discharge; formation
and native execution do not establish those predicates or a security theorem.

Checked notation inspection is available through
`inspectNotations` with `NotationInspectionOptions.includePrivate` and
`includeInstallation`, and `zkc inspect --view=notations` with `--notation-private` and
`--notation-installation`. The version-0 diagnostic view covers descriptors,
bindings, scopes and occurrences, with private/local data hidden by default and
installation data opt-in. [Notation limits](spec/language/notation.md#bounds)
set 4096 descriptor keys per environment including fixed Boolean descriptors,
64 delimiter holes and 8 MiB output; lowered SDK limits are rechecked on retained
projects. The separate layout authoring service uses retained syntax and typed
queries; this inspection artifact itself does not authorize source rewriting.

The [distributed record source contract](spec/language/records.md) has focused
[inference and capture controls](../compiler/test/language_record_inference.cpp)
for nested alias category admission, constructor field evidence, structural role
equations including empty arrays, receiver ambiguity and projected repeat
captures. These checked-source controls do not establish complete native record
transport, external ingress, Entry selection or formal-consumer support.
The [distributed succession controls](../compiler/test/language_distributed_succession.cpp)
exercise home-authorized consuming inspection and repacking through closed source,
native originals, independently decoded interfaces, actual-candidate comparison
and CPU Run compilation. [Native bundle execution](../common/tests/protocol/test_distributed_succession.py)
checks scalar results at zero, one and multiple trips with simplification enabled
and disabled, without fabricated resource ingress. Function Entry Host schema
support is covered separately by the fresh Entry component tests above.
Fixed-roster fragments retain exact roots across helper
calls and existing repeats, including zero trips, private/sealed payloads and
non-identity role maps. Consume plus fresh construction remains an invalid
repeat successor. Source-selected control integration and independent formal
resource-unit consumption remain separate work.

Source Entry originals use checked Func/CF control with explicit Data/Exec
boundaries. Fallible operations expose return-or-stop outcomes; their independent
reader checks actual edges, carried values and terminal propagation. The
[table relation library](../libraries/relations/table/README.md) supplies exact
finite membership and indexed-read consumers through the current VM, including
masks and duplicate/empty cases. Its AIR reciprocal control is a verifier-equation
comparison, not a new lookup proof system. The independent Lean evaluator laws
do not establish a native correspondence theorem. The actual plain
CheckMembership artifacts also have checked aggregate preparation and
constructed-model completeness and deterministic rejection proofs. Their
explicit resource bounds and remaining native/codec boundary are recorded in
[formal support](../lean/docs/support.md). The structured Lean
import admits the complete table subjects, including nominal queries and
finite-fold realizations. Exact retained formula laws state the full Boolean
result under reached length bounds and exhaustion otherwise; the
[formal scope](../lean/docs/spec/table-relations.md) separates these source-model
laws from native execution correspondence.

Relation and target/input/output/continuation clauses state intent; declarations
alone add no runtime guard, satisfaction fact or security theorem.
Original PIR retains all closed declaration contracts and exact relation
formula references. Native verification checks ownership, complete Math ABI,
port types and roles, clause shapes and agreement of an entry statement with
retained targets. Source proof statements retain the exact selected target name;
its owned clause supplies the decision role. The logical source interface
independently checks that selection against the verifier, and native proof
deployment checks the recovered decision role against its validator.
The version-0 [structured export](spec/formats/structured-source.md)
includes formula links and one contract-table row for every protocol, regardless
of the selected Entry. Application expansion retains declaration metadata;
participant projection erases contracts, formula links and selected-target
references explicitly. This adds
no runtime predicate evaluation or proof transport through those transforms.

Generic opaque relations retain canonical ordered typed static arguments in
closure, native declarations, interface comparison, the strict Rust Entry
interface reader and structured export,
including unused parameters. Equal closed identities must agree on signature
and purposes. Lean's explicit opaque registry fixes a family's typed
instantiation before evidence and supplies the exact registered meanings to
uniform and domain-indexed contract consumers. Focused controls cover two field
domains, distinct natural arguments, aliases and refusal mutations. This is a
generic boundary; Stage3 GKR and proximity callers still need their family
entries, integration and protocol-specific theorems.

## Foundation capability map

| Capability | Support and boundary |
|---|---|
| Numerical scheduling | [Numerical computation](spec/ir/computation.md) retains the mathematical subject and checks a private standard SCF loop schedule before scoped execution. Explicit collect–fold fusion supports total field-vector/field-sequence producers and element or same-position indexed consumers; unsupported observations retain materialization. Nominal values, domain admission and ordered state are checked independently. No vectorized schedule, writable-buffer ABI or new VM instruction is implied. |
| Scalar, collection and polynomial mathematics | Nominal Algebra field/group vectors, indices, field matrices and field arrays, with ordered `data.array_from_elements` packing. A shared collection interface reports structure without granting finite, mathematical, Copy/Drop or wire admission; shape evidence retains the logical family. Source syntax, logical binding spellings and native codecs retain their meanings; builtin tensors have no compatibility alias. Total expressions and checked realization recipes; [structured mathematics](compiler/mathematics.md). Kernel installation alone does not supply a mathematical recipe. |
| Group identity | Total `intrinsic<G>("curve.identity")`, Algebra identity and independently checked native recipe. Dalek Ristretto255 and prime-order Edwards25519; arkworks BLS12-381 G1/G2/GT and BN254 G1/G2/GT, including multiplicative-one GT. Empty MSM identity is checked for the six installed dense group families; [contract](spec/domains/values.md#group-identity). No native proof claim. |
| Shared expression evaluation | Captured [Ring and Bundle terms](spec/language/definitions.md#asset-domains-and-projections), derived static dimensions, retained Entry assets and independent Host preflight. [Checked structural sharing](spec/domains/ring-expressions.md#structural-sharing) preserves ordered substitution and read obligations. The [generic Sumcheck library](../libraries/protocols/polynomial/sumcheck/README.md) derives its width and degree from its Ring parameter; it remains a public-table client without a PCS or native security theorem. |
| Source clients of imported AIR | The [imported AIR client](../common/tests/fixtures/projects/imported-air/README.md) checks actual trace, configuration and public inputs. The [AIR STARK client](../common/tests/fixtures/projects/air-stark/README.md) adds base-field trace commitments, scoped extension-field quotient chunks, OOD/DEEP equations and FRI through ordinary source libraries and separate proof Hosts. The single-table profile covers one present table's assertions; the three-table profile adds whole-Bundle Boolean multisets and signed field balance through LogUp. Security reductions for both remain separate work. |
| Pointwise vector maps | Source `map` applies one static scalar `math fn` over installed field vectors through [checked numerical realization](spec/ir/protocols.md#checked-pointwise-maps): complete domain admission first, with bulk and ordered scoped alternatives. A common semantic reader independently interprets source and candidate payloads, admitting sharing and commuted field arithmetic; helper calls are interpreted from the original source and installed contract laws remain a shared foundation. Shape mismatches are backend failures (`rejected:require`); optional extraction of field constants, addition, subtraction and multiplication obeys Ring depth 1,024; other admitted callbacks retain ordered execution. The [KoalaBear/Ext8/Ext4 comparison](../common/tests/kernels/test_pointwise_polynomials.py) checks maps, Ring rows and coefficients, and coset kernels against integer arithmetic, including the off-domain interpolation distinction. Installed numerical expression calls support map, sum and product over borrowed columns and scalar captures; bulk vector alternatives remain available. No first-class function value or foreign memory ABI is introduced. |
| Finite vector reductions | [Source binders](spec/language/definitions.md#finite-reduction-binders) use general scoped consumers and finite IR. Arbitrary vector reducers collect first and call once. Native `vector.product` has empty identity one across the installed field families, with independent C++/Rust admission and normal resource charges. The default scoped route retains the collection and reducer. Default-false [collection/native-sum fusion](spec/ir/protocols.md#optional-vector-reduction-fusion) selects dot or summed numerical expressions on actual scoped occurrences, independently of finite bulk selection. Every original domain guard remains ordered, including unused rows. The independent reader checks the original callback, actual scalar result and reducer occurrence; explicit sum selections remain fixed. Physical alternatives retain checked map/sum or ordered collection endpoints. The migrated public-coin consumer distinguishes all four finite/vector policy combinations in emitted artifacts. These checks establish values and ordered shape refusals under sufficient resources, without claiming equal exhaustion or a memory bound. The scalar Lean bridge does not cover vector-map/reduction correctness. |
| Mathematical shape and bounds | A shared MLIR-free [fact kernel](spec/domains/mathematical-facts.md) supplies exact origin/axis equality, strict bounds and exact/upper cardinalities. Independent source and SSA adapters replace duplicate closure rules. Helper observations are scoped to immutable symbol closures, with explicit rebuild and pass-manager invalidation controls. Nested work is cumulative and distinguishes absence from capacity. Source symbolic naturals retain their interpretation; guards and nominal types remain unchanged. Core scope intersection is available, while production reached-guard and loop-invariant propagation remain unsupported. |
| General finite IR | [Typed domains and total/scoped fold and collect](spec/ir/finite.md) retain static helpers, complete entry admission, exact bound provenance and state dependency closure. Declaration-owned laws, structural SSA views, separate transient equation matches and shared producer emission support checked loop fallback, native sum/product/dot/MSM, elementwise fields and sum/product reductions of accumulator-independent pointwise field expressions. Selected matrix rows and columns use scalar contractions; admitted nested collections use one whole matvec, preserving empty-outer admission. Total callbacks expose ordinary helper calls and fixed pack/projection pairs remaining after canonicalization before optional bulk selection, while retaining the source of that selection for comparison. Nested indexed helpers preserve callback extent/bound premises and exact positional argument identities, including selected matrix axes. Independent readers check actual candidates, including checked original-helper normalization for total finite recipes and `exec.compute`. Bounded DAG sizing and a per-callback structural ceiling preserve later small opportunities without refunding spent work. Optional lane or payload-comparison capacity retains checked ordered fallback; required-reader exhaustion is diagnosed separately. Checked candidate publication is shared. Opt-in decision records distinguish missing evidence, actual capacity, policy and recipe restrictions, ordered retries and nested publication boundaries; preparation and total Math lowering also expose remarks and IR dumps. These observations supply no checking evidence. Generic canonicalization/CSE preserve domain admission. [Handwritten controls](../compiler/test/fixtures/finite/README.md) cover mutations, failures and 2^17 field workloads. Full fixed-array/matrix fallback additionally requires the native checked-access contracts; the source frontend now uses checked adapters into this IR. No Lean-to-native bridge is claimed. |
| Calls, roles and control | Static application, role projection, structured local control, nested repetition and [conditional completion](compiler/control.md). General dynamic protocol composition remains open. |
| Structured values | Products, alternatives, extents, checked indexing and [nested immutable data](compiler/mathematics.md), including independently shaped matrices; source sequence elements include contextually packed records, tuples, source arrays and empty products, with explicit packing/unpacking and source comparison; affine and non-Drop elements are excluded. Persistent sequence storage and retained validation support default-budget scoped collection of 16,384 indices and 8,192 two-index records in maintained controls. Whole-value encoding has a separate peak-storage limit; a collection that executes locally can exceed it when exported. |
| Restricted records | Explicit linear/affine ordinary and fixed-roster distributed wrappers retain nominal native custody even with empty or entirely Copy/Drop payloads. Consuming home-authorized inspection and repacking preserve every original fragment across helpers and existing zero-trip repeats, with exact nominal/static and placed payload identity; independent source/native comparison checks actual fragment operands. Source-selected control integration remains separate. Structured native export retains typed Slot bindings; the independent formal consumer admits exact-slot local custody under its closed interpretation. Runtime ledger freshness and nested-frame correspondence remain separate obligations. |
| Affine resources and services | Scoped helpers use the shared native execution exact-origin analysis through the Protocol adapter. Directly authored scoped controls and fresh native bundles cover exact roots, state successors, participant-local stops, resource custody, entry service aliases and failure cleanup; [resource origins](compiler/resource-origins.md). Equal roots do not prove equal state or independent randomness. |
| FRI source library | [Binary FRI](../examples/projects/fri/README.md) has one logical `Commit` and private checker shared by `Query`, `QueryAssociated`, `ScalarLowDegree` and `BlockLowDegree`. Commitment state contains no positions; an explicit scalar or product sampler and checked binding produce query state before opening verification. Its private state retains bounded actual/virtual handle sequences and exact coset geometry. Terminal coefficients have exact length after checked padding, with strict degree below `2^(TerminalLog+Rounds)`. [Same-source execution tests](../common/tests/protocol/test_fri_realizations.py) select clear tables, quartic Poseidon2 individual leaves and quartic Keccak paired/reversed leaves while preserving the retained source and interface. Authentication packets preserve all logical child reads and verify complete selected leaves. The AIR caller consumes the authenticated positions and initial values. An independent Lean model of its verifier with ideal commitments is [complete on codewords and has a round-by-round soundness theorem](../lean/docs/spec/fri-security.md), with interactive bounds in the unique-decoding regime and up to the cube-root proximity radius `1 - (ρ + η)^(1/3)`, also stated over the verifier's residual processes, and transferred to a Fiat–Shamir bound for adaptively chosen initial words with one key for the query block, with [commitments read in the clear](../lean/docs/spec/fri-security.md#fiatshamir-transfer) and with [words committed](../lean/docs/spec/fri-security.md#committed-words) by Merkle trees with one field element per hashed leaf, in one random oracle with the hash calls. The committed bound covers acceptance together with the initial word being far from the code for the extraction at a verifier checkpoint, completed with zero at the entries the extraction misses. The model targets an independently transcribed FRI verifier; correspondence to the current shared source and its compiled code is not established. The implication from an application's bad event to that checkpoint event, the installed schemes' leaf encoding (tag, codec, width and height) and the source's sequential position draws remain separate obligations. |
| Pairing groups | BN254 and BLS12-381 each install G1, G2 and a prime-order target with group arithmetic, `pairing.check`, `pairing.apply`, canonical compressed codecs and native frames; [contract](spec/domains/values.md#pairing-field-capabilities). BLS12-381 G2 uses the 96-byte compressed encoding of the Ethereum consensus specifications. Independent arkworks comparisons and Ethereum ceremony points check arithmetic and encodings; no native adequacy proof. |
| Resident BLS12-381 provider | `blst/resident/` scalar, vector, G1/G2 and pairing bindings consume typed `blst/fr`, `blst/g1` and `blst/g2` ports. [Automatic Target preferences](compiler/representation.md#resident-providers) select G2 scaling and pairing checks; canonical ports and Contracts defaults remain Arkworks. Direct conversions are separate reached calls. Complete nested sequences, variants, resident field arrays and fixed vectors retain selected children; fixed vectors are local-only. Canonical selected codecs preserve existing encodings. Known variable-time MSM requires trusted execution permission. [Provider scope and resource boundary](../crates/zkc-kernels/README.md#alternative-bls12-381-provider); no resident GT/PCS output or whole-runtime timing guarantee. |
| Resident BN254 provider | Explicit `halo2curves-axiom/resident/` field/vector, G1/G2, MSM and `pairing.check` bindings consume six typed flat ports at `halo2curves-axiom/bn254.fr`, `/bn254.g1` and `/bn254.g2`. Native and compiler author positive operation inventories independently. Checked mathematical-byte conversions preserve canonical ports and BN254 codecs, including readable JSON. MSM requires variable-time authority for operands `[0,1]`; pairing preparation is invocation-local with kernel work/workspace admission. No automatic Target preference, Halo GT/PCS/FFT/matrix/field-array route, recoverable upstream OOM claim or whole-runtime timing guarantee. Provider selection uses existing physical proposals; compiled source controls cover canonical, resident, mixed-provider, G2 and bulk paths. |
| General numerical composition | Installed field/group/vector/matrix, polynomial, pairing and oracle kernels with [composed clients](compiler/mathematics.md) and [changing numeric state](compiler/mathematics.md). The [linear-expression library](../libraries/core/README.md#linear-group-expressions) composes ordered scalar/point terms and evaluates one equation through an ordinary MSM; authors combine shared-basis coefficients explicitly. Complete Groth16 applications remain separate work. The [weighted inner-product argument](../libraries/arguments/bulletproofs/README.md) supplies reusable rounds, and the [Monero Bulletproofs+ construction](../libraries/constructions/monero/bulletproofs_plus/README.md) implements 64-bit aggregated range proofs for 1..16 commitments; pinned upstream controls compare exact bytes at every count. Full transaction integration, batch verification and security proofs remain outside this library. The [KZG library](../libraries/commitments/kzg/README.md) provides checked evaluation domains, evaluations and opening equations. The [Ethereum EIP-4844 construction](../libraries/constructions/ethereum/eip4844/README.md) supplies commitment, proof, challenge, batch-verification and precompile functions. Its constructions reproduce c-kzg-4844's explicit challenge hash inputs, tagged `FSBLOBVERIFY_V1_` and `RCKZGBATCH___V1_`, and all 262 c-kzg-4844 v2.1.8 vectors and 57 derived reference cases agree; no Fiat–Shamir security theorem covers these constructions. The source bound permits 1..64 blobs; admissible execution also depends on the selected capacity. Bit-reversed evaluation domains use a checked two-adic constructor without pairwise root validation. Earlier measured execution limits do not characterize this implementation. Asset formats carry relation data only, so the prover receives the setup's G1 Lagrange points as an ordinary input that the library admits only with their pinned SHA-256, and the verifier key is a library constant. The batch transcript construction recomputes each blob's evaluation point and value from the statement, because a construction observes only messages and start inputs. No KZG security proof is claimed. |
| GKR source library | The [GKR library](../libraries/protocols/polynomial/gkr/README.md) verifies layered arithmetic circuits of uniform width with public stacked add and mul wiring: degree-two Sumcheck rounds per layer, a line restriction to the next layer and the input check, with an honest prover in the same unit. Lean proves [Fiat–Shamir soundness](../lean/docs/spec/fiat-shamir-security.md#the-compiled-gkr-proof-entry) of the plain verifier and of the compiled example Entry for fixed well-formed statements. Non-uniform widths, succinct or private wiring and commitments to the inputs are outside the library. |
| Sigma source library | The [Sigma library](../libraries/protocols/sigma/compositions/README.md) composes the Schnorr pattern into an AND of two discrete-logarithm statements with one shared challenge and a Chaum–Pedersen proof of one discrete logarithm at two bases; the [example project](../examples/projects/sigma/README.md) selects BLS12-381 G1 and the Merlin suite. Maintained checks cover declaration checking, native SSA/Lean replay of the Interactive Entries and construction checking of the compiled proof Entries; no maintained test runs, proves or verifies its Entries through the Host or refuses a wrong witness or proof. Formal results are in [support](../lean/docs/support.md#sigma-compositions). |
| Checked element access | `matrix.get` preserves BLS12-381 Fr, BN254 Fr, Ristretto255 scalar and the [registered residue fields](spec/domains/values.md#registered-residue-fields); missing in-range sparse cells yield zero. `field_array.get` accepts a dynamic index over native BLS12-381 Fr arrays; static `field_array.at` remains available. Both check bounds, including empty shapes and huge indices. The libraries also expose total `at` access under checked input conditions; finite domain indices and matrix views can discharge these bounds. |
| Relations | Bounded R1CS/AIR data import and Assets, exact [relation bindings](compiler/relations.md), a [native R1CS reduction adapter](compiler/relations.md), and an isolated [Plonky3 AIR adapter](../compiler/adapters/plonky3/README.md) checked differentially against its pinned upstream. Import does not prove upstream source adequacy. |
| Multi-table relations | [Relation bundles](spec/domains/relation-bundles.md) have independent C++ and Rust admission and evaluation of deterministic data and challenge-dependent staged predicates. Captured Bundles retain an explicit source relation ABI, table/public/channel counts, polynomial facts, interaction descriptors and simultaneous record substitution. The external [accumulator-machine adapter](../compiler/adapters/accumulator-machine/README.md) supplies a CPU/program/memory relation and independent staged LogUp/grand-product references. The [source machine proof](../common/tests/fixtures/projects/accumulator-machine/README.md) commits base, auxiliary and quotient columns, checks OOD identities and composes one FRI instance. Its selected profile has three tables with independent two-adic heights, optional presence, global all-row Boolean multisets, and signed field balance through LogUp. Native immutable table-width metadata is independent of height and presence; polynomial references admit table/carrier structure, and reached height-taking operations retain actual domain and window checks. Source admission uses these widths for absent configuration and reserves polynomial shape checks for present tables. Complete proof controls cover absent fixed/configured heights 1, 3 and beyond the active profile, exact configuration lengths, and present-table refusal. Arbitrary table counts and other interaction profiles remain library work; relation adequacy and cryptographic soundness are not established by these executions. |
| OpenVM relation comparison | The optional [OpenVM adapter](../compiler/adapters/openvm/README.md) captures five upstream AIRs for a KoalaBear RV32 branch slice. Upstream recorder/DAG/debug checks, the adapter evaluator and both native Bundle evaluators agree on selected traces and mutations. Its memory-bus test partner permits inconsistent reads, so these checks establish neither execution nor termination under VM semantics, nor authentication of initial memory. Deployed BabyBear, persistent memory, full ISA and OpenVM proof compatibility are outside this selection. Its five-table layout is outside the current three-table source argument; admitting signed field balance alone does not supply the missing execution semantics. |
| Clean export comparison | A [pinned Clean flat AIR export](../lean/integrations/clean/README.md) is compared with native finite-AIR evaluation and the KoalaBear/Ext8 ring provider on fixed honest, invalid and mutated rows. This checks native agreement on those rows; it does not prove the native decoders correct. |
| Native proofs | Separate producer/validator execution, derived or authored transcripts, structured framing and authorized setups; [proof contract](compiler/construction.md). One policy covers flat, iterated, PCS and structured programs in `zkc.program/0`. |
| Native hash-chain suites | [BLS12-381, KoalaBear quartic and KoalaBear octic Keccak suites](spec/ir/construction.md#native-hash-chain-suites): Keccak-256 chains with full-digest states, framed events, counter-expanded requests and the decoders of the Merlin suites over the same challenge fields; the quartic and octic instances have UniformIndex transitions. States are host-owned affine capabilities, as for the other suites, implemented by the field backends. Known-answer vectors from an [independent Python reference](../common/tests/support/hash_chain_reference.py), whose Keccak-f[1600] is checked against published Keccak-256 answers and Python's SHA3-256, fix the backend's states, request answers and decoded challenges. Independent replays of compiled native proofs (Schnorr, DLEQ and Sumcheck families, octic index rounds), the maintained Schnorr, Sumcheck and FRI examples and managed transcript methods prove and verify under them. The base-field KoalaBear has no random service or transcript instance. The quartic installation does not extend the independent Lean byte table. Lean proves the reduction of the existing BLS and octic suites' chain to the history oracle, with the byte hash as a random oracle and loss `(q + V)² / \|S\|` for `q` adversary and `V` verifier calls ([provider simulations](../lean/docs/spec/fiat-shamir-security.md#provider-simulations)). The hash-chain theorem is about the construction's byte-level chain model; that the compiled transcript handlers and the installed Keccak-256 kernels implement that model, and that the suites' decoders are modelled ones, remain obligations. |
| Programmable constructions | [Labelled messages and queries](spec/language/entries.md) select ordinary typed scoped handlers, one inherited base and whole-rule overrides. Checked plans preserve state, actual payloads and loop order through participant lowering and independent runtime admission. Providers use private copyable data or an authorized managed transcript with explicit byte-labelled methods. Finite authority sets retain each query's actual service contract; unselected verifier services remain private, with checked dependencies and explicit budgets. Whole-call delegation preserves one live root, actual child-start inputs and root codec coverage across nested, repeated and empty children. Iterated Sumcheck and Schnorr exercise execution and malformed-input order; record codecs support sequential and disjoint round chunks, original-byte observations and conditional completion. |
| Structured participant comparison | The optional [source-bound native probe](../lean/bridges/structured/participant.md) compares both actual Interactive Schnorr endpoints and generic service fixtures with original-SSA and Lean replay. It checks sampled generator-multiple G1 values, independent inputs/receives, pending prefixes, canonical codec failures and provider residual state. Native cleanup and failure adapters are explicit additional observations; this is bounded evidence, not Rust refinement or arbitrary-point decoding correctness. |
| Attempts and retained work | [Persistent attempts](runtime/attempts.md) retain provider state, failed work and unpublished buffers under explicit application policy. |
| Retained storage and work | [Runtime ledgers](spec/runtime/capacity.md#retained-values-and-logical-work) count each shared immutable allocation once while retained and once when produced, with a separate logical-work ceiling charged at every kernel use. The [invocation root](spec/runtime/capacity.md#invocation-ledgers) bounds the bytes of the Host and of every participant runner together in Run, Proof and Function invocations, and each of its charges reports its item's own [refusal code](spec/runtime/capacity.md#root-refusals); each Run and Proof runner keeps its own instruction and iteration fuel, a Function's children charge only its pooled meter, and every execution report renders the root's [usage](spec/runtime/capacity.md#reported-usage) as `invocation`. 65,536 extension-field rows committed once and opened 64 times complete within default budgets. Only row openings, accessors and length queries declare partial read extents. These are retained-payload charges, not peak-memory measurements. |
| Authored transcripts | Explicit external initialization, trial/live checks and snapshots under [authored transcript contracts](compiler/construction.md). Source libraries have bounded `Bytes`, repetition and fragment joining, private copyable SHAKE128 snapshots and shortest unsigned LEB128 index encoding, scalar/collection BLS12-381 Fr/G1/G2 and Edwards/scalar byte codecs, whole-vector big-endian BLS12-381 Fr decoding, plus raw Keccak-256 and SHA-256. A format-only construction selects native framing or one raw `Bytes` message. Pinned Spongefish Schnorr tests cover both directions, the fixed 80-byte vector and ordered decoder failures; they do not establish complete parser equivalence or soundness. Admission does not prove transcript completeness or snapshot reachability. |
| KoalaBear quartic extension | [`koala-bear.ext4-binomial3`](spec/domains/values.md#nominal-field-extensions), `F_p[X]/(X^4 - 3)`, is installed alongside the octic extension: field, vector, polynomial, round and sparse-matrix kernels, base embedding, coset evaluation, interpolation and folding on base-field subgroups, Ring and relation-bundle carriers, canonical wire frames (field 21, vector 22, matrix 28) and the word codecs. The extension-field, matrix, checked-access, numerical and pointwise kernel families run on it against degree-parametrized [integer arithmetic](../common/tests/support/binomial_reference.py), and C++, Rust admission and backend signatures agree in the contract conformance probes. Its rows are committed by the [Poseidon2 row instance](spec/domains/oracles.md#poseidon2-instances) or the distinct [Keccak row instance](spec/domains/oracles.md#installed-binary-merkle-schemes). Its random service and Keccak hash-chain transcript support field draws and `IndexRandomness`; the [parameterized STARK configurations](../libraries/arguments/stark/README.md#configurations) select either direct quartic Keccak challenges or the explicit first-four-coordinate conversion of octic Merlin draws for Poseidon2. |
| BabyBear and Goldilocks | The [registered residue family](spec/domains/values.md#registered-residue-fields) includes `baby-bear`, `baby-bear.ext4-binomial11`, `goldilocks` and `goldilocks.ext2-binomial7`: exact characteristic and base facts, five value representations, full-width canonical literals, scalar/vector/matrix message eligibility, Ring and Bundle carriers, canonical coordinate words, and base-subgroup cosets through logs 27 and 32. Goldilocks uses eight-byte coordinates and has no Montgomery32 byte operations. Explicit extension RNG/Merlin suites and field-appropriate Poseidon2 row commitments support the generic AIR/FRI library. Independent C++ inventory/root controls and [source integration controls](../common/tests/kernels/test_plonky3_fields.py) cover nonbase coordinates, high constants, malformed inputs and cross-family refusal. Native and source tests exercise the complete path, including identical proof bytes at one and four workers and refusal of changed statements or claims. |
| Binary fields | [`gf2-64.pentanomial-4-3-1`](spec/domains/values.md#binary-fields), `F_2[x]/(x^64 + x^4 + x^3 + x + 1)`, and its cubic extension `gf2-64.pentanomial-4-3-1.ext3-trinomial1` by `y^3 + y + 1` are installed through Plonky3 0.8.0's `Poly64` and `Poly192`: field, vector, polynomial, round and sparse-matrix kernels, the base embedding, [bit-pattern literals](spec/domains/values.md#bit-pattern-literals) for `field.constant` and `vector.constant`, canonical wire frames (field 73 and 76, vector 74 and 77, matrix 75 and 78), a hexadecimal readable form and the little-endian [bit-pattern byte codecs](spec/realization/external-constructions.md#binary-bit-patterns). Backend tests compare Plonky3 with an independent shift-and-add reference that also checks the field orders, and run every installed binary kernel to confirm that none reaches Plonky3's halving, which panics in characteristic two; a [`.zkc` Entry test](../common/tests/kernels/test_binary_fields.py) compares kernel results, constants and codecs with the same arithmetic in Python and checks compile-time refusal of two-adic domains, folding, Montgomery codecs and decimal constants above one. Relation bundles over these fields refuse in both readers, the Ring bulk kernels are not installed for them, and pointwise maps over them run. C++, Rust admission and backend signatures agree in the contract conformance probes. There is no random service, transcript suite, row-commitment scheme or Lean admission for these fields. |
| Hash-based proof primitives | KoalaBear [coordinate-word codecs](spec/realization/external-constructions.md#coordinate-words): canonical and Montgomery little-endian encodings for `koala-bear` and its installed extensions, with whole-element vector decoders that reject words at or above the modulus. The [word-codec kernel test](../common/tests/kernels/test_field_words.py) compares them with integer arithmetic through `.zkc` Entries; backend tests compare Montgomery words with Plonky3 0.8.0's serializer. [Bit-reversal permutations](spec/domains/vectors.md) of elements and of whole rows of flat row-major tables are installed for every field family and [checked through `.zkc` Entries](../common/tests/kernels/test_bit_reversal.py) against independent digit reversal. The batched [width-16 Poseidon2 permutation](spec/domains/permutations.md) over KoalaBear uses Plonky3 0.8.0's default parameters with external-work accounting; backend tests compare it with the upstream known answer, p3-poseidon2's generic round functions and an integer implementation, and a [`.zkc` test](../common/tests/kernels/test_poseidon2.py) checks batching and refusal. [Digest-generic Merkle schemes](spec/domains/oracles.md#digest-generic-merkle-schemes) carry fixed-width digest bytes, so another leaf hash and compression is an instance rather than new carriers; the installed Poseidon2 instances over `koala-bear` rows and quartic-extension rows add `MultiOpening`: `oracle.open_many`/`oracle.check_many` with Plonky3's pruned proofs. Backend tests compare roots, rows and pruned proofs with Plonky3 0.8.0's `MerkleTreeMmcs` (and `ExtensionMmcs` for quartic rows) and with a reference model that makes every permutation call explicit, including short, long, altered, duplicate and wrong-root proofs, and a [native proof test](../common/tests/protocol/test_merkle_multi_opening.py) opens positions of both instances through a Fiat–Shamir proof. Each tree commits one table, so tables of different heights cannot share a tree; Merkle commitment, opening and checking charge no permutation work; and no operation exposes a root's digest words as field elements, so a challenger cannot absorb a root as field data. A quartic table and its flattened base table have the same root and proof, so a transcript that absorbs a root must also bind its scheme. Additional explicit Poseidon2 instances commit BabyBear base/quartic and Goldilocks base/quadratic rows; their [parameters and digest widths](spec/domains/oracles.md#poseidon2-instances) remain separate from arithmetic installation. The KoalaBear octic extension has no Poseidon2 row instance. The three KoalaBear Keccak row schemes also support pruned multi-openings through their existing tree owner, preserving their roots, leaf encoding and ordered duplicate positions; proof capacity is bounded by actual element/byte/work limits instead of a single-path sibling limit. |
| Parameterized STARK library | [`stark::single_table::ScalarTableArgument` / `BlockTableArgument`](../libraries/arguments/stark/README.md#parameterized-single-table-argument) implements a protocol for the assertions of one present relation table. `Configuration` owns the base/extension fields, challenge conversion and outer trace/quotient row commitments. The one shared logical FRI component owns its commit/query protocol; deployment separately selects its table schemes, leaf grouping and order. After trace commitment, composition challenge, quotient commitment, OOD claims and identity, the caller batches its DEEP word, calls shared `Commit`, explicitly samples scalar or block positions and binds them into query state, opens outer rows at those positions, and calls `QueryAssociated` on the same state. FRI authenticates the initial value before association and each complete fold before its chain or terminal equality. Outer rows retain pruned multi-openings; FRI uses checked dynamic packets and does not retain the former specialized sibling-omission implementation. KoalaBear/quartic, BabyBear/quartic and Goldilocks/quadratic configurations remain explicit. No proof-size or throughput parity with the removed implementation is claimed. The [integration suite](../common/tests/protocol/test_stark_library.py) covers field conversion, generated AIRs, outer row permutations, authentication and dishonest prover controls. The caller now covers unread committed witness columns with additional rotation-zero claims and applies a fresh linear degree adjustment in both the first FRI word and its query equation; the [reduction contract](spec/domains/stark.md) distinguishes exact degree membership from the remaining proximity/security obligations. One table without interactions. Direct quartic Keccak source deployments cover scalar sampling, block sampling, a canonical zero-bit gate and a positive gate through the installed transcript. No soundness theorem is claimed for this composition, sampling or Fiat–Shamir transform. |
| Host applications | Named Entry inputs/results, joint bundles, proof jobs, explicit immutable data/prover-material reuse and callable Rust bindings through the common Hosts; [Entry guide](runtime/entries.md). |

Setup input associations and authorized incoming PCS values follow the
[setup contract](spec/formats/messages.md#application-authorized-setups).
The protocol retains an explicit verifier-key-consuming terminal check.

Registered services cover seven RNG distributions/providers. Each offers field
`draw`; the KoalaBear quartic and octic, BabyBear quartic and Goldilocks quadratic services also offer [UniformIndex](spec/runtime/services.md#uniformindex-realization)
sampling over a static power-of-two domain (`coins.index<N>()`), interactively and
as a typed [derived transcript transition](spec/ir/construction.md#uniformindex-transitions)
under their installed transcript suites. These four services also expose static
`coins.indices(N,Q)` blocks; native Keccak quartic/octic suites implement the
[block/gate contract](spec/formats/native-index-block.md). Explicit native policies
select grinding difficulty and construction-owned witness transport; source proof
declarations currently select ungated blocks. The STARK library and independent
Lean interpretation have not adopted this native gate path. Explicit query handlers support other positive static
u64 bounds; `zkc::sampling` supplies bounded rejection over ordinary word
providers. The installed interactive and native transcript samplers retain
their power-of-two restriction. Runtime query bounds and other service families
remain unsupported. Tests check
prover/verifier agreement and an independent replay of the framing; they make no
uniformity or Fiat–Shamir security claim. Arbitrary user-defined
request/reply service families remain an extension. Domain and kernel contributions
require their own implementation and installation. Constant-time MSM and diagonal
contractions are supported; automatic contraction selection is an explicit
[optimizer/planner option](compiler/representation.md#checked-physical-decisions),
disabled by the Entry compile path.

Compiler admission has explicit [limits](spec/ir/limits.md), distinct from
[runtime capacity](spec/runtime/capacity.md). Larger bulk-kernel clients do
not enlarge the scalar relation adapter's envelope.

## Checking and evidence

[Preservation](compiler/verification.md) compares adjacent compiler subjects,
including actual receives, ordered action operands, region interfaces, physical
materialization and emitted program content. Rust independently admits the
executable and Host envelope. Bounded tests exercise source/IR mutations, native
execution, framing, failures, capacity and installed consumers. The
[validation map](../common/tests/native.md) records those scopes.

Optional polynomial checks cover `boolean-sum-to-point/0` and relation-pinned
`r1cs-sum-to-point/0`. [Public-coin analysis](compiler/public-coin.md) checks a
selected verifier's dependencies against bound public context, challenges and
receives. Field, scalar `UniformIndex` and atomic product `UniformIndices` requests retain
exact methods and static domains. Shared helper/repeat summaries retain
verifier observations and the selected checked realization. Neither establishes a Fiat–Shamir reduction or arbitrary polynomial
or protocol equivalence.

The [transcript-construction bridge](../lean/bridges/construction/README.md)
exports the checked validators of the compiled proof Entries of the Schnorr,
Sumcheck, composed Sumcheck, Sigma and GKR examples and of a guessing fixture
([format](spec/formats/constructed-participant.md)). Lean checks their transcript
construction and their [participant projection](../lean/docs/spec/participant-projection.md)
against the original exports and proves that each compiled verifier's ideal
meaning, with helper calls read by the original's helpers, is the Fiat–Shamir
transform of its original verifier; other Entries, suites and programmable
constructions have no such check. The composed Sumcheck Entry is covered by the
generated `TwoSums` root, with exact scalar and charged soundness requests and a
compiled-ideal completeness receipt. These are independent of native execution
correspondence. The compiled Sigma proof
Entries (Chaum–Pedersen, two-proof AND, Okamoto) also have fixed-statement
knowledge soundness through the registered endpoints. The
exporter repeats the native proof check before printing the validator; it is
reviewed native code, not a proved component. For Schnorr it proves
fixed-statement Fiat–Shamir knowledge soundness in the random-oracle model, under
the [named assumptions](../lean/docs/spec/fiat-shamir.md#named-assumptions). Lean also
proves [Fiat–Shamir soundness](../lean/docs/spec/fiat-shamir-security.md) of the
transform of any validator over the common participant actions with a
round-by-round soundness certificate, and of the imported Sumcheck verifier's
transform. These are instances of a theorem over typed query sites: any
validator signature with a transcript interface whose sites decode
key-dependent raw answers, possibly refusing, with an error per site. Realized
sampling laws (exact decodings, masking with refusal, low-bit masking of
KoalaBear elements, reduction modulo the BLS12-381 scalar order as in EIP-4844),
grinding-gated sites, compound sites and role separation at one key are proved
for it. Native construction now emits checked index blocks and grinding-gated blocks
under explicit native policies. The formal compiled-verifier connection still
uses the narrower field-challenge participant instance: the new native sites
have no independent Lean interpretation or compiled-verifier theorem yet. Composed with the Sumcheck Entry's checked transform equation, this
bounds the compiled Sumcheck verifier's ideal interpretation in the random-oracle
model: a false claim is accepted with probability at most `(Q + n) / |F|` for a
fixed well-formed statement with `n` rounds (the Entry admits at most two), and
at most `(Q + 2) (1 / |F| + loss)` for adaptively chosen well-formed statements,
`loss` being the challenge decoding's excess, when the initial
transcript determines the statement. The adaptive premise is discharged by one
typed public-value binding event whose row holds the table values as a vector,
the claim as a scalar and the round count as a count. The typed public-value
binding establishes statement determination only; that the native transcript
absorbs the encoded rows, in order, remains assumed.
For the GKR Entry, Lean proves that the
admitted original validator, through its generated normal form (an instance of
the participant normalizer's soundness theorem,
`Zkc.Source.Structured.NormalForm.normalize_sound`, checked by kernel
evaluation), is the plain GKR verifier on well-formed statements within the Entry's maxima, and bounds the
compiled verifier's acceptance of claimed outputs other than the circuit's for a
fixed statement through the composed check's transform of that original, with a
charge per phase: against a weighted adversary budget whose oracle keys are
charged their challenge site's error, and by
`(Q + width + layers (2 width + 1)) max 2 width / |F|` against `Q` queries.
The [executable bridge](../lean/bridges/executable/README.md) reads the validators
of the `zkc.program/0` candidates of the Schnorr and Sumcheck Entries and of a
deferred-rounds fixture, which the runtime admits. Lean checks each against its constructed validator with a
[lowering rule](../lean/docs/spec/executable.md) whose meaning covers proof
framing, decoding failures, instruction budgets, loops, local calls with frames,
helper calls and transcript custody. The rule compares instructions up to checked
normalization of pure total calculations, so a schedule that computes values
before their first consumer, as the compiler's calculation batching does, is
accepted when its anchors and their operand terms agree with the export's. The
compiled Schnorr and Sumcheck programs equal their exports; the two-round
deferred-rounds fixture, whose program defers the first round's product past
the second draw, is accepted through normalization, and compiled with `--no-calculation-batching`, which
computes values where the source defines them, by equality. That fixture's
theorems stop at the constructed validator, since the participant projection
rule is not applied to it. For Sumcheck the program's helper functions are proved to
implement the source's checked helpers: the Pending constructor, openClaim,
point extension and atPrefix by the general helper rule, whose soundness is
proved once, and the terminal
check, whose body iterates and is outside the rule's recipes, by a proof of its
own. Honest-prover completeness of the executable holds for every round count up
to the Entry's static maximum, at every budget of at least `76 + 59 · rounds`
instructions, a charge derived from the program's reading, which at two rounds
is the runtime's acceptance threshold; the proofs are the Sumcheck family's and
do not depend on the value of the maximum. A current limitation: the compiler
accepts a Sumcheck Entry with any static maximum, but the library's terminal
check bounds the point at 64 coordinates, so honest proofs of 64 or more rounds
are rejected, and the executable theorems require a maximum below 64.
The security bounds
transfer to provers of proof bytes through the general construction, projection
and lowering rules, with no equation specific to an Entry about the compiled
program: Schnorr knowledge soundness for a fixed statement, and Sumcheck soundness
for fixed and adaptively chosen statements, the latter from the typed
public-value binding of the transcript model, one event whose row holds the
table values as a vector, the claim as a scalar and the round count as a count,
and determines the statement. The typed public-value binding establishes
statement determination only; that the native transcript absorbs the encoded
rows of the invocation root, in order, remains assumed. The bridge compares the
runtime's stops and observations with that meaning, at every budget up to the
acceptance threshold and on mutated proofs, and checks that the runtime executes
the program a verification receipt names, with the acceptance output and public
inputs of the Lean statement. The runtime's execution, kernels and codec, the
program renderer and the structured exporter remain trusted; the runtime refuses
some inputs the meaning classifies differently, listed in
[support](../lean/docs/support.md).

The [construction obligations](spec/ir/construction-obligations.md) specify
query identities, construction classes, realized laws, observation classes with
certified openings, blocks, gates, cryptographic effects, binding, provider and
explicit-input obligations, equivalence notions and the model of claims. The
native construction implements the profile that absorbs every message, over the
installed Merlin, spongefish and hash-chain suites. Scalar `index` requests use
bounds defined by `data.index` constants. Explicit `indices` blocks and gated
blocks are also implemented for their installed native profiles, with static
bound/count parameters, authenticated gate policy, witness framing and independent
actual-body checks; see [native index blocks](spec/ir/construction.md#native-index-blocks).
Source proof declarations select gates through authored query labels and checked
application paths, including explicit zero difficulty. The separate
[construction-binding views](spec/ir/construction-binding.md) check installed
native history, canonical hash-history handlers and explicit hash inputs against
the actual candidate. They retain exact encoding/state coverage, complete public
inputs and terminal-message distinctions. Unsupported handler, codec, omission
and query-law forms refuse the requested profile; admitted execution alone
carries no binding judgment. General hash-role independence, certified omissions
and salt remain outside these closed checks. Lean states
formal readings of the obligations, refutes each with a model counterexample
([support](../lean/docs/support.md#construction-obligation-counterexamples)),
fixes the type of provider simulations and proves one for the hash-chain
suites' byte-level chain model (the duplex providers' simulations remain
named), and states the joint experiment of a committed opening with its
extraction checkpoint convention and proves its bound for a total straight-line
extractor; a general bound for verifiers with committed tables, read in one
random oracle with their hash calls, also applies to it. The committed opening
is a model protocol, not a compiled Entry. It also states law records with their five constructors and the gated
accepted-value decoder, per-key charges in the typed Fiat–Shamir theorems,
raw answer types by the last event and the lifting of uniform-sort certificates,
binding codecs over typed public-value binding events, and the data shape of the
interaction pattern with the reserved salt kind. The construction model carries
typed draw requests on its challenge occurrences and a typed public-value
binding event, from which the compiled and executable Sumcheck theorems derive
their statement binding; the exported query key and the native occurrence
template keep their draw spelling until the first method with operands. ArkLib's
worst-case round-by-round soundness imports into the typed engine for verifiers
with a guarded verdict, each challenge round charged its own error, and a
process-form certificate transports to a participant validator that realizes the
process form: a worst-case round-by-round proof stated in ArkLib's framework
(written for the example) bounds the compiled verifier of a guessing fixture
Entry, and the bound is attained at zero queries. The import of ArkLib's
interaction-stack soundness is outstanding adapter and instance work: the
attempted implementation met its execution prefixes in `Type 1`, its challenge
models that sample arbitrary distributions and its private Sumcheck instance,
and a restricted route through a propositional realization relation is proposed
but unchecked
([imports](../lean/docs/spec/fiat-shamir-security.md#imports-from-arklibs-round-by-round-soundness)).

The security results share one probabilistic endpoint and one composition rule.
Lean states keyed bad-event certificates over any key space of the lazily
sampled oracle, with an all-table resampling and a trace obligation, and its
soundness theorem is the endpoint that typed certificates and the commitment
bridge reach through transformers; charged reductions compose sub-validators
whose returned values satisfy a postcondition
([composing certificates](../lean/docs/spec/fiat-shamir-security.md#composing-certificates)).
Renamings of oracle cells transport executions, query bounds and weighted costs
between key forms, including the commitment bridge's joint keys and history
keys. [Stage relations](../lean/docs/spec/fiat-shamir-security.md#stage-relations)
compose with budget transport, bounding against the worst adversary in a
translation's support; the construction, projection and pruning equalities, the
typed theorem, provider simulations and the commitment bridge are stages. The
[joint stage](../lean/docs/spec/fiat-shamir-security.md#the-joint-stage-of-a-commitment-and-a-provider)
of a commitment and a transcript provider that share one primitive is a
contract with jointly injective namespaces, a checkpoint extraction, the
checkpoint event and an implication from the intended event, and its frame
records a provider simulation with namespace, hash-answer, state-separation and
joint-loss obligations; the contract composes, and a frame is constructed for a
provider whose primitive inputs are the joint oracle's own tagged keys. The
[hash-chain frame](../lean/docs/spec/fiat-shamir-security.md#the-hash-chain-frame)
passes the commitment's tagged row calls through to their own cells while the
chain realizes the transcript on the same byte hash; every frame obligation and
the provider's budget map are proved, and the abstract committed-opening
verifier over the Keccak-256 hash chain is bounded by the collision and
prediction loss over the joint trace, `(q + depth + 4)² / 2^256`, plus the
commitment stage's loss at `q`. The bound is about the model's deployed reading:
its event encoding is a model encoding rather than the native frames, its index
is one digest modulo `2^depth` rather than the installed index request, and no
compiled Entry, native transcript reading or executable is connected. Statement
bindings relate policy statements to model statements, with the coverage of the
application's false statements and the rejection of unmapped statements as
separate registered obligations.
[Registered endpoints](../lean/docs/spec/fiat-shamir-security.md#endpoints-over-artifact-indexed-evidence)
state ordinary soundness, for fixed and adaptive statements, of a compiled
verifier's ideal meaning and of host validation of program bytes, and
fixed-statement knowledge soundness through a generic Sigma bridge, for evidence
indexed by a compiled Entry's artifacts and by the claim its retained contract
states. The subject driver generates each claim as the registered endpoint
applied to a subject's evidence: knowledge soundness of the compiled Schnorr
(ideal meaning and program bytes), Chaum–Pedersen, two-proof AND and Okamoto
proof Entries, and ordinary soundness of the guessing Entry (ideal meaning) and
of the Sumcheck proof Entry (ideal meaning and program bytes, fixed and adaptive
statements, every round count up to the static maximum, malformed vectors
included). A records run given the subject pipeline's evidence establishes the
assurance reports of Schnorr, Chaum–Pedersen, AND, Okamoto, the guessing Entry
and Sumcheck. Composed Sumcheck retains `target public_sums`; its maintained
claims use the generated `TwoSums` root rather than that manifest report.
GKR retains `target circuit_outputs` and has separate canonical scalar and
charged source-claim receipts, plus perfect compiled-ideal completeness. They
share the full nominal source-to-participant connection and fix width and layer
maxima at four. The adaptive scalar bound is `4 * (Q + 40) / |F|`; the charged
request assigns `4 / |F|` to each selected site and validator cost `160 / |F|`.
These receipts include malformed adversarial statements. They are distinct from
the fixed-statement GKR bound above and from the six manifest assurance reports.
Neither route proves native GKR execution security.

The [scalar Lean bridge](../lean/bridges/common/README.md) consumes the actual
Structured export, derives scalar open-process contracts, and applies selected
ArkLib/VCVio security results. The independent Common source format, admission
and native exporter are retired. Its named DSL target path also checks an authored relation body.
Native SSA/Lean differential tests cover the admitted finite scalar profile.
The separate [structured import](spec/formats/structured-source.md) exports
original protocol-stage units: shared helpers, protocol roots, retained contracts
and formula links, checked primitives, maps and realizations, protocol
applications and repeats, with the native catalogue rows of every domain
identity and random service they use. The native exporter and an independent C++ SSA
reference check this profile, including the 4096-instruction admission budget,
reference depth 64 and effective-site collisions. The
[structured bridge](../lean/bridges/structured/README.md) compares native SSA
evaluation, Lean replay and selected Runner cases; it does not prove native
transformations. Native affine resources, conditional entry completion and
construction-start selection are outside this profile.

Lean independently checks each structured export's metadata, signatures, helper
linking, role scopes, service provenance and computational availability, and
proves its process equations on the shared Region carrier: each generated
participant normal form is an instance of one soundness theorem of a verified
normalizer (`Zkc.Source.Structured.NormalForm.normalize_sound`), checked by
kernel evaluation. It resolves every
domain identity against the exported catalogue rows and admits the rows that
agree with its environment: the BLS12-381 scalar field, its pairing groups and
its random service, at field, vector, G1 and service types. Other installed
identities export their rows and are refused by Lean admission.
[Formal support](../lean/docs/support.md) states exact experiments and premises,
including: the Interactive Schnorr verifier contracts, an honest prover derived
from the checked source's sends and the Sigma properties; the Schnorr AND and
Chaum–Pedersen compositions with their Sigma properties and fixed-statement
random-oracle knowledge soundness of the Fiat–Shamir transforms of their
imported interactive verifiers (not of the compiled proof Entries); two inlining pairs checked
against actual prepared exports; `n / |F|` Sumcheck bounds on the actual
admitted roots under a uniform query service; and honest-prover completeness of
both imported Sumcheck pairs with the prover's per-round fold invariant. No general
availability-soundness or native execution-correspondence theorem is claimed.
Full DSL/compiler/runtime correspondence, production arithmetic/sampling,
backend correctness and complete protocol security remain open.
[Assurance](assurance.md) distinguishes these evidence boundaries.

## Scope of the supported package

Default build and execution checks cover C++/Rust. Formal builds and checks are
optional standalone work; LLZK remains a generic optional relation adapter.
Use [development](development/README.md) and the [test guide](../common/tests/README.md)
for current commands. [Roadmap](roadmap.md) records further work.

The optional [Clean adapter](../compiler/adapters/clean/README.md) exports finite
inductive-table constraints, explicit public boundaries, indexed immutable
lookups and signed channels from one flat component to native Bundles. The
[Fibonacci and FemtoCairo examples](../examples/projects/README.md) execute through
ordinary STARK libraries. LogUp admits signed field balance as well as Boolean
multisets; grand product remains restricted to the latter. Native controls and
complete proof runs cover this path; the existing Lean flat-fragment theorem
does not cover the native adapter. Full Clean ensembles remain outside it.

## Compiler tooling

Root build profiles, shared CLI/SDK requests, structured diagnostics, optional
phase/pass/decision reports, LLVM time traces, feature-gated runtime counts,
manifest consumer tests and bounded captured-input compilation reuse are
implemented. The optional MLIR LSP uses the upstream server with installed zkc
dialects. The separate source LSP serves the development layout profile.
Persistent query caching and automatic policy search remain separate work.
See [tooling](compiler/tooling.md) for supported boundaries.

The native structured exporter retains protocol template origins as bounded,
kind-preserving static term trees, shared with source-claim subject arguments.
It exports total index comparison, vector length and the natural power-of-two
predicate. Sumcheck and composed TwoSums retain exact verifier-side table shape
and repeat-bound input clauses. Native syntax, source comparison and executable
recipe checks are separate from Lean reader admission, ABI-relative clause
identification, callee binding and body equality proofs.

The bounded [component export](spec/language/claims.md#export-and-comparison-api)
retains existing linear record declarations and exact source port layouts in
the current eleven-slot structured schema. Native source-claim export supplies
per-call logical instantiation proposals and direct, pure, terminal and method
routes, including acceptance exits and the initial/yielded alternatives of
repeats. Repeat boundaries retain ordinary carried, captured, count and yielded
action dependencies, including carried backedges and maximum-zero alternatives.
The producer explicitly refuses more than 512 deduplicated logical slots
across a call's subject and residual clauses.
The independent Lean reader admits the original and recomputes these routes;
Boolean, guarded-stop and vector fixtures exercise actual repeated calls and
zero iterations. Unsupported control and effects refuse explicitly. Typed
assignment, formula, readback and mathematical-law obligations remain for the
consumer; this adds no independent acceptance of authored mathematics or
protocol security result. Root generator and protocol-library migration is
separate integration work.


The native declaration foundation retains one immutable canonical declaration
index with catalog-owned record intrinsic associations, managed service signature
rules and builtin constructor homes. Ordinary source homonyms resolve first;
record custody actions retain the authored caller's constructor authority through
closure and independent checking, including fixed-roster distributed succession.
This does not implement View/family syntax or the independent formal
resource-unit consumer.
The checked source [selected-control profile](spec/language/selected-control.md)
admits Math and Protocol if/match with closed captures, exact placed joins,
service aliases, role-local rosters and independently derived common-input
requirements. Source closure rechecks specialized arms and zero-trip state.
Source common-control recurrence completes the immutable graph before checking
demands and independently grounds each demanded carry observation in its base
and yielded transition. Dedicated source tests compare complete canonical
inventories with actual emitted and admitted native originals, including
retained helpers, role permutations, conditional payloads and collection
extents. Canonical Entry inventories are published and independently compared;
the fresh compiler/SDK tests above exercise actual input admission through the
recursive source schema and component mapping.
Original comparison and the retained structured-source/application-map carriers
compare every actual arm. Registered native selection and executable Math scopes
are exercised through actual 4.1 source, native comparison and CPU execution for
Boolean branches and enum matches under simplification and storage policies.
Independent native recurrence analysis checks demanded initial and transition
observations. The source recurrence correction and automatic Entry/SDK
input-requirement binding are integrated. Selected oracle/security realization
remains outside the supported profile. These native checks supply no formal correspondence
claim. Missing registered operations refuse explicitly.


Native SDK ordinary outputs retain private/sealed subtrees in opaque owners.
Schema-checked public getters and whole-value FunctionEntry transport preserve
nominal identity and constructor restrictions, including empty fields and array
elements. Generated opaque bindings keep private storage. Named Run/proof reports
remove duplicate raw returns; inaccessible JSON exports and the physical
BackendRun output seam refuse explicitly. This is source encapsulation coverage,
not a confidentiality or proof-soundness claim. Fresh source outputs and generated consumers execute with the paired native
compiler. Selecting an external root Entry with an opaque parameter still
requires native constructor authority; retained SDK schema transport and native
Host child closure are separate surfaces.
## Represented arithmetic development

The represented-execution unit consolidates collection ownership in Data. Its
canonical [Residue contract](spec/ir/residues.md) specifies exact modular values,
projection and lifts independently of nominal field and byte-codec meaning. The
scalar word producer and independent actual-body reader cover closed arithmetic,
canonical ranges, unsigned projection, exact centered lifts and standard CSE.
The reader reconstructs a canonical expression from actual word operations;
mutations of the modulus, ranges, outputs and poison-producing flags refuse.
Static pointwise tiles now use upstream Linalg vectorization and One-Shot
Bufferization. An independent reader checks actual accesses, initialization,
aliases, release, poison isolation and the fresh returned owner, then recovers
the scalar meaning. The default CPU target now retains that actual expression,
lane bound and liveness-proposed scratch assignment in a typed Runtime plan.
Independent C++/Rust readers validate actual symbolic slot contents; the reached
CPU Call consumes the plan using packed resident kernels with exact-slot aliases
and scalar tails. Extension/binary domains keep complete identities and select
opaque providers. Old executable bare Ring parameters are refused.

Maintained checks exercise default selection, actual-candidate mutation,
resource refusal and compiled field/quotient-ring/group clients. Lazy-context
checks cover collection and pass dependencies; the installed IR client consumes
a word candidate without the lowering or target libraries. The admitted storage
profile is static, rank-one and pointwise. These native readers do not add Lean
correspondence or object-code/AOT coverage.


## Installed native message source requirements

The installed `zkc::transport::NativeMessage(T)` requirement supports abstract
Relay contracts and generic Forward clients through existing `where` syntax,
normal indexed imports, alpha-renamed implementations and selected dispatch.
It demands executable data, external construction, native message support and
a nonempty complete source carrier. Source replay authenticates explicit
requirements independently, including standalone and unused declarations,
inherited module/section telescopes, erased requirements and erased admission
expansions. Anonymous Construction handlers replay inherited clauses through
frozen ownership links, including grouped rules with shared spans. Universal
conformance refuses hidden strengthening, and generated Host selections check
unused protocol demands. Repeated concrete clauses and
distinct static specializations exercise exact, insufficient and intermediate
work allowances at real callable and generated helper snapshot boundaries.
Admission types and call origins are metered before project, header, callable
and cached helper copies, with unused-declaration and structural-limit controls;
discharged metadata releases its allocation. Copy/Drop, Participants, descriptor
categories, physical codec selection and native/runtime admission remain
separate. No Lean semantic or connector implementation is included. The
[native consumer controls](../compiler/test/language_consumer_requirements.cpp)
and [Host controls](../common/tests/protocol/test_consumer_requirements.py)
record the maintained scope, including manifest dependencies and default Host
execution. Transport-library API inspection also passes through a separately
built SDK CLI with the strict assurance reader repair. That reader's integration
is independently owned; these source checks change no SDK decoding contract.
