# What the implementation supports

This page says what the compiler, runtime and formal library do today, and what
they do not claim. The [specification](spec/README.md) describes the model itself
and is not weakened to match this page; the [roadmap](roadmap.md) orders the work
that remains.

Every capability below is bounded. Passing controls establish behavior within an
implemented subset; they do not establish that the complete target architecture
is realized, and no entry is a cryptographic security theorem.

## Routes at a glance

| Route | Entry and execution | Checking and state |
|---|---|---|
| Mathematical source | `.zkc` → mathematical MLIR → existing participant compiler/runtime | Explicit bounded R1CS/AIR asset capture, fields/groups/Boolean formulas, nominal products/variants, catalog domain statics, associations and capability bounds, static generics/components, permissions, native data/kernel bindings, formal polynomial intrinsics, mathematical helper realization in local code, ordered local control, messages, static protocol composition, managed random services, owner guards, bounded distributed repetition, conditional participant completion and selected Entries; immutable definition graphs, selected Entry closures, independent source comparison and structural interface reading; [scope](spec/profiles/source/mathematical-language.md) |
| Source | `.pir` → `protocol_exec` → `zkc.participants/1`; source/artifact hosts | Supported Lean source/candidate checks; retained while consumers migrate |
| Native mathematical | Direct MLIR → `zkc.program/1`; `zkc.run/1` bundles or proof deployments | Bounded compiler preservation and runtime admission; foundation complete, native Lean connection open |
| Finite tables | Table source → direct/physical plans → table session | Independent Lean references and scoped transformation proofs; executable consumers remain |

## Mathematical source and Host

The fresh `.zkc` path resolves explicit modules/assets, checks generic libraries,
closes an Entry, emits mathematical MLIR and independently compares the admitted
SSA with the checked source. Its immutable original and interface retain logical
schemas, participant availability, services, relation definitions and exact clause
bindings. Standalone admission requires canonical original/interface bytes.

Run/proof Entries select participants, public inputs, acceptance, optional target,
setup associations and explicit construction. `zkc.entry/1` packages retain the
original, interface, artifact, toolchain and compilation choices. Rust authenticates
the package against an application-supplied digest and binds the named interface
to the independently admitted native artifact. It trusts the compiler publication
for source correspondence; it does not interpret the retained MLIR.

The [common Host](language/entries.md) supports named logical inputs/results,
independent prove/verify calls, immutable reusable prover material, setup slots,
explicit attempts and bounded defaults. CLI files and optional Rust data bindings
use these same Hosts. Public values bind shared proof operands; setup material
never supplies its own authority. Results publish after successful cleanup, and
reports retain reached execution and publication state on failure.

| Boundary | Maintained evidence |
|---|---|
| Syntax, types, naturals, permissions and static contracts | [Source checks](../compiler/test/language.cpp), [types](../compiler/test/language_types.cpp), [normalization](../compiler/test/language_natural.cpp), [power-of-two shapes](../compiler/test/language_power.cpp), [capabilities](../compiler/test/language_capabilities.cpp) |
| Formal polynomials and helper realization | [Polynomial controls](../compiler/test/language_polynomial.cpp), [independent recipes](../compiler/test/math_realization.cpp) |
| Relations, exact attachments and actual composition bindings | [Source predicates](../compiler/test/language_specifications.cpp), [admitted-IR mutations](../compiler/test/language_specification_ir.cpp) |
| Entry selection, interface and source correspondence | [Entries](../compiler/test/language_entries.cpp), [Entry IR](../compiler/test/language_entry_ir.cpp), [interface admission](../compiler/test/language_interface.cpp), [command controls](../compiler/test/language_cli.py) |
| Actual receives, distributed control, services, resources and native data | [Runtime source corpus](../crates/zkc-tools/examples/language_native.rs): role substitutions, service aliases, conditional draws, nested repeats/completion, affine cleanup, vector/matrix/sequence kernels and formal polynomial realization |
| Named Host, setup authority and attempts | [Host clients](../crates/zkc-tools/examples/language_native/host.rs), [proofs](../crates/zkc-tools/examples/language_native/proof.rs), [setups](../crates/zkc-tools/examples/language_native/setups.rs), [attempts](../crates/zkc-tools/examples/language_native/attempts.rs) |
| Files and generated Rust data bindings | [CLI and independent Rust consumer](../tests/protocol/test_language_host.py): both transcript suites, authored proofs, malformed inputs, changed public/context values, retries, private-file protection and partial publication |
| Maintained authoring and installed consumers | [Schnorr/Sumcheck projects](../tests/protocol/test_source_projects.py), [installed C++ API](../tests/consumer/compilercore.cpp) and [separate runtime execution](../tests/consumer/execution.py) |

The source profile does not expose every native operation as concise syntax.
Fixed source arrays use static numeric indexing. Private ingress without an
admitted validator, member-generic conformance and zero-leaf messages refuse.
Receive-only setup declarations and finer per-receive pinning remain explicit
[migration obligations](compiler/migration.md#frontend-consumer-transition).
Formula/opaque/captured relations and target/input/output/continuation clauses
state intent; they add no guard, satisfaction fact or security theorem.
Source no-Drop rules and native affine custody retain their separate checks.

Entries/Host implementation and review are complete. Integrated frontend
stabilization is in progress. Native Lean correspondence, full existing library
and external compatibility, and the remaining table/checker consumers stay open.

## Foundation capability map

The selected foundation is implemented and stabilized. This map separates
formation, execution and proof-host support. The [validation map](compiler/foundation-validation.md)
connects it to maintained evidence; the [migration inventory](compiler/migration.md)
records consumers still using earlier paths. Full migration and native Lean
correspondence remain open.

| Capability | Implemented path and evidence owner | Limits and later extensions |
|---|---|---|
| Total scalar mathematics and dependencies | [Mathematical formation](../compiler/lib/Dialect/Protocol/IR/Mathematical.cpp), [math lowering](../compiler/lib/Transforms/MathLowering.cpp); generated arithmetic and received-value controls | Wider mathematical vocabulary is admitted per operation; an installed kernel alone is not a total-operation recipe. |
| Static calls and applications | Canonical application expansion, projection and authored local preservation; [nested Schnorr](../compiler/test/fixtures/mathematical/nested-schnorr.mlir) | Affine application results use exact-input summaries; unknown roots remain refused at repeat obligations. |
| Structured local control | [Local control](compiler/local-control.md), C++/Rust admission and managed frames; bounded `local.condition` termination in the [entry completion](compiler/entry-completion.md) profile | Exact-root `if`/`match` captures/`for` results compose with mathematical repeats. Aggregate payload provenance and private-match history are not added. |
| Protocol iteration and roles | [Structured iteration](spec/profiles/compiler/structured-iteration.md), [compiler checks](../compiler/test/native_iteration.py), [runtime client](../crates/zkc-tools/examples/native_iteration.rs) | Composed RNG/transcript local control now executes through nested repeats. Count agreement in a joint run is not a proof of equal count expressions. |
| Products, sums, extents and indexing | Structured data operations, optional matrices and residual state execute | Common data operations retain total payloads; checked local variant operations package copyable non-total PCS objects. [Runtime-count sequences](compiler/nested-data.md) now support immutable records and independently shaped matrices; affine elements remain excluded. |
| Affine resources and effects | [Native local policy](../compiler/lib/Dialect/Protocol/NativePolicy.cpp), state-successor contracts, runtime custody and generation checks | [Exact origins](compiler/resource-origins.md) prove input identity through structured control; this does not establish state equality or independent randomness. |
| Services and aliases | Entry-origin scalar services, nested capture/query and lease cleanup execute | Mathematical query formation admits the installed BLS, BN254, Ristretto and ext8 random-service contracts with exact result types. Native attempts retain provider state while reinstalling entry service bindings. Broader service contracts remain separate. |
| Vector/group bulk algebra | Explicit [algebra](../compiler/include/zkc/Contracts/Declarations/Algebra.td) and [curve](../compiler/include/zkc/Contracts/Declarations/Curve.td) contracts; [composed numeric state](compiler/composed-state.md) executes shrinking inner products and growing commitment batches through proof and interactive hosts | BLS numeric state, partial inverses and persistent returned attempts have maintained coverage. [Composed clients](compiler/mathematical-composition.md) extend this evidence to BN254 QAP/pairing and KoalaBear/ext8 oracle data; [entry completion](compiler/entry-completion.md) covers early-abandoned attempts. |
| Polynomial residuals | [Recipe lowering](spec/profiles/compiler/polynomial-recipes.md), product/cubic Sumcheck and actual original-point checks | The [composition client](compiler/mathematical-composition.md) exercises ext8 interpolation, coset transforms and quotient/fold kernels in transparent local bodies. Formal polynomial expansion retains its separate declared limits. |
| Relation and setup identity | [Structured relation declarations and actual entry bindings](compiler/relation-bindings.md), selected BLS PCS and [multiple authorized setups](spec/profiles/compiler/structured-proof-messages.md#application-authorized-setups) | Exact key/input authority includes unused ports and inactive PCS alternatives. Non-BLS leaf codecs and typed services have contrasting executed clients; installed bulk-domain compositions have [executed coverage](compiler/mathematical-composition.md); declarations alone do not check relation satisfaction. |
| QAP, pairing and AIR/oracle composition | [Composed clients and capacity](compiler/mathematical-composition.md): bound matrix/assignment, coset numerator/MSM/GT and full-trace extension/oracle checks through separate participants; native component sizes up to 8,192 rows in three lowering modes | Individual GT values, all installed scalar vectors/matrices and source-group vectors; dense GT vectors and full protocol libraries remain later work. No native Lean execution correspondence is claimed. |
| Native transcript construction | [Native proof packages](compiler/native-proofs.md) derive selected BLS, Ristretto and ext8 suites; [authored external state](compiler/authored-transcripts.md) uses explicit initialization, snapshots, trials/live checks and exact native messages | Authored admission preserves calls but does not prove transcript completeness or snapshot reachability. Existing suite selection is not arbitrary derivation. |
| Native proof input and wire | [Host constructors](../crates/zkc-tools/src/artifact/native.rs) and [closed codec](../crates/zkc-backends/src/codec/native.rs) | Native inputs require a supported wire type or explicit resource/key constructor. [Structured proof messages](compiler/structured-proofs.md) supply `/4` records/sums with installed typed numeric leaves. [Nested data](compiler/nested-data.md) adds record sequences and ragged matrix frames. Each complete type retains explicit wire admission. |
| Attempts and retained work | [Native attempts](compiler/native-attempts.md) retain RNG/services, unpublished buffers and consumed work, including authored external calls; reports expose per-attempt primitive work and a host-configurable lower cap | Application-owned Boolean policy; one-shot inputs and unsupported affine outputs refuse. [Conditional entry completion](compiler/entry-completion.md) skips unreached suffixes and preserves affine successors, prefix work and exact return coordinates. |
| Independent proof execution | Existing native producer/validator programs use the common `Runner`; source and supplied-participant admission have separate scopes | No protocol-specific interpreter is required. New boundary forms still need admission, host construction and composed proof tests. |
| Observation inputs and checking | Actual receives, draws, roots, ordered guards/stops and source operands remain explicit under their contracts | Rich observation analyses and broad native Lean correspondence are later work; current passes/fixtures are not security proofs. |

## Checking and evidence

The [owner map](architecture.md#implementation-owners) locates code. The table
below distinguishes compiler checks, runtime admission, independent references
and formal evidence. Current test results apply to the tested revision and scope;
a documentation link is not evidence of a fresh run.

The [foundation validation map](compiler/foundation-validation.md) records the
checks, references and trust boundaries. Native compiler checks recognize bounded
relations; equal but unrecognized rewrites may refuse. Native Lean differential
execution and source/artifact correspondence remain open. Existing source and
table consumers retain their independent checking contracts.

## Native mathematical protocol path

Mathematical MLIR enters as `protocol.module` with the `protocol` profile.
Preparation expands static applications and helpers, then performs scoped
canonicalization. Projection emits participant programs with total expressions
retained. Demand lowering outlines calculations at their first consumers and
applies admitted execution recipes. Physical selection binds installed kernels.
[Compiler profiles](spec/profiles/compiler/mathematical-protocols.md) and
[preservation checks](compiler/preservation.md) define each boundary.

The current execution formats are [`zkc.program/1`](spec/profiles/compiler/program.md)
and [`zkc.run/1`](spec/profiles/compiler/run.md). They cover flat and structured
values, loops, messages and services. Superseded native participant/run tags and
the service-only carrier are refused. The earlier source route uses
`protocol_exec` and `zkc.participants/1`; its frontend and independent checker
consumers have not migrated. The source host's `zkc.run/2` input array is a
separate interface, not a version of the native Run bundle.

| Mechanism | Current behavior and guide |
|---|---|
| Mathematical values | Total scalar expressions, formal polynomials, dynamic tensors, nominal products/sums and runtime-count record/ragged containers; [structured mathematics](compiler/structured-mathematics.md), [nested data](compiler/nested-data.md). Formation alone does not install a realization or codec. |
| Ordered computation | Authored local calls, partial operations, guards, affine successors, bounded loops and conditional entry completion; [local control](compiler/local-control.md), [entry completion](compiler/entry-completion.md). |
| Interaction | Arbitrary declared roles within the roster bound, actual receives, compact counted regions and source-bound schedules; [structured iteration](spec/profiles/compiler/structured-iteration.md). General network transport and dynamic protocol composition remain open. |
| Resources | Exact-root summaries through local control/static applications, distinct randomness draws, nonce/transcript custody, poisoned service roots and cancellation; [resource origins](compiler/resource-origins.md), [native services](spec/profiles/compiler/native-services.md). |
| Relations | Immutable R1CS/AIR signatures, configuration/public/witness purposes and actual decision binding; [relation bindings](compiler/relation-bindings.md). A declaration alone does not check satisfaction. |
| Proof execution | Selected derived or authored transcripts, separate producer/validator processes, exact deployment pins, structured frames, authorized setups and persistent attempts; [native proofs](compiler/native-proofs.md), [attempts](compiler/native-attempts.md). Producer completion alone does not certify a proof prefix. |
| Numerical composition | QAP/coset/MSM/GT, full-trace AIR/extension/oracle checks and shrinking/growing state; [mathematical composition](compiler/mathematical-composition.md), [composed state](compiler/composed-state.md). These are general mechanisms and composed clients, not full BP+/Groth16/zkVM libraries. |
| Observation inputs | Actual operands, receives, draw occurrences, resource roots, ordered guards/stops and later disclosures remain explicit; [analysis inputs](compiler/ir-foundation.md#information-retained-for-observation-analyses). No affine observation analyzer or sampling/security theorem is claimed. |

### Compiler limits

The following limits are separate from runtime value, wire and work capacities.
They bound analysis and expansion; increasing one does not raise the others.

| Boundary | Limit |
|---|---|
| Declared role roster | 1,024 roles |
| Active helper depth and expanded helper analysis | 64 levels; 100,000 operations |
| Helper dependency analysis | 1,000,000 bit-vector words and dependency indices |
| Availability replay | 1,000,000 words, including repeated calls |
| Role expansion | 100,000 operation/port visits before allocation |
| Exact resource-origin analysis | 100,000 shared work units and 64 call/structured-region levels |
| Formal scalar interpolation | Subject to expansion budgets; formation of 64 points does not imply scalar lowering succeeds |
| Composed R1CS adapter | BLS Fr, at most 8 rows, 128 columns and 1,024 nonzero terms; ordinary lowering limits also apply |

Every original helper, including unreferenced private definitions, is checked
before optimization. Analysis summaries belong to the current IR revision.
Unknown/conflicting resource roots refuse independently of analysis-limit stops.
The R1CS adapter's envelope is distinct from the larger bulk-math clients.

The optional checked polynomial compiler binds original and participant inputs,
receives, guards, queries, residual outputs and the terminal decision. It supports
`boolean-sum-to-point/1` and relation-pinned `r1cs-sum-to-point/1`; its reports bind
companion bundle bytes and post-check passes. See [structured mathematics](compiler/structured-mathematics.md)
for the exact comparison and trusted boundaries.

### Native verifier views

[Public-coin analysis](spec/profiles/compiler/public-coin.md) now checks the
selected verifier's guard/decision dependencies on bound entry components,
actual received values and designated draws. It derives ordered challenge
prefixes and authored application paths from an unsimplified prepared copy;
unchanged challenge delivery and statement coverage are checked independently
of candidate reports. The `ZkcCompilerCore` API, standalone report checker and
checked native bundle option are implemented. Reports identify exact original
and prepared IR, requirements and, for compilation, source text and bundle.

Controls distinguish public-table Sumcheck from composed R1CS with verifier
witness inputs. Statement-only binding refuses the latter; full-assignment
binding reports its non-statement coordinates. Generated runtime controls cover
honest prefixes, altered prover messages, an explicit unsatisfiable-R1CS
weighted bad event, early guard stops, service failures, decode stops and driver
limits. This is conservative structural analysis. Broader automatic Fiat–Shamir, new encoding/domain policies, algebraic
extraction and native Lean correspondence remain open. Selected native transcript
constructions have separate admission rules; this analysis supplies no security
premises for them.

## 1. By implementation area

| Area | What runs | What is not claimed |
|---|---|---|
| C++/MLIR | Typed source, constrained libraries, interaction, construction, participant projection and physical lowering, relation ingestion, optional execution-bound claims | Broader domain lowering, path-sensitive claims, scalable summaries |
| Lean checking | Executable source and artifact references, bounded differential comparison, finite closure, scoped transformation and algebraic proofs | Raw-to-typed adequacy, checker soundness, application security, native refinement |
| Rust | Separate role and artifact execution, owned immutable values, checked concrete preparation and setup reuse, real cryptographic adapters, bounded resource admission | General preparation interfaces, broader kernels, complete memory and progress guarantees |
| Runnable protocols | Original-subject Sumcheck and PCS, bounded machine execution proof, range/inner-product/excess/owner transaction composition over Arkworks, Dalek and Merlin | Production setup and zero-knowledge profiles, larger scalable applications, further families |
| Optimization | Changed physical interpolation and linear-contraction plans, measured in both domains against direct-library baselines | Shared preparation, layout and MSM improvements, controlled whole-route ablations |

**Input-selected families and controllers.** One compact common body and its
projected participants retain bounded symbolic counts. Each role computes its
count from explicitly mapped actual entry inputs; native and independent Lean
execution check bounds and the joint driver checks agreement. Witness and RNG
ports need not enter the selector. Dynamic families currently enter only at the
root, without protocol dependencies; the automatic artifact-bound construction
path refuses them. Lean supplies count-instantiation/projection laws, not a
proof of this native interpreter. Resumable finite-step controllers preserve
state and failure events. A compiled-attempt driver buffers typed messages and
discards retry output while retaining consumed RNG state; completion yields
unpublished bytes through an explicit external codec. Failed ingress now returns
an observable stopped runner with its reached work and earlier selections.
Native and Lean ingress use role-local iteration allowances and finish each
role's selectors before checking agreement. The reference stops preparation at
its first role-local failure, while the native host also constructs peer runners;
arbitrary peer-event or joint-trace equality is not claimed. A test-only
zero-result oracle exercises the compiled challenge guard
and retries, with exact per-body Lean reply replay.

**External protocol boundaries.** Authored local calls compile and execute exact
Monero hash-chain and OpenVM duplex transitions, with explicit grouping and no
zkc prefix. Archived upstream checkpoints agree with native execution; bounded
Lean replay independently interprets the schedule using trusted exact-input
hash/permutation replies. Raw Edwards bytes and subgroup images, ordered Boolean
axes, and exact Monero choice sampling have separate checked adapter APIs and
negative controls. Edwards arithmetic is not yet installed in the PIR kernel
catalogue. A persistent grinding driver separates candidate trials on clones
from one compiled live witness check. Proof metadata extracted using pinned
upstream types drives compact selectors for archived BP+ and mixed/optional
OpenVM AIR cases; selected VK/config metadata remains a separately authenticated
input obligation. These are shared foundations, not complete BP+ or recursive OpenVM
provers/verifiers, a cryptographic retry bound, or a native refinement theorem.

## 2. Paths that execute end to end

**Frontend.** Immutable input, analysis and checked-module APIs retain nominal
records, products/unit, finite arrays with retained element/count identity,
lexical bindings/scopes, domain parameters, resolved calls and specialization
origins before common PIR erasure. Participant placement
blocks share the function checker and capture only used owned leaves. Named
distributed outputs, child-result bindings and direct closed entries lower to
the existing interaction model. Named natural constants and domain-generic protocol families support
bounded static construction. Abstract family bodies receive source type, role
and requirement checks; concrete selections still require independent PIR
admission. Queries retain partial declarations without admitting them. Checked
static components add immutable interfaces, parametric component conformance,
abstract clients, coherent linking, private typed layouts, sorted static
applications and explicit logical resource units. The same checked client executes with empty affine and Boolean
representations, including rejected guard inputs, through independent Lean and
Rust paths. Finite local variants add exhaustive matching and active-only payloads;
checked array traversal retains affine element ownership and zero-trip state.
Source, MLIR, Rust and Lean preserve terminal stops through those boundaries.
Native checked ingress binds real Groth16 key/assignment material to the retained
compiled relation and reuses one PCS setup across separately checked indices.
Missing cryptographic and ceremony premises remain explicit. Captured multi-file
projects add exact library dependencies, visibility and reexports, owner-local
checking, private checked helper closure, named public
operands and lexical map/fold. File-aware analysis reports partial availability,
exact dependencies, obligation causes and ordinary unused-binding warnings.
Package discovery/distribution, generic runtime preparation packages and verified
native elaboration remain future work. The
[frontend guide](compiler/frontend.md) and
[project guide](language/projects.md) describe the implementation.

Installed domain vocabulary is declared in MLIR-independent typed contract
records. Generated modules expose types, capabilities and operations through
ordinary `use` paths, aliases and reexports; implicit primitive namespaces and
profile module headings have been removed. Finite `Vector`/`Matrix` families
reduce to the existing logical types. Library-owned operators select by known
nominal operand constructors and elaborate to checked calls, including in
component bodies. Source functions may define hooks for records owned by their
package. Duplicate bindings and private or unavailable targets are refused.
Contract metadata owns copy/drop permissions, history transitions, source
availability and the conservative local effect envelope. Kinded Domain/Type/Nat
applications now survive source specialization, common admission and domain-owned
MLIR type adapters. Logical admission is independent of physical availability;
exact installation data owns provider and representation selection. C++, Rust
and Lean independently admit the structural profile. The fixed-vector example
executes an exact-length KoalaBear dot product through Plonky3 and compares it
with an independent Lean reference. Its BLS instance is logically admitted but
has no physical implementation, and fixed-vector codecs are not installed.
New domain meanings, native kernels and Lean interpretations still require
explicit implementations; declarations generate neither execution nor proofs.

Domain authoring now has generated direct/custom/unavailable native-binding
coverage and standard ODS verifier forwarding. Explicit build contributions
assemble one declaration inventory and native registry per installation;
installed base/extended consumers cover static and shared linkage. Rust and Lean
admission is independently authored in operation-family modules. Native dispatch
uses exact implementation owners after common security checks, and flat typed
values require exhaustive classification and accounting. A same-port alternate
BLS dot-product implementation preserves the default selection. Layout aliases
inherit dispatch and security constraints. Four independent physical registry
readers compare signatures; native tests execute every installed alternative.
Lean implementation selection uses explicit domain-owned registrations. Tests detect
deliberately different reader signatures; they are not equivalence proofs.
The [extension guide](development/extensions.md) describes these boundaries and
an IR-only specialization example. Full external nominal/runtime-value SDKs and
portable decomposition certificates remain outside this support.

Successful frontend publication pairs a checked model with its emitted common
content. Pure dependency inspection is separate from loading, and callers can
set per-invocation [formation and expansion budgets](compiler/frontend-budgets.md).
These budgets cover selected logical work; they are not whole-process quotas.

Checked libraries construct runtime-dependent alternatives using isolated Boolean
conditionals, in generic clients and component members. Linking propagates selected
terminal calls and removes unreachable join results without recovering a stop.
A component is selected only by a declared `link`: a concrete component written
as a generic call's component actual, as in `Client::<BoolCell>(x)`, refuses as
`library-component-actual`. Empty component representations (`type Value = ()`)
retain logical ownership through plain helpers, mixed aggregates, captures and
joins. Linking inserts explicit resource creation or disposal at representation
boundaries; it preserves same-slot transfers and does not reinterpret one
abstract slot as another. Abstract callers still need the declared copy/drop
permissions. One join is still refused at link (`library-resource-boundary`):
an arm that yields a plain public variant input beside an arm that yields a
variant built from a zero-storage value. Propagation carries the unit back into
the public input instead of creating it on the plain arm.
Self-contained variant content graphs retain exact subjects and share nested
type structure. The measured corpus includes 200-row captured relations and
distinct full-width BN254 coefficients. The split-project wrapper chain executes through depth three;
depths four and eight deterministically reach the existing 128-byte algorithm
occurrence-path limit in C++ and Lean. This is an explicit capacity limitation,
not support for arbitrary-depth source combinators. The earlier direct selected
variant graph checks remain separate from this source expansion measurement.
Module/type byte ceilings and proportional decode budgets remain explicit.
Resource units follow each participant's own frame. The native driver and the
independent Lean source interpreter retain a completed participant's returned
units when another participant later stops; stopped and cancelled roots retire
their units. The reference suspends original-source execution separately for
each role and drains roles in the declared joint scheduler's lexical order.
Differential controls include later peer failure, nested frame disposal,
message cuts and independent iteration budgets. This is bounded execution
evidence, not a proof of participant projection.
A logical origin that becomes a carrier name (a function's, a generic
definition's, a component member's, a link's or a view's) is at most 128
bytes; a module path that makes one longer is refused at the declaration
(`source-origin-limit`). Origins are carried as dotted names, not as
structured module paths.
Repeated decoding is not cached; these controls do not establish a wall-clock
bound, particularly for the Lean physical reference's repeated descriptor checks.
Canonical inlining coalesces duplicable capture aliases consistently in MLIR and
Lean. Logical origins and emitted symbols are allocated separately from exact
source identities. Cross-owner origin collisions receive checked owner qualifiers;
ambiguous source selectors refuse.
Ordinary source uses unwrapped files, strict ASCII identifiers and `r#` escapes.
Declaration and associated paths use `::`; runtime projections use `.field`,
`.N` and `[index]` according to receiver kind. Exact installed identities and
`bind` contract IDs are quoted. Records use braces only. Qualified constants
retain existing staging rules; protocol reference slots do not gain hidden
computation. Temporary projections evaluate once and retain the owning source
permission checks, including zero-leaf obligations and disjoint siblings.

Printed carrier text is a `carrier module`: a closed flat form that keeps the
names the compiler generated. It cannot import modules or assets or declare
library interfaces, components, records, constants or exports
(`source-carrier-authoring`), and cannot be a child module or an imported
library (`source-carrier-project`); like common JSON, a carrier root refuses
`--library` options (`unsupported-option`). Carrier text reads directly into common
records and uses common admission diagnostics. Authored analysis is unsupported
for both carrier forms. Canonical printing rereads its final formatted output
for exact common equality; text formatting preserves tokens and comments.
Operations with MLIR properties refuse an
unknown property key (`mlir-unknown-property`) instead of dropping it.
Normalized construction refuses a selected alias whose raw sites do not map to
one numbered site (`construction-selector-coordinates`), and a direct function
selector whose spelling also names another origin family refuses
(`construction-source-selector-ambiguous`), also when the function belongs to
the group its spelling names. An imported function's selector reaches the copies
its entry and its links carry.
The match history-effect check is lexical; public transcript scheduling remains
subject to the separate construction and static-schedule restrictions. KZG index
reuse executes through native host APIs and feeds ordinary compiled opening
verification. The exact index/relation binding remains a checked host
boundary; no compiler-visible index-encoding theorem is claimed.

**Interactive protocols.** Common source runs through MLIR projection and
physical lowering, independent Lean candidate checking, and Rust execution over
Arkworks. It covers Sumcheck and repeated opening children, independent and
supplied role controls, and native differential evidence. The
[interactive execution guide](compiler/interactive-execution.md) owns the path.

**Constructed artifacts.** Proof production and validation run as separate
processes with an independent original-source reference, under the
[artifact format](compiler/artifact-format.md), with
[normalized identity](runtime/artifact-identity.md) by default and an explicit
exact-identity mode.

**Composable libraries.** Inspectable trace reduction and opening, and aggregated
range and inner-product components, execute through the same compiler with real
Arkworks and Dalek kernels. One optional contraction analysis changes reached
computations in both domains.

**Imported relations.** A standalone LLZK adapter imports Circom and BLS Halo2
constraints into inspectable R1CS. A complete explicit PIR Groth16 consumer
produces BN254 Poseidon membership proofs that unmodified snarkjs accepts, and
accepts upstream proofs at depths 2 and 16. Controlled randomness gives identical
coordinates and canonical serialized bytes. Prepared-key data is cross-checked
against the actual R1CS; key derivation and ceremony integrity stay external
premises, and the fixture uses public test trapdoors, so it is unsuitable for
production deployment. Finite AIR retains its own degree, window and read
structure. The first imported proof is not zero-knowledge and its matrix
verification is linear and unstructured.

**Applications.** Bounded machine execution proof and confidential transactions
execute through the shared compiler and actual backends. An optional registered
claim analysis checks independently retained requirements against exact calls,
subjects and verifier guards under explicit body-law premises. Both public-only
validators consume that verifier-owned contract; authenticating it is the
caller's responsibility and is not inferred from the proof. Transaction overhead
is substantial and native and reference resources are limited.

**Source-route AIR and oracles.** An authored two-AIR permutation argument runs with
extension-field auxiliary traces, scope quotients, opening batching, binary FRI
and authenticated queries; a non-FRI affine-table client uses the same oracle and
construction interfaces. Small cases agree with an independent Lean source
interpreter. The route is nonhiding and carries no security-bit or BCS theorem,
and it is not yet arbitrary AIR-to-argument elaboration. Larger runs need an
explicit host accounting policy, and a height-8192 element-limit failure stands.

**Tables and physical execution.** Typed source imports into registered MLIR
retaining logical table operations, exports the direct plan, is checked in Lean
and executes over owned Rust tables across two fields, ordered residuals,
structured control and complete failure effects. Packed and segmented immutable
buffers substitute through the same runtime, with capacity checked before
execution. The scalar physical path converts scalar types and operations, checks
the submitted body and executes it on either layout, with preparation, deferred
reads and output decoding bounded and capacity refusal preceding execution.

## 3. What is checked, and how

The maintained formal package builds all declared modules, enforces module
dependency boundaries, and audits reached axioms for every supported target;
only `propext`, `Classical.choice` and `Quot.sound` are permitted, so a proof
hole or an added axiom fails. The optional integration package audits itself
separately. Tool wrappers are compiled and linked separately, and their
serialization behavior is not covered by the library audit. Declaration counts
report coverage, not maturity.

For the older source/table routes with executable Lean references, differential
testing supplies the scoped native correspondence evidence described by the
[assurance policy](assurance.md#6-implementation-correspondence-policy). The
mathematical program route has not discharged that Lean differential obligation.
Existing reference comparisons cover complete outcomes, selected observations, live values and
residual states, with independent input generation, failure controls and replay,
including export after canonicalization and common-subexpression elimination.
Intentionally corrupted observations are detected. This is finite execution
evidence, not a correspondence theorem.
Malformed input-family controls are refused under one table of identifiers in
the compiler, the Lean reader and the native reader. A separate admission
corpus ([cases](../tests/fixtures/refusal-agreement/cases.json),
[test](../tests/protocol/test_refusal_agreement.py)) compares shared admission
reasons for resource reuse, operation signatures, attributes, natural syntax,
local control and variant types, including attribute-order cases with multiple
defects. Native variant
diagnostics retain additional detail after the common reason. Formation and
source-to-plan correspondence are distinct phases: a well-formed changed plan
can pass formation and fail correspondence. This is bounded agreement, not a
global error-priority rule for malformed inputs with several defects.
All three readers bound vector sizes, positions and degrees at 1,048,576 at
admission, as they bound curve indices. The Lean checker and the runtime apply
the direct-plan metadata tests in order with the same codes, decoding context
types before comparing metadata
([test](../tests/admission/test_direct_plan_metadata.py)), and both stop an
execution whose joint schedule exhausts its budget. Outside these some reasons
are still named per implementation. The runtime decodes raw body syntax and
checks operand types together after the metadata tests. Lean decodes that
syntax before metadata and checks operand types afterward. A plan with malformed
body syntax and metadata can therefore report its metadata defect natively and
its body defect in Lean; the compiler's request reader names every request defect
`invalid-request`; and the specification does not place the installed-dependency
check, which both readers apply after decoding. The Lean library and local
readers name attribute defects `kernel-attributes`, which admission maps to the
shared names and which remains the runtime kernel name everywhere. The Lean
reader refuses a number longer than 78 digits as `natural-limit` before reading
its syntax, where the compiler and runtime name the position's range. Loop-count
and parameter range refusals, and transcript origin labels, are named
differently by each reader; a schedule depth limit is a failed host natively and
a refusal in Lean; and Lean refuses a vector past its runtime capacity where the
runtime, whose capacity is smaller by default, stops as exhausted.

**Source layer.** The native source checker -- parser, resolver, constant
evaluator, record flattener and library checker -- is trusted for
source-language formation; the Lean source laws state elaboration obligations,
not proofs of that implementation. Requirement certificates are replayed by the
C++ `checkCertificate`, Rust `replay_static_requirements` and Lean
`Tools.RequirementChecker.check`; the Lean checker returns facts proved by
`checked_sound`, and the native checkers are tested against it rather than proved
equivalent. The compiler, runtime and Lean reference independently admit the
common carriers emitted for checked libraries and local variants, and
differential tests compare their concrete observations and resource behavior on
finite cases.

Neither the finite checker nor the portable interactive checker performs
per-artifact kernel proof replay. The finite checker runs a proved algorithm
under explicit build and execution trust; the portable checker is independently
implemented executable Lean whose soundness and raw-to-typed elaboration are not
proved.

## 4. The model that is covered

The reference covers subjects and finite scope; complete execution; pure and
effectful source interpretations; role inputs, captures and admission; mutable
state, facts and immutable preparation; interaction and atomic composition;
observation and disclosure; persistent probability and conditional judgments;
relation and terminal use; authorized continuation; transformations; and
realization.

The [formal package](../formal/README.md) organizes the retained capabilities by
semantic responsibility. `Zkc` is the small foundation; source, compiler,
probability and protocol modules use narrow imports. The main package resolves
Mathlib; optional integrations resolve their own compatible dependencies.
[Support](../formal/SUPPORT.md) states the exact premises of each claim.

The heterogeneous execution relation connects different returned representations
in their actual final states, with sequencing and composition laws. It extends
the equal-reply relation for realization; it does not change the finite execution
model or prove anything about native Rust allocation.

Six [protocol interpretations](guides/protocols.md) exercise the selected
boundaries. Their expression, mathematical, wire and native coverage are
distinct: describing a family is not implementing its stack.

## 5. What remains

The [architecture](architecture.md), [compiler design](compiler/design.md),
[runtime design](runtime/design.md) and [layout](development/layout.md) specify the
responsibility boundaries; exact source, dialect and runtime interfaces follow
their first joined implementation. The [roadmap](roadmap.md) orders the work.

Real external backends and bounded checked changes already run, as listed
above. Remaining engineering work includes broader backend/kernel coverage,
shared demand and preparation reuse across contrasting clients, general endpoint
admission and transformation coverage, and independently deployable role modules
with their coordination interface. The artifact ABI and final authoring language
remain open interface boundaries.
Asynchronous projection, stronger observers, richer recurrence and
protocol-changing wire transformations have explicit research triggers rather
than places in the sequence.

Formal theorem availability and native implementation completion stay separate.
The ordinary interactive Sumcheck theorem exists in Lean; connecting it to a
complete native protocol is implementation work.
