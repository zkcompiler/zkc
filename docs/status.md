# What the implementation supports

This page says what the compiler, runtime and formal library do today, and what
they do not claim. The [specification](spec/README.md) describes the model itself
and is not weakened to match this page; the [roadmap](roadmap.md) orders the work
that remains.

Every capability below is bounded. Passing controls establish behavior within an
implemented subset; they do not establish that the complete target architecture
is realized, and no entry is a cryptographic security theorem.

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
Unquoted dotted references refuse (`source-name-ambiguous`) when the spelling
has two complete readings that authorize the requested category, as an exact
declaration and a module, import or dependency path do. This covers calls,
declarations, types, static terms, record literals, predicates and values. An
ordinary function does not authorize arbitrary member suffixes. Quoted calls/declaration references select the exact local name; other
ambiguous uses need a renamed declaration or an unambiguous import alias.
Printed carrier text is a `carrier module`: a closed flat form that keeps the
names the compiler generated. It cannot import modules or assets or declare
library interfaces, components, records, constants or exports
(`source-carrier-authoring`), and cannot be a child module or an imported
library (`source-carrier-project`). Operations with MLIR properties refuse an
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

**AIR and oracles.** An authored two-AIR permutation argument runs with
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

Differential testing is the default native correspondence evidence, as the
[assurance policy](assurance.md#6-implementation-correspondence-policy) states.
Comparisons cover complete outcomes, selected observations, live values and
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
