# What the implementation supports

The supported implementation is `.zkc` frontend → Protocol IR (PIR)
(`protocol`, `participant`, `exec`, `physical`) → `zkc.program/0` → a shared Rust
Runner with Entry/proof/joint Hosts. Direct MLIR enters the same compiler.
[Specification](spec/README.md) defines contracts; this page records support.
Links identify maintained checks, not a claim that they ran for this revision.

## Current public interfaces

Artifacts use one current schema with exact tags, record shapes and unknown-field
validation. Boundary versions remain `0` during development; equal versions do
not guarantee compatibility across builds. Their specification owners define the
accepted contents; the [maintenance policy](development/maintenance.md#format-versions)
defines when versions change.

| Interface | Contract |
|---|---|
| Executable program | [`zkc.program/0`](spec/formats/program.md), a physical participant program |
| Source Entry | [`zkc.entry/0` and `zkc.language-interface/0`](spec/formats/entry.md#published-entry-package), authenticated source, input/result schemas and selected artifact |
| Joint execution | [`zkc.run/0`](spec/runtime/joint.md), participants, schedule and invocation policy |
| Native proof | [Policy, descriptor, deployment, construction map and invocation binding](spec/formats/proof.md), with `zkc.native-origin/0` occurrences |
| Installed declarations | [`zkc.contract-declarations/0`](compiler/operation-contracts.md), declaration inventory; the language catalog contributes an opaque compiler fingerprint |

Use `zkc run`, `prove` and `verify` for named Entries, and `run-bundle`,
`prove-bundle` and `verify-bundle` for lower-level artifacts. In the C++ SDK,
`Zkc::Compiler` owns compilation and packaging;
`Zkc::Driver` separately owns CLI parsing. Request `Tools` for installed commands.
See the [SDK reference](../compiler/README.md#components-and-ownership).
Rust package, run and deployment admission take trusted 32-byte SHA-256 pins;
CLI adapters own hexadecimal spelling. Backend service installation uses
`service_support` returning a named `ServiceSupport` signature and reply bound.

## Source and application boundary

`run` and `proof` explicitly select joint execution or proving/verification.
`zkc.toml` supplies the module/asset map; the CLI discovers the nearest manifest.
Commands accept unique short or qualified Entry names. Execution filters omitted
names by run/proof kind; inspection and compilation require a single Entry.
`new` and `init` create separate protocol and Entry files with input templates;
`prepare` creates missing maps while preserving existing values. Manifest-relative
paths supply omitted inputs, proof files and run results. Runs obtain a fresh
session unless supplied explicitly. `inputs check` shares native preparation without
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
primitive definitions and an embedded scalar prelude,
local short-circuit Boolean operators and total Boolean formulas, inferred usage, catalog
and natural preconditions with explicit contract checking, derived boundary admission, unified data/service arguments,
source rejection with `require`, formal polynomial intrinsics, checked
pointwise `map` of scalar helpers over vectors, general finite reductions,
statically bound scoped Math/Local callbacks with generic apply/forward and
module wrappers, local control,
messages, services, static protocol composition, bounded repetition and conditional completion.
Independent source comparison checks emitted MLIR against checked definitions;
[source semantics](spec/language/README.md) owns exact limits.

An authenticated `zkc.entry/0` package retains the original, source interface,
compilation choices, selected artifact and the expression assets the artifact
references. The Host binds named logical inputs and results to the independently
admitted program and checks every reachable asset reference before any
invocation. It trusts compiler publication
for source correspondence; it does not interpret retained MLIR. Maintained
[Schnorr and Sumcheck projects](../examples/projects/README.md) exercise this path.

Fixed source arrays use static numeric indexing. Private ingress without an
admitted validator, member-generic conformance and zero-leaf messages refuse.
Abstract callable signatures with member generics can be checked and inspected,
but modules implementing them are not supported. Associated types cannot
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
Native source tests cover ordered and Unit state, mixed state dependencies,
filtered stops, strict zip admission, packed record sequences, repeated calls,
dependent inner ranges and mutable capture snapshots. Fixed source arrays now
adapt through independently checked sequence construction, including records,
empty arrays and Unit items. Source item-provenance checks
now cover callback-local `where item_from(input, domain)`, optional input labels,
arbitrary slots, multiple independent origins, generic restricted forwarding,
named argument order, nested captures and invariant local-region inputs. Native
controls include exact normalized module conformance, independent authored
selector reconstruction and mutation refusal. Inner conditions preserve outer
catalog/natural inference. Labels and canonical maps are exposed separately in
declaration inspection; they add no runtime closure or finite IR attributes.
Retained witnesses also check formal callback slots and authored invocation
identities through nested regions. Total index literals, static natural index construction and comparisons now
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
field backends may lack that realization. The [shared libraries](../libraries/zkc/README.md#finite-computations)
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

Checked notation inspection is available through
`inspectNotations` with `NotationInspectionOptions.includePrivate` and
`includeInstallation`, and `zkc check --notations` with `--notation-private` and
`--notation-installation`. The version-0 diagnostic view covers descriptors,
bindings, scopes and occurrences, with private/local data hidden by default and
installation data opt-in. [Notation limits](spec/language/notation.md#bounds)
set 4096 descriptor keys per environment including fixed Boolean descriptors,
64 delimiter holes and 8 MiB output; lowered SDK limits are rechecked on retained
projects. This does not supply an LSP server or formatter.

Relation and target/input/output/continuation clauses state intent; declarations
alone add no runtime guard, satisfaction fact or security theorem.

## Foundation capability map

| Capability | Support and boundary |
|---|---|
| Scalar, collection and polynomial mathematics | Nominal Algebra field/group vectors, indices, field matrices and field arrays, with ordered `algebra.array_from_elements` packing. A shared collection interface reports structure without granting finite, mathematical, Copy/Drop or wire admission; shape evidence retains the logical family. Source syntax, logical binding spellings and native codecs retain their meanings; builtin tensors have no compatibility alias. Total expressions and checked realization recipes; [structured mathematics](compiler/mathematics.md). Kernel installation alone does not supply a mathematical recipe. |
| Group identity | Total `intrinsic<G>("curve.identity")`, Algebra identity and independently checked native recipe. Dalek Ristretto255 and prime-order Edwards25519; arkworks BLS12-381 G1 and BN254 G1/G2/GT, including multiplicative-one GT. Empty MSM identity is checked for the five installed dense group families; [contract](spec/domains/values.md#group-identity). No native proof claim. |
| Shared expression evaluation | Captured [Ring and Bundle terms](spec/language/definitions.md#asset-domains-and-projections), derived static dimensions, retained Entry assets and independent Host preflight. [Checked structural sharing](spec/domains/ring-expressions.md#structural-sharing) preserves ordered substitution and read obligations. The [generic Sumcheck library](../libraries/sumcheck/README.md) derives its width and degree from its Ring parameter; it remains a public-table client without a PCS or native security theorem. |
| Source clients of imported AIR | The [imported AIR client](../common/tests/fixtures/projects/imported-air/README.md) checks actual trace, configuration and public inputs. The [AIR STARK client](../common/tests/fixtures/projects/air-stark/README.md) adds base-field trace commitments, scoped extension-field quotient chunks, OOD/DEEP equations and FRI through ordinary source libraries and separate proof Hosts. The single-table profile covers one present table's assertions; the three-table profile adds whole-Bundle Boolean multisets and signed field balance through LogUp. Security reductions for both remain separate work. |
| Pointwise vector maps | Source `map` applies one static scalar `math fn` over installed field vectors through [checked bulk vector operations](spec/ir/protocols.md#checked-pointwise-maps): shapes first and O(formula) code. A common semantic reader independently interprets source and candidate payloads, admitting sharing and commuted field arithmetic; helper calls are interpreted from the original source and installed contract laws remain a shared foundation. Shape mismatches are backend failures (`rejected:require`); field constants, addition, subtraction and multiplication are limited to Ring depth 1,024. The [KoalaBear/Ext8 comparison](../common/tests/kernels/test_pointwise_polynomials.py) checks maps, Ring rows and coefficients, and coset kernels against integer arithmetic, including the off-domain interpolation distinction. There is no dedicated row kernel, backend ABI or first-class function value. |
| Finite vector reductions | [Source binders](spec/language/definitions.md#finite-reduction-binders) use general scoped consumers and finite IR. Arbitrary vector reducers collect first and call once. Native `vector.product` has empty identity one on BLS12-381 Fr, BN254 Fr, Ristretto scalar, KoalaBear and KoalaBear Ext8, with independent C++/Rust admission and normal resource charges. Default-false [fusion](spec/ir/protocols.md#optional-vector-reduction-fusion) handles adjacent single-use multiply-map/native-sum with every original row guard retained. Its relation is values and ordered shape refusals under sufficient resources, not equal exhaustion or a memory bound. The scalar Lean bridge does not cover vector-map/reduction correctness. |
| Mathematical shape and bounds | A shared MLIR-free [fact kernel](spec/domains/mathematical-facts.md) supplies exact origin/axis equality, strict bounds and exact/upper cardinalities. Independent source and SSA adapters replace duplicate closure rules. Helper observations are scoped to immutable symbol closures, with explicit rebuild and pass-manager invalidation controls. Nested work is cumulative and distinguishes absence from capacity. Source symbolic naturals retain their interpretation; guards and nominal types remain unchanged. Core scope intersection is available, while production reached-guard and loop-invariant propagation remain unsupported. |
| General finite IR | [Typed domains and total/Local fold and collect](spec/ir/finite.md) retain static helpers, complete entry admission, exact bound provenance and state dependency closure. Declaration-owned laws, structural SSA views, separate transient equation matches and shared producer emission support checked loop fallback, native sum/product/dot/MSM, elementwise fields and sums of accumulator-independent pointwise field expressions. Selected matrix rows and columns use scalar contractions; admitted nested collections use one whole matvec, preserving empty-outer admission. Total callbacks expose ordinary helper calls and fixed pack/projection pairs remaining after canonicalization before optional bulk selection, while retaining the source of that selection for comparison. Nested indexed helpers preserve callback extent/bound premises and exact positional argument identities, including selected matrix axes. Independent readers check actual candidates, including checked original-helper normalization for total finite recipes and `local.realize`. Bounded DAG sizing and a per-callback structural ceiling preserve later small opportunities without refunding spent work. Optional lane or payload-comparison capacity retains checked ordered fallback; required-reader exhaustion is diagnosed separately. Checked candidate publication is shared. Opt-in decision records distinguish missing evidence, actual capacity, policy and recipe restrictions, ordered retries and nested publication boundaries; preparation and total Math lowering also expose remarks and IR dumps. These observations supply no checking evidence. Generic canonicalization/CSE preserve domain admission. [Handwritten controls](../compiler/test/fixtures/finite/README.md) cover mutations, failures and 2^17 field workloads. Full fixed-array/matrix fallback additionally requires the native checked-access contracts; the source frontend now uses checked adapters into this IR. No Lean-to-native bridge is claimed. |
| Calls, roles and control | Static application, role projection, structured local control, nested repetition and [conditional completion](compiler/control.md). General dynamic protocol composition remains open. |
| Structured values | Products, alternatives, extents, checked indexing and [nested immutable data](compiler/mathematics.md), including independently shaped matrices; source sequence elements include contextually packed records, tuples, source arrays and empty products, with explicit packing/unpacking and source comparison; affine and non-Drop elements are excluded. Persistent sequence storage and retained validation support default-budget Local collection of 16,384 indices and 8,192 two-index records in maintained controls. Whole-value encoding has a separate peak-storage limit; a collection that executes locally can exceed it when exported. |
| Affine resources and services | Exact-origin analysis, state successors, resource custody, entry service aliases and failure cleanup; [resource origins](compiler/resource-origins.md). Equal roots do not prove equal state or independent randomness. |
| FRI source library | [Binary FRI](../examples/projects/fri/README.md) over natural-order two-adic cosets, with commitment/fold/query/terminal checks and independent-reference tests. The library retains a checked coset word across folds; the AIR library consumes the authenticated positions and values. Security theorems remain separate obligations. |
| General numerical composition | Installed field/group/vector/matrix, polynomial, pairing and oracle kernels with [composed clients](compiler/mathematics.md) and [changing numeric state](compiler/mathematics.md). The [linear-expression library](../libraries/zkc/README.md#linear-group-expressions) composes ordered scalar/point terms and evaluates one equation through an ordinary MSM; authors combine shared-basis coefficients explicitly. Complete Groth16 applications remain separate work. The source [Bulletproofs+ library](../libraries/bulletproofs/README.md) implements weighted inner-product rounds and Monero 64-bit aggregated range proofs for 1..16 commitments; pinned upstream controls compare exact bytes at every count. Full transaction integration, batch verification and security proofs remain outside this library. |
| Checked element access | `matrix.get` preserves BLS12-381 Fr, BN254 Fr, Ristretto255 scalar, KoalaBear and KoalaBear Ext8; missing in-range sparse cells yield zero. `field_array.get` accepts a dynamic index over native BLS12-381 Fr arrays; static `field_array.at` remains available. Both check bounds, including empty shapes and huge indices. The libraries also expose total `at` access under checked input conditions; finite domain indices and matrix views can discharge these bounds. |
| Relations | Bounded R1CS/AIR data import and Assets, exact [relation bindings](compiler/relations.md), a [native R1CS reduction adapter](compiler/relations.md), and an isolated [Plonky3 AIR adapter](../compiler/adapters/plonky3/README.md) checked differentially against its pinned upstream. Import does not prove upstream source adequacy. |
| Multi-table relations | [Relation bundles](spec/domains/relation-bundles.md) have independent C++ and Rust admission and evaluation of deterministic data and challenge-dependent staged predicates. Captured Bundles retain an explicit source relation ABI, table/public/channel counts, polynomial facts, interaction descriptors and simultaneous record substitution. The external [accumulator-machine adapter](../compiler/adapters/accumulator-machine/README.md) supplies a CPU/program/memory relation and independent staged LogUp/grand-product references. The [source machine proof](../common/tests/fixtures/projects/accumulator-machine/README.md) commits base, auxiliary and quotient columns, checks OOD identities and composes one FRI instance. Its selected profile has three tables with independent two-adic heights, optional presence, global all-row Boolean multisets, and signed field balance through LogUp. Native immutable table-width metadata is independent of height and presence; polynomial references admit table/carrier structure, and reached height-taking operations retain actual domain and window checks. Source admission uses these widths for absent configuration and reserves polynomial shape checks for present tables. Complete proof controls cover absent fixed/configured heights 1, 3 and beyond the active profile, exact configuration lengths, and present-table refusal. Arbitrary table counts and other interaction profiles remain library work; relation adequacy and cryptographic soundness are not established by these executions. |
| OpenVM relation comparison | The optional [OpenVM adapter](../compiler/adapters/openvm/README.md) captures five upstream AIRs for a KoalaBear RV32 branch slice. Upstream recorder/DAG/debug checks, the adapter evaluator and both native Bundle evaluators agree on selected traces and mutations. Its memory-bus test partner permits inconsistent reads, so these checks establish neither execution nor termination under VM semantics, nor authentication of initial memory. Deployed BabyBear, persistent memory, full ISA and OpenVM proof compatibility are outside this selection. Its five-table layout is outside the current three-table source argument; admitting signed field balance alone does not supply the missing execution semantics. |
| Clean export comparison | A [pinned Clean flat AIR export](../lean/integrations/clean/README.md) is compared with native finite-AIR evaluation and the KoalaBear/Ext8 ring provider on fixed honest, invalid and mutated rows. This checks native agreement on those rows; it does not prove the native decoders correct. |
| Native proofs | Separate producer/validator execution, derived or authored transcripts, structured framing and authorized setups; [proof contract](compiler/construction.md). One policy covers flat, iterated, PCS and structured programs in `zkc.program/0`. |
| Programmable constructions | [Labelled messages and queries](spec/language/entries.md) select ordinary typed Local handlers, one inherited base and whole-rule overrides. Checked plans preserve state, actual payloads and loop order through participant lowering and independent runtime admission. Providers use private copyable data or an authorized managed transcript with explicit byte-labelled methods. Finite authority sets retain each query's actual service contract; unselected verifier services remain private, with checked dependencies and explicit budgets. Whole-call delegation preserves one live root, actual child-start inputs and root codec coverage across nested, repeated and empty children. Iterated Sumcheck and Schnorr exercise execution and malformed-input order; record codecs support sequential and disjoint round chunks, original-byte observations and conditional completion. |
| Attempts and retained work | [Persistent attempts](runtime/attempts.md) retain provider state, failed work and unpublished buffers under explicit application policy. |
| Retained storage and work | [Runtime ledgers](spec/runtime/capacity.md#retained-values-and-logical-work) count each shared immutable allocation once while retained and once when produced, with a separate logical-work ceiling charged at every kernel use. 65,536 extension-field rows committed once and opened 64 times complete within default budgets. Only row openings, accessors and length queries declare partial read extents. These are retained-payload charges, not peak-memory measurements. |
| Authored transcripts | Explicit external initialization, trial/live checks and snapshots under [authored transcript contracts](compiler/construction.md). Source libraries have bounded `Bytes`, repetition and fragment joining, private copyable SHAKE128 snapshots and shortest unsigned LEB128 index encoding, scalar/collection BLS12-381 Fr/G1 and Edwards/scalar byte codecs, plus raw Keccak-256. A format-only construction selects native framing or one raw `Bytes` message. Pinned Spongefish Schnorr tests cover both directions, the fixed 80-byte vector and ordered decoder failures; they do not establish complete parser equivalence or soundness. Admission does not prove transcript completeness or snapshot reachability. |
| Host applications | Named Entry inputs/results, joint bundles, proof jobs, explicit immutable data/prover-material reuse and generated Rust data bindings through the common Hosts; [Entry guide](runtime/entries.md). |

Setup input associations and authorized incoming PCS values follow the
[setup contract](spec/formats/messages.md#application-authorized-setups).
The protocol retains an explicit verifier-key-consuming terminal check.

Registered services cover four RNG distributions/providers. Each offers field
`draw`; the KoalaBear octic service also offers [UniformIndex](spec/runtime/services.md#uniformindex-realization)
sampling over a static power-of-two domain (`coins.index<N>()`), interactively and
as a typed [derived transcript transition](spec/ir/construction.md#uniformindex-transitions)
under its Merlin suite. Explicit query handlers support other positive static
u64 bounds; `zkc::sampling` supplies bounded rejection over ordinary word
providers. The installed interactive and native transcript samplers retain
their power-of-two restriction. Runtime query bounds and other service fields
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
receives. Neither establishes a Fiat–Shamir reduction or arbitrary polynomial
or protocol equivalence.

The [scalar Lean bridge](../lean/bridges/common/README.md) imports actual retained
PIR programs, proves open-process contracts, and applies selected ArkLib/VCVio
security results. Its named DSL target path also checks an authored relation body.
Native SSA/Lean differential tests cover the admitted finite scalar profile.
[Formal support](../lean/docs/support.md) states exact experiments and premises.
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
