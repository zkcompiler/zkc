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
nominal products/variants, static parameters and components, capabilities and
permissions, lexical scopes and patterns, mutable bindings with inferred region
state/captures, statement-scoped participant inference, nested ordered calls,
helper result inference, expression-wide structural type constraints, partial
static arguments with positional or named binding, named value/service arguments,
Unicode 17 NFC names, scoped mathematical operators and paired-delimiter calls
with import activation, explicit fixity and local component bindings, catalog-checked
primitive definitions and an embedded scalar prelude,
local short-circuit Boolean operators and total Boolean formulas, inferred catalog/natural
preconditions with explicit contract checking, unified data/service arguments,
source rejection with `require`, formal polynomial intrinsics, checked
pointwise `map` of scalar helpers over vectors, local control,
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
Abstract member-generic signatures can be checked and inspected, but components
implementing them are not supported.
Resource permission inference, implicit role remapping, natural equation solving
and inversion of associated types are outside the source profile. Finite reduction
binders remain unsupported; `∑` and `∏` are reserved. The staged parser resolves
notation environments after imports and before bodies. Callable notation uses
ordinary signature constraints and authored evaluation order, with descriptor
arity and scope checked by the independent binding witness. No formal
elaboration-correctness theorem is claimed.

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
| Scalar, tensor and polynomial mathematics | Total expressions and checked realization recipes; [structured mathematics](compiler/mathematics.md). Kernel installation alone does not supply a mathematical recipe. |
| Shared expression evaluation | Captured [Ring and Bundle terms](spec/language/definitions.md#asset-domains-and-projections), derived static dimensions, retained Entry assets and independent Host preflight. [Checked structural sharing](spec/domains/ring-expressions.md#structural-sharing) preserves ordered substitution and read obligations. The [generic Sumcheck library](../libraries/README.md#expression-sumcheck) derives its width and degree from its Ring parameter; it remains a public-table client without a PCS or native security theorem. |
| Source clients of imported AIR | The [imported AIR client](../examples/projects/imported-air/README.md) checks actual trace, configuration and public inputs. The [AIR STARK client](../examples/projects/air-stark/README.md) adds base-field trace commitments, scoped extension-field quotient chunks, OOD/DEEP equations and FRI through ordinary source libraries and separate proof Hosts. The single-table profile covers one present table's assertions; the machine profile adds whole-Bundle Boolean multiset interactions. Security reductions for both remain separate work. |
| Pointwise vector maps | Source `map` applies one static scalar `math fn` over installed field vectors through [checked bulk vector operations](spec/ir/protocols.md#checked-pointwise-maps): shapes first and O(formula) code. The matcher reads the generated body independently but shares the realizer's formula derivation. Shape mismatches are backend failures (`rejected:require`); field constants, addition, subtraction and multiplication are limited to Ring depth 1,024. The [KoalaBear/Ext8 comparison](../common/tests/kernels/test_pointwise_polynomials.py) checks maps, Ring rows and coefficients, and coset kernels against integer arithmetic, including the off-domain interpolation distinction. [Lean map laws](../lean/Zkc/Algebra/RingExpression/Pointwise.lean) cover values, refusals and realization for a list model, without native correspondence. There is no dedicated row kernel, backend ABI or first-class function value. |
| Calls, roles and control | Static application, role projection, structured local control, nested repetition and [conditional completion](compiler/control.md). General dynamic protocol composition remains open. |
| Structured values | Products, alternatives, extents, checked indexing and [nested immutable data](compiler/mathematics.md), including independently shaped matrices; affine sequence elements are excluded. |
| Affine resources and services | Exact-origin analysis, state successors, resource custody, entry service aliases and failure cleanup; [resource origins](compiler/resource-origins.md). Equal roots do not prove equal state or independent randomness. |
| FRI source library | [Binary FRI](../examples/projects/fri/README.md) over natural-order two-adic cosets, with commitment/fold/query/terminal checks and independent-reference tests. The AIR library consumes the authenticated positions and values. Security theorems remain separate obligations. |
| General numerical composition | Installed field/group/vector/matrix, polynomial, pairing and oracle kernels with [composed clients](compiler/mathematics.md) and [changing numeric state](compiler/mathematics.md). Complete Groth16 and range-proof applications remain separate work. |
| Relations | Bounded R1CS/AIR data import and Assets, exact [relation bindings](compiler/relations.md), a [native R1CS reduction adapter](compiler/relations.md), and an isolated [Plonky3 AIR adapter](../compiler/adapters/plonky3/README.md) checked differentially against its pinned upstream. Import does not prove upstream source adequacy. |
| Multi-table relations | [Relation bundles](spec/domains/relation-bundles.md) have independent C++ and Rust admission and evaluation of deterministic data and challenge-dependent staged predicates. Captured Bundles retain an explicit source relation ABI, table/public/channel counts, polynomial facts, interaction descriptors and simultaneous record substitution. The external [accumulator-machine adapter](../compiler/adapters/accumulator-machine/README.md) supplies a CPU/program/memory relation and independent staged LogUp/grand-product references. The [source machine proof](../examples/projects/accumulator-machine/README.md) commits base, auxiliary and quotient columns, checks OOD identities and composes one FRI instance. Its selected profile has three tables with independent two-adic heights, optional presence and global all-row Boolean multiset interactions. Absent fixed-height and configured-height tables still face active polynomial height checks, which can refuse valid absent tables. Arbitrary table counts and other interaction profiles remain library work; relation adequacy and cryptographic soundness are not established by these executions. |
| OpenVM relation comparison | The optional [OpenVM adapter](../compiler/adapters/openvm/README.md) captures five upstream AIRs for a KoalaBear RV32 branch slice. Upstream recorder/DAG/debug checks, the adapter evaluator and both native Bundle evaluators agree on selected traces and mutations. Its memory-bus test partner permits inconsistent reads, so these checks establish neither execution nor termination under VM semantics, nor authentication of initial memory. Deployed BabyBear, persistent memory, full ISA and OpenVM proof compatibility are outside this selection. Its field-balance relation is separate from the Boolean-multiset machine proof profile. |
| Clean export comparison | A [pinned Clean flat AIR export](../lean/integrations/clean/README.md) is compared with native finite-AIR evaluation and the KoalaBear/Ext8 ring provider on fixed honest, invalid and mutated rows. This checks native agreement on those rows; it does not prove the native decoders correct. |
| Native proofs | Separate producer/validator execution, derived or authored transcripts, structured framing and authorized setups; [proof contract](compiler/construction.md). One policy covers flat, iterated, PCS and structured programs in `zkc.program/0`. |
| Attempts and retained work | [Persistent attempts](runtime/attempts.md) retain provider state, failed work and unpublished buffers under explicit application policy. |
| Retained storage and work | [Runtime ledgers](spec/runtime/capacity.md#retained-values-and-logical-work) count each shared immutable allocation once while retained and once when produced, with a separate logical-work ceiling charged at every kernel use. 65,536 extension-field rows committed once and opened 64 times complete within default budgets. Only row openings, accessors and length queries declare partial read extents. These are retained-payload charges, not peak-memory measurements. |
| Authored transcripts | Explicit external initialization, trial/live checks and snapshots under [authored transcript contracts](compiler/construction.md); admission does not prove transcript completeness or snapshot reachability. |
| Host applications | Named Entry inputs/results, joint bundles, proof jobs, reusable immutable prover material and generated Rust data bindings through the common Hosts; [Entry guide](runtime/entries.md). |

Setup input associations and authorized incoming PCS values follow the
[setup contract](spec/formats/messages.md#application-authorized-setups).
The protocol retains an explicit verifier-key-consuming terminal check.

Registered services cover four RNG distributions/providers. Each offers field
`draw`; the KoalaBear octic service also offers [UniformIndex](spec/runtime/services.md#uniformindex-realization)
sampling over a static power-of-two domain (`coins.index<N>()`), interactively and
as a typed [derived transcript transition](spec/ir/construction.md#uniformindex-transitions)
under its Merlin suite. Other fields, runtime or non-power-of-two bounds,
out-of-domain and rejection sampling, and retries are not supported. Tests check
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

Native Lean execution semantics, full source/compiler/runtime correspondence,
backend correctness and complete protocol security remain open. Independent
[formal models](../lean/docs/support.md) retain their proved propositions and
model-specific tools. These do not validate the supported native path without
an explicit correspondence. [Assurance](assurance.md) defines how these kinds
of evidence may be reported.

## Scope of the supported package

Default build and execution checks cover C++/Rust. Formal builds and checks are
optional standalone work; LLZK remains a generic optional relation adapter.
Use [development](development/README.md) and the [test guide](../common/tests/README.md)
for current commands. [Roadmap](roadmap.md) records further work.
