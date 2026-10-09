# What the implementation supports

The supported implementation is `.zkc` Language → mathematical MLIR
(`protocol`, `participant`, `exec`, `physical`) → `zkc.program/2` → a shared Rust
Runner with Entry/proof/joint Hosts. Direct MLIR enters the same compiler.
[Specification](spec/README.md) defines contracts; this page records support.
Links identify maintained checks, not a claim that they ran for this revision.

## Current public interfaces

Artifacts use one current schema with exact tags, record shapes and unknown-field
validation. Boundary versions remain fixed during development; equal versions do
not guarantee compatibility across builds. Their specification owners define the
accepted contents; the [maintenance policy](development/maintenance.md#format-versions)
defines when versions change.

| Interface | Contract |
|---|---|
| Executable program | [`zkc.program/2`](spec/profiles/compiler/program.md), a physical participant program |
| Source Entry | [`zkc.entry/1` and `zkc.language-interface/7`](spec/profiles/source/mathematical-language.md#published-entry-package), authenticated source, input/result schemas and selected artifact |
| Joint execution | [`zkc.run/1`](spec/profiles/compiler/run.md), participants, schedule and invocation policy |
| Native proof | [Policy, descriptor, deployment, construction map and invocation binding](spec/profiles/compiler/native-proofs.md), with `zkc.native-origin/2` occurrences |
| Installed declarations | [`zkc.contract-declarations/3`](compiler/operation-contracts.md), declaration inventory; the language catalog contributes an opaque compiler fingerprint |

Use `zkc run`, `prove` and `verify` for named Entries, and `run-bundle`,
`prove-bundle` and `verify-bundle` for lower-level artifacts. In the C++ SDK,
`Zkc::Compiler` owns compilation and packaging;
`Zkc::Driver` separately owns CLI parsing. Request `Tools` for installed commands.
See the [SDK reference](../compiler/README.md#components-and-ownership).
Rust package, run and deployment admission take trusted 32-byte SHA-256 pins;
CLI adapters own hexadecimal spelling. Backend service installation uses
`service_support` returning a named `ServiceSupport` signature and reply bound.

## Source and application boundary

Language resolves explicit modules and R1CS/AIR Assets, checks generic libraries
and closes selected Entries. It supports scalar mathematics, Boolean formulas,
nominal products/variants, static parameters and components, capabilities and
permissions, formal polynomial intrinsics, local control, messages, services,
static protocol composition, bounded repetition and conditional completion.
Independent source comparison checks emitted MLIR against checked definitions;
[source semantics](spec/profiles/source/mathematical-language.md) owns exact limits.

An authenticated `zkc.entry/1` package retains the original, source interface,
compilation choices and selected artifact. The Host binds named logical inputs
and results to the independently admitted program. It trusts compiler publication
for source correspondence; it does not interpret retained MLIR. Maintained
[Schnorr and Sumcheck projects](../examples/projects/README.md) exercise this path.

Fixed source arrays use static numeric indexing. Private ingress without an
admitted validator, member-generic conformance and zero-leaf messages refuse.
Relation and target/input/output/continuation clauses state intent; declarations
alone add no runtime guard, satisfaction fact or security theorem.

## Foundation capability map

| Capability | Support and boundary |
|---|---|
| Scalar, tensor and polynomial mathematics | Total expressions and checked realization recipes; [structured mathematics](compiler/structured-mathematics.md). Kernel installation alone does not supply a mathematical recipe. |
| Calls, roles and control | Static application, role projection, structured local control, nested repetition and [conditional completion](compiler/entry-completion.md). General dynamic protocol composition remains open. |
| Structured values | Products, alternatives, extents, checked indexing and [nested immutable data](compiler/nested-data.md), including independently shaped matrices; affine sequence elements are excluded. |
| Affine resources and services | Exact-origin analysis, state successors, resource custody, entry service aliases and failure cleanup; [resource origins](compiler/resource-origins.md). Equal roots do not prove equal state or independent randomness. |
| General numerical composition | Installed field/group/vector/matrix, polynomial, pairing and oracle kernels with [composed clients](compiler/mathematical-composition.md) and [changing numeric state](compiler/composed-state.md). These are not complete Groth16, AIR/FRI or range-proof applications. |
| Relations | Bounded R1CS/AIR data import and Assets, exact [relation bindings](compiler/relation-bindings.md), and a [native R1CS reduction adapter](compiler/relation-composition.md). Import does not prove upstream source adequacy. |
| Native proofs | Separate producer/validator execution, derived or authored transcripts, structured framing and authorized setups; [proof contract](compiler/native-proofs.md). One policy covers flat, iterated, PCS and structured programs in `zkc.program/2`. |
| Attempts and retained work | [Persistent attempts](compiler/native-attempts.md) retain provider state, failed work and unpublished buffers under explicit application policy. |
| Authored transcripts | Explicit external initialization, trial/live checks and snapshots under [authored transcript contracts](compiler/authored-transcripts.md); admission does not prove transcript completeness or snapshot reachability. |
| Host applications | Named Entry inputs/results, joint bundles, proof jobs, reusable immutable prover material and generated Rust data bindings through the common Hosts; [Entry guide](language/entries.md). |

Setup authority comes from Entry input associations and the Host registry.
Decoding accepts matching metadata for an authorized key; `pcs.check` consumes
the explicit verifier key and enforces the terminal's expected key and arity,
possibly after observation. Unchecked returned PCS data need not belong to a
particular output setup. The [setup contract](spec/profiles/compiler/structured-proof-messages.md#application-authorized-setups)
states the exact boundary.

Registered services cover four RNG distributions/providers. Arbitrary user-defined
request/reply service families remain an extension. Domain and kernel contributions
require their own implementation and installation. Constant-time MSM and diagonal
contractions are supported; automatic contraction selection is an explicit
[optimizer/planner option](compiler/representation.md#checked-physical-decisions),
disabled by the Entry compile path.

### Compiler limits

| Boundary | Limit |
|---|---|
| Declared role roster | 1,024 roles |
| Helper depth and expanded helper analysis | 64 levels; 100,000 operations |
| Helper dependency analysis and availability replay | 1,000,000 words/indices within their separate budgets |
| Role expansion | 100,000 operation/port visits |
| Exact resource-origin analysis | 100,000 shared work units and 64 call/region levels |
| Native R1CS reduction adapter | BLS Fr; at most 8 rows, 128 columns and 1,024 nonzero terms |

Source expansion, runtime value capacity, wire size and execution work have
independent bounds. Larger bulk-kernel tests do not expand the scalar R1CS
adapter's envelope. Every original helper is checked before erasure, including
unreferenced private definitions. Unknown roots refuse independently of budget
exhaustion. The owning profiles define additional operation-specific limits.

## Checking and evidence

[Preservation](compiler/preservation.md) compares adjacent compiler subjects,
including actual receives, ordered action operands, region interfaces, physical
materialization and emitted program content. Rust independently admits the
executable and Host envelope. Bounded tests exercise source/IR mutations, native
execution, framing, failures, capacity and installed consumers. The
[validation map](compiler/foundation-validation.md) records those scopes.

Optional polynomial checks cover `boolean-sum-to-point/1` and relation-pinned
`r1cs-sum-to-point/1`. [Public-coin analysis](compiler/public-coin.md) checks a
selected verifier's dependencies against bound public context, challenges and
receives. Neither establishes a Fiat–Shamir reduction or arbitrary polynomial
or protocol equivalence.

Native Lean execution semantics, full source/compiler/runtime correspondence,
backend correctness and complete protocol security remain open. Independent
[formal models](../formal/SUPPORT.md) retain their proved propositions and
model-specific tools. These do not validate the supported native path without
an explicit correspondence. [Assurance](assurance.md) defines how these kinds
of evidence may be reported.

## Scope of the supported package

Default build and execution checks cover C++/Rust. Formal builds and checks are
optional standalone work; LLZK remains a generic optional relation adapter.
Use [development](development/README.md) and the [test guide](../tests/README.md)
for current commands. [Roadmap](roadmap.md) records further work.
