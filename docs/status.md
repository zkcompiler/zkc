# What the implementation supports

The supported implementation is `.zkc` Language → mathematical MLIR
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

Language resolves explicit modules and R1CS/AIR Assets, checks generic libraries
and closes selected Entries. It supports scalar mathematics, Boolean formulas,
nominal products/variants, static parameters and components, capabilities and
permissions, lexical scopes and patterns, mutable bindings with inferred region
state/captures, statement-scoped participant inference, nested ordered calls,
helper result inference, expression-wide structural type constraints, partial
static arguments, inferred catalog/natural
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
Resource permission inference, implicit role remapping, natural equation solving
and inversion of associated types are outside the source profile.
Relation and target/input/output/continuation clauses state intent; declarations
alone add no runtime guard, satisfaction fact or security theorem.

## Foundation capability map

| Capability | Support and boundary |
|---|---|
| Scalar, tensor and polynomial mathematics | Total expressions and checked realization recipes; [structured mathematics](compiler/mathematics.md). Kernel installation alone does not supply a mathematical recipe. |
| Shared expression evaluation | Captured [Ring and Bundle terms](spec/language/definitions.md#asset-domains-and-projections), derived static dimensions, retained Entry assets and independent Host preflight. [Checked structural sharing](spec/domains/ring-expressions.md#structural-sharing) preserves ordered substitution and read obligations. The [generic Sumcheck library](../libraries/README.md#expression-sumcheck) derives its width and degree from its Ring parameter; it remains a public-table client without a PCS or native security theorem. |
| Source clients of imported AIR | The [imported AIR client](../examples/projects/imported-air/README.md) checks actual trace, configuration and public inputs. The [AIR STARK client](../examples/projects/air-stark/README.md) adds base-field trace commitments, scoped extension-field quotient chunks, OOD/DEEP equations and FRI through ordinary source libraries and separate proof Hosts. The single-table profile covers one present table's assertions; the machine profile adds whole-Bundle Boolean multiset interactions. Security reductions for both remain separate work. |
| Pointwise vector maps | Source `map` applies one static scalar `math fn` over installed field vectors through [checked bulk vector operations](spec/ir/protocols.md#checked-pointwise-maps): shapes first and O(formula) code. The matcher reads the generated body independently but shares the realizer's formula derivation. Shape mismatches are backend failures (`rejected:require`); field constants, addition, subtraction and multiplication are limited to Ring depth 1,024. The [KoalaBear/Ext8 comparison](../tests/kernels/test_pointwise_polynomials.py) checks maps, Ring rows and coefficients, and coset kernels against integer arithmetic, including the off-domain interpolation distinction. [Lean map laws](../formal/Zkc/Algebra/RingExpression/Pointwise.lean) cover values, refusals and realization for a list model, without native correspondence. There is no dedicated row kernel, backend ABI or first-class function value. |
| Calls, roles and control | Static application, role projection, structured local control, nested repetition and [conditional completion](compiler/control.md). General dynamic protocol composition remains open. |
| Structured values | Products, alternatives, extents, checked indexing and [nested immutable data](compiler/mathematics.md), including independently shaped matrices; affine sequence elements are excluded. |
| Affine resources and services | Exact-origin analysis, state successors, resource custody, entry service aliases and failure cleanup; [resource origins](compiler/resource-origins.md). Equal roots do not prove equal state or independent randomness. |
| FRI source library | [Binary FRI](../examples/projects/fri/README.md) over natural-order two-adic cosets, with commitment/fold/query/terminal checks and independent-reference tests. The AIR library consumes the authenticated positions and values. Security theorems remain separate obligations. |
| General numerical composition | Installed field/group/vector/matrix, polynomial, pairing and oracle kernels with [composed clients](compiler/mathematics.md) and [changing numeric state](compiler/mathematics.md). Complete Groth16 and range-proof applications remain separate work. |
| Relations | Bounded R1CS/AIR data import and Assets, exact [relation bindings](compiler/relations.md), a [native R1CS reduction adapter](compiler/relations.md), and an isolated [Plonky3 AIR adapter](../compiler/adapters/plonky3/README.md) checked differentially against its pinned upstream. Import does not prove upstream source adequacy. |
| Multi-table relations | [Relation bundles](spec/domains/relation-bundles.md) have independent C++ and Rust admission and evaluation of deterministic data and challenge-dependent staged predicates. Captured Bundles retain an explicit source relation ABI, table/public/channel counts, polynomial facts, interaction descriptors and simultaneous record substitution. The external [accumulator-machine adapter](../compiler/adapters/accumulator-machine/README.md) supplies a CPU/program/memory relation and independent staged LogUp/grand-product references. The [source machine proof](../examples/projects/accumulator-machine/README.md) commits base, auxiliary and quotient columns, checks OOD identities and composes one FRI instance. Its selected profile has three tables with independent two-adic heights, optional presence and global all-row Boolean multiset interactions. Arbitrary table counts and other interaction profiles remain library work; relation adequacy and cryptographic soundness are not established by these executions. |
| Clean export comparison | A [pinned Clean flat AIR export](../formal/integrations/clean/README.md) is compared with native finite-AIR evaluation and the KoalaBear/Ext8 ring provider on fixed honest, invalid and mutated rows. This checks native agreement on those rows; it does not prove the native decoders correct. |
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
[validation map](../tests/native.md) records those scopes.

Optional polynomial checks cover `boolean-sum-to-point/0` and relation-pinned
`r1cs-sum-to-point/0`. [Public-coin analysis](compiler/public-coin.md) checks a
selected verifier's dependencies against bound public context, challenges and
receives. Neither establishes a Fiat–Shamir reduction or arbitrary polynomial
or protocol equivalence.

Native Lean execution semantics, full source/compiler/runtime correspondence,
backend correctness and complete protocol security remain open. Independent
[formal models](../formal/docs/support.md) retain their proved propositions and
model-specific tools. These do not validate the supported native path without
an explicit correspondence. [Assurance](assurance.md) defines how these kinds
of evidence may be reported.

## Scope of the supported package

Default build and execution checks cover C++/Rust. Formal builds and checks are
optional standalone work; LLZK remains a generic optional relation adapter.
Use [development](development/README.md) and the [test guide](../tests/README.md)
for current commands. [Roadmap](roadmap.md) records further work.
