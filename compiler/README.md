# zkc compiler

The compiler implements one model:

```
.zkc Language → Protocol IR → generic participant programs
```

Language captures explicit module buffers and relation Assets, checks declarations
and closes a selected Entry. Translation emits a mathematical `protocol.module`.
Preparation expands local applications and protocol applications; projection
assigns actions and values to participants. Mathematical lowering produces the
`exec` profile. Representation and kernel selection produce `physical` programs,
exported as `zkc.program/0` for the generic participant runtime.

## Build and validate

Use the repository [development guide](../docs/development/README.md) and
[test guide](../tests/README.md#selecting-checks). A matching LLVM/MLIR installation
and utf8proc 2.12.0 are required. Configure CMake with
`-S compiler -B BUILD -DMLIR_DIR=... -Dutf8proc_DIR=...`; build
with `cmake --build BUILD -j4` and run `ctest --test-dir BUILD --output-on-failure`.
The same source supports static and shared libraries. Install into a fresh prefix
with `cmake --install BUILD --prefix PREFIX` and build `tests/consumer` against
that prefix to check every component and installed public header.

## Public commands

`zkc-compile --help` lists the supported commands. The primary Language commands
are `language-check`, `language-emit`, `language-interface`, `language-bundle`,
and `language-package`, with explicit `--module=NAME=FILE.zkc`, selected Entry,
and optional `--asset=NAME=FORMAT=FILE` inputs. `language-check` may omit the
Entry to check definitions alone; `--declarations` reports completed public
callable contracts. The separate
[notation inspection surface](../docs/language/notation.md#inspect-notation-and-locations)
provides `--notations` and explicit private/installation visibility options; its
completion status is tracked in [status](../docs/status.md#source-and-application-boundary).
`zkc check` and `compile` also accept an explicit
[project map](../docs/language/README.md#project-inputs). Language Assets retain binary R1CS
and AIR data ingress without generating an intermediate authored language.

For Protocol IR, `protocol-bundle` compiles a run. `protocol-checked-bundle`
additionally checks supplied polynomial or public-coin requirements.
`protocol-public-coin`, `protocol-check-public-coin`, and
`protocol-check-reductions` expose the corresponding analyses.
`protocol-proof`, `protocol-construct-proof`, and `protocol-check-proof` use
the native proof policy, descriptor and deployment schemas. Unknown tags and
malformed records refuse. Transcript construction uses
indexed origin templates, `transcript.native.indexed.challenge`,
`transcript.native.indexed.index` and typed
`transcript.native.indexed.observe.data`; loops and flat protocols share this
model. An empty suite selects an authored proof without constructed transcripts.
`protocol-export` emits a checked physical `zkc.program/0` artifact.

Relation data commands retain R1CS import/export, normalization, inspection,
matrices, evaluation, and native Sumcheck authoring (`relation-protocol` and
`relation-requirements`). The `relation-air-*` commands retain AIR inspection,
import/export, evaluation and polynomial planning. The isolated
[LLZK adapter](adapters/llzk) emits relation data. The external
[accumulator-machine adapter](adapters/accumulator-machine/README.md) emits an
example multi-table Bundle with staged reductions.

There is no JSON-program-to-MLIR importer. `protocol::exportProgram` returns
checked typed Program records; `protocol::exportModule` returns the checked
physical JSON carrier. Program codecs read only
`zkc.program/0`, the physical executable carrier, with explicit participant
arguments.

## Components and ownership

| Installed component | Public header roots | Responsibility |
| --- | --- | --- |
| `Zkc::Support` | `Support/` | Refusals, JSON, bounded input helpers and diagnostic spans |
| `Zkc::Contracts` | `Contracts/` | Types, capabilities, operations, named bindings, representations and installed implementations |
| `Zkc::Relation` | `Relation/` | Pure R1CS/AIR data, normalization, evaluation and matrices |
| `Zkc::Language` | `Language/` | Immutable `.zkc`/Asset capture, syntax, checking and Entry closure |
| `Zkc::Program` | `Program/` | Shared participant records, native local-definition view, bounded codec and admission |
| `Zkc::IR` | `Dialect/`, `Interfaces/` | Dialects, mandatory profile verification, type adapters and interfaces |
| `Zkc::Translation` | `Translation/` | Language-to-math emission/comparison, relation ingress and checked program export |
| `Zkc::Transforms` | `Transforms/`, `Target/` | Mathematical preparation/projection, local expansion, polynomial lowering and physical selection |
| `Zkc::Compiler` | `Compiler/` | Owned compilations, run/proof packaging, public-coin/polynomial checks and pass registration |
| `Zkc::Driver` | `Driver/` | CLI parsing and input loading |

Header paths are relative to `zkc/`. C++ namespaces express semantic subjects;
`zkc::protocol` spans several components and does not identify a link dependency.
The `Tools` package component imports `Zkc::zkc-compile`, `Zkc::zkc-opt` and
`Zkc::zkc-tblgen`; it has no `Zkc::Tools` library target.

Support, Contracts, Relation and Program use LLVM without MLIR. Language also
requires the pinned external utf8proc library for NFC; it depends on Contracts
and Relation and still has no MLIR dependency. Program depends on Contracts.
IR adds MLIR and depends on Program and Relation. Transforms depends on IR; Translation depends on IR and Language; Compiler depends on Transforms
and Translation; Driver depends on Compiler. Compiler does not link CLI Driver.
Tools imports Driver's dependency closure.

### Installed package discovery

Request the components the consumer uses. For an LLVM-only program client:

```cmake
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Program)
add_executable(client main.cpp)
target_link_libraries(client PRIVATE Zkc::Program)
```

This works with `CMAKE_DISABLE_FIND_PACKAGE_MLIR=TRUE`. A matching LLVM package
is required: the exact LLVM version used to build the SDK is asserted even for
LLVM-only requests. Native components additionally discover MLIR and installed
contribution dependencies. The SDK retains these external installations rather
than bundling them. Static and shared libraries use the same component contract;
install into a fresh prefix and relocate the entire prefix together.

For source capture, checking and inspection without MLIR:

```cmake
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS Language)
add_executable(source_client main.cpp)
target_link_libraries(source_client PRIVATE Zkc::Language)
```

Provide utf8proc 2.12.0 through `CMAKE_PREFIX_PATH` or `utf8proc_DIR` as well as
the matching LLVM installation. Language discovery requires that exact version
and its `utf8proc::utf8proc` CMake target for both static and shared consumers;
the SDK does not bundle the dependency. A missing or incompatible dependency
makes Language and its dependent components unavailable. A preloaded target or
explicit package directory cannot silently select a different version. This
request works with `CMAKE_DISABLE_FIND_PACKAGE_MLIR=TRUE`.

The [Unicode manifest](../support/unicode/manifest.json) pins raw UCD hashes and
normalizers: utf8proc 2.12.0 for C++, `unicode-normalization` 0.1.25 for Rust.
Classification is generated offline from Unicode 17.0.0 inputs, independently
of either normalizer's repertoire. The manifest, generator and raw inputs enter
compiler build identity. NFC preserves exact admitted source spelling; see the
[lexical contract](../docs/spec/language/lexical.md).

Component names are case-sensitive. Unknown required components make discovery
fail; optional unknown components report `ZkcCompiler_<component>_FOUND=FALSE`.
Known optional native components also report false when MLIR or a contribution
dependency is unavailable, while required LLVM-only components remain usable.
Missing dependencies or incompatible LLVM/MLIR versions make the affected
components unavailable. Required components make the package not found; `REQUIRED`
package requests fail configuration. An explicit `LLVM_DIR` or `MLIR_DIR` is not
silently replaced with another installation. Native discovery preserves upstream
LLVM/MLIR build variables, including `MLIR_CMAKE_DIR` and `MLIR_TABLEGEN_EXE`, for
external dialect consumers. Damaged installations remain errors.
Without a component list, discovery requires `Compiler` and
`Tools`, importing the complete SDK. Repeated requests can add components in the
same CMake directory; they preserve existing imported targets and include paths.
Requests cannot mix targets from different SDK installations or replace known
components with caller-created targets. Consumers invoking installed generators
explicitly request `Tools`.

`OperationContracts` is a facet aggregate: initialize its fields directly when
constructing records. Aggregate construction does not install an operation or
validate its semantics; installed queries and contribution admission retain
those responsibilities.

`Program/Model.h` contains `zkc::program` records. `LocalDefinitions` is an internal
structural view used to check mathematical local callables, with `LocalApply`
representing native `local.apply` before expansion; it has no authored carrier.
`Contracts/Binding.h` owns named operation bindings and assignment pairs.
Program records carry no diagnostic locations. Language diagnostics retain
source spans; MLIR operations retain their own locations. Physical selection
accepts explicit pass parameters. `Compilation` owns its context, module and
statistics. `verifyProgramArtifact` returns the admitted program after comparing
it with physical SSA, so consumers can reuse the checked records.

`registerDialects` installs the native dialect set and contributions. The
protocol, local, data, crypto, algebra, polynomial, oracle, PCS, relation and Plan
dialects are registered. Plan describes native selected representations and
kernels. Registration does not grant profile admission or transformation correctness.

## Transformations and checks

The native profile progression is `protocol → participant → exec → physical`.
Profiles and mandatory formation/export checks select the semantics. Participant
arguments are explicit ports; kernel operation parameters are static operands.
Unknown properties refuse admission.
`zkc-opt` exposes individual preparation, projection, polynomial and physical
passes, and the `zkc-participant-pipeline` convenience pipeline. Its
`project-only`, `linear-contractions` and `release-storage` options select the
corresponding native behavior. Explicit binding selections are honored by
`zkc-select-physical` and the C++ selection APIs. Automatic linear contractions
are opt-in through the optimizer or C++ selection API; Entry compilation uses
the default selection policy. Constant-time MSM and diagonal contraction
implementations are selectable.

Local calls retain structured conditionals, bounded loops, variants, affine
resources, stopping checks and storage release. Physical planning validates the
whole proposal before materialization, including per-use layout conversions,
fixed choices and diagonal contraction groups. Shared primitives such as table
folding, vector operations, matrix identity checks and PCS kernels remain
ordinary local operations.

The native checks compare actual inputs and candidates under declared operation
meanings. They do not establish backend cryptographic security or general
resource-bound equivalence. Public-coin and polynomial analyses keep their own
scope and refusal conditions. Lean research remains independent.

The [domain contribution example](examples/domain) demonstrates native nominal
types, adapters and reversible local specialization using an installed package.

Native service queries use the four registered random-distribution contracts
and their Host providers. Arbitrary user-declared request/reply service families
are outside this API. Domain contributions
retain logical type/operation declarations, adapters and transformations; a
logical-only contribution does not acquire a physical implementation implicitly.
