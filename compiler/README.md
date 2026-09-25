# zkc compiler

C++/MLIR common-protocol, participant and physical compilation.
The [authored AIR/oracle examples](../examples/protocols/air-oracle/README.md)
exercise coset arithmetic, explicit field embedding, challenged composition,
authenticated queries and source-written FRI through the same pipeline.
`oracle-inspect` and `oracle-check` expose source dataflow and optional ordering
policies; they are not cryptographic security checkers.
[Readable source notation](../docs/language/reference.md) provides
`.pir` authoring, comments, formatting and diagnostics over the existing protocol
source. The [examples](../examples/protocols/README.md) can be compiled directly.
[Interactive execution](../docs/compiler/interactive-execution.md) explains
the authored source, independent roles, actual backend and assurance boundaries.
The earlier [finite table path](../docs/compiler/table-execution.md) remains
separately tested and uses its existing commands.
Its dialects and APIs are not frozen production interfaces. The
[compilation architecture](../docs/compiler/protocol-pipeline.md) owns the
representation boundaries and the implementation homes this path builds toward.

The [typed source model](../docs/compiler/source-model.md) serves text and
programmatic authoring through owned records and immutable documents.
The C++ frontend builds private syntax, checks a retained
[source-language model](../docs/compiler/frontend.md), then emits the
common model. `protocol-analyze` queries source types and uses, including partial
input; it does not claim common admission.
`protocol-parse` emits tagged syntax inspection, not portable common JSON or
admission evidence; text formatting needs complete syntax but no resolution;
`protocol-source` performs semantic admission. `protocol-explain`,
`protocol-inspect` and `--locations` expose actual requirements, selections and
MLIR locations.

The optional [execution-bound claim checker](../docs/compiler/claim-composition.md)
pairs original source with an independent caller contract and candidate derivation.
It exports registered `claim` MLIR and checks construction/physical custody;
body and cryptographic laws remain explicit caller premises.

## Build

The [development environment](../docs/development/README.md) is the supported pinned
setup. Enter `nix develop` for native CMake/Ninja iteration, or use
`nix build .#compiler` for the sandboxed installed package and compiler tests.

Use LLVM/MLIR 23, Clang, CMake and Ninja. Any 23 release configures; the
release the current evidence was produced with is `ZKC_TESTED_LLVM_VERSION` in
[`CMakeLists.txt`](CMakeLists.txt), and configuring with another one warns. GCC 13 is not a validated build
configuration: its `maybe-uninitialized` diagnostic in upstream generated
property hashing has not been revalidated after the include-path cleanup.
Compiler-owned code builds with `-Wall -Wextra -Werror`; dependency and generated
headers use system include paths.

From the repository root, the [`justfile`](../justfile) builds and tests this
compiler together with the [native workspace](../crates) and the
[formal library](../formal/README.md). It needs [`just`](https://just.systems):

```sh
just build    # CMake, Lake and Cargo builds
just test     # CTest, Rust, formal-library and documentation checks
just doctor   # tool versions in use against the recorded ones
```

The three builds are independent. The tests here run this build's tools and no
others, so `ctest` means the same thing wherever it is run; the tests that
compare this compiler against the native runtime or a Lean consumer live in
[tests](../tests), which resolves all three. A test names the tool it needs and
reads where it is from the environment, which the registration supplies, so
nothing is passed an executable path. The compiler alone builds with CMake:

```sh
cmake -S compiler --preset release
cmake --build build/compiler --parallel 4
ctest --test-dir build/compiler --output-on-failure
```

That registers and runs every test, with no option to set and nothing skipped:
a Python file in `compiler/test` is a test because it is there, and its name is
the test's name. Each takes no arguments: it names the tool it needs and
`compiler/test/support/tools.py` resolves it. Run one on its own with
`ctest --test-dir build/compiler -R NAME -V`.

Outside Nix, provide `MLIR_DIR` and select Clang with `CC`/`CXX` before using the
configure driver. Direct CMake calls can instead use an equivalent search prefix.
The `dev` preset retains project
assertions and debug information; `just test-sanitize` runs the native tests
under ASan and UBSan. Each preset has its own build directory.

What the tests write -- sources, plans, IR, and the record of every command
they ran -- stays in `build/reports/tests/compiler-test/NAME/`, so a failure
can be read after the fact rather than reproduced. `ZKC_REPORTS_DIR` selects the common report root and moves
that elsewhere, which is what CI does before keeping it.

Rust tests that cross into another build resolve the tools they need by name
through `crates/zkc-test-support`, and run like any other: a tool that is not
there is a failure naming the directory searched and the command that builds
it, not a test that is skipped. `just test-rust` builds all three and runs
them. Native test executables are under `build/compiler/test/`.

The driver bounds source input at 1 MiB and MLIR input at 64 MiB: textual MLIR
can be larger than the admitted source that produced it. Both readers reject
oversized input. These are resource limits, not protocol-security properties.

## Interactive protocol

For a first run, use the [proof walkthrough](../docs/getting-started.md).
The commands below expose each MLIR boundary of the smaller interactive example.
Run `just build` first, then from the repository root:

```sh
build/compiler/zkc-compile protocol-import examples/protocols/two-factor.pir > /tmp/common.mlir
build/compiler/zkc-opt --zkc-project-participants /tmp/common.mlir > /tmp/participants.mlir
build/compiler/zkc-opt --zkc-plan-participants /tmp/participants.mlir > /tmp/physical.mlir
build/compiler/zkc-compile protocol-export /tmp/physical.mlir > /tmp/participants.json
build/compiler/zkc-compile protocol-source examples/protocols/two-factor.pir > /tmp/source.json
target/release/zkc run-protocol /tmp/source.json \
  /tmp/participants.json examples/protocols/two-factor.inputs.json \
  formal/.lake/build/bin/interactive-protocol
```

`protocol-compile SOURCE` combines the same actual import/projection/physical
selection/export route. The host checks the actual candidate against the source
before constructing separate role runners. It uses real arkworks multilinear
commitments and OS challenges, with explicitly selected development setup.
Substitute `group-exchange.pir` and `group-exchange.inputs.json` for a
non-polynomial BLS G1 exchange. The latter has no cryptographic claim.

`protocol-admit` checks module/library or participant declaration formation;
construction descriptors require the construction path. External bodies prevent executable compilation.
The [carrier decision](../docs/compiler/carrier-consolidation.md) records
frontend profile convenience and the explicit-only execution boundary.

## Source projects

Pass explicit library roots with repeated `--library=FILE` options. The loader
captures source modules and relation assets before pure analysis. Exact dependency
identities, public exports and aliases are resolved before checking; imports do
not search the network or an ambient registry. See the
[source project guide](../docs/language/projects.md) and
[split examples](../examples/projects/README.md).

## Local algorithm calls

Local functions support `[site] let result = Helper(arguments);`. Generic
helpers and configurations take residual static arguments, for example
`[site] let y = Helper::<F>(x);`, under checked public requirements. Closed
functions can supply concrete identities or invoke closed configurations. Omitted
static arguments are inferred from operands or local result annotations, without
associated-member inversion, a global solver or backend search. `F: Field` adds a
capability; `F: domain Field` supplies only a sort. Protocol-local generic work
keeps explicit configurations, and `fn Name<>` remains distinct from `fn Name`.
Import retains native `func.call` structure; `--zkc-expand-algorithms` expands
acyclic calls before participant projection. `protocol-expand` emits the
expanded source and `protocol-algorithm-map` reports the original primitive and
nested call path. [Local composition](../docs/compiler/local-composition.md)
defines its canonical accounting, construction selectors and tested limits.

## Constrained generic libraries

The [generic carrier](../docs/compiler/specialization.md) supports
parameterized functions, checked requirements, partial configurations, explicit
semantic/implementation bindings, demand-driven specialization and code sharing.
Closed logical types retain their domains; physical types additionally retain
representations. A fixed MSB implementation can coexist with LSB storage through
actual checked conversions.

The readable [generic DLEQ](../tests/fixtures/generic-dleq.pir) and
[generic committed two-factor](../tests/fixtures/generic-committed-two-factor.pir)
fixtures contain reusable algorithms and their protocol compositions. For example:

```sh
build/compiler/zkc-compile protocol-source tests/fixtures/generic-dleq.pir > /tmp/library.json
build/compiler/zkc-compile protocol-compile /tmp/library.json > /tmp/participants.json
```

`protocol-prepare` instead produces a closed source-shaped view retaining original
configuration names, used by construction. It does not replace the original
library as source authority. Rust's [interactive host](../docs/runtime/inputs.md)
uses original source ports and explicit setup policies. The
[artifact host](../crates/zkc-tools/ARTIFACT.md) supports separate proof production
and validation with multiple configured keys. The installed operation/domain set
is finite; automatic performance search and raw elaboration/native refinement
proofs are separate future work.

## Finite table path

From the repository root:

```sh
build/compiler/zkc-compile import examples/tables/source.json > /tmp/table.mlir
build/compiler/zkc-opt /tmp/table.mlir \
  --pass-pipeline='builtin.module(lower-pir-to-plan)' > /tmp/table-plan.mlir
build/compiler/zkc-compile export /tmp/table-plan.mlir > /tmp/table-plan.json
target/release/zkc run examples/tables/source.json /tmp/table-plan.json \
  examples/tables/inputs.json formal/.lake/build/bin/table-protocol
formal/.lake/build/bin/table-protocol run examples/tables/source.json \
  /tmp/table-plan.json examples/tables/inputs.json
```

`zkc-compile compile SOURCE` combines import, direct conversion and actual export.
The example sends `[2,5]`, draws `3`, evaluates the original table and returns
`true`. Both executions retain the ordered sent/drawn events.

To select physical scalar preparation:

```sh
build/compiler/zkc-compile compile examples/tables/source.json \
  --physical=materialized > /tmp/table-physical.json
target/release/zkc run-physical examples/tables/source.json /tmp/table-physical.json \
  examples/tables/inputs.json formal/.lake/build/bin/table-physical-reference \
  --storage segmented
```

Use `--physical=lazy` for deferred evaluation. The explicit MLIR pipeline is
`builtin.module(lower-pir-to-plan,lower-plan-to-physical{mode=materialized})`.
It changes scalar values and region signatures to `!plan.scalar`, with
`plan.prepare` and `plan.invoke` operations, while retaining the logical input
context and compact control. Export serializes the actual converted body.
`run-physical` also accepts the same `--phase` and `--endpoint` options, before
trailing `--storage` options, with exact physical realization and policy
acknowledgment.

Add `--simplify` to `compile SOURCE --physical=lazy|materialized` to eliminate
`poly.linear(a, a, r)` when its two endpoint operands are the same SSA value.
The explicit pass is `simplify-table-regions`, before physical conversion, for
example `builtin.module(simplify-table-regions,lower-pir-to-plan,lower-plan-to-physical{mode=lazy})`.
It retains partial operations, calls and control, including unused producers.
Run the result with the **original source** and its original phase certificate.
Lean checks logical equivalence and physical representation together. The
[checking contract](../docs/compiler/targets.md#checked-logical-folding)
explains why direct-only compilation currently refuses `--simplify`.

Add `--phase table-round/1 examples/tables/phase-certificate.json` to the `zkc run`
command to require the installed send/draw phase discipline as well as direct
preservation. The consumer retains that certificate with the source and plan;
it does not alter the MLIR lowering. [Admission scope](../docs/compiler/phase-admission.md#native-table-admission)
explains the proved contract and native checks.

## Components

The build separates semantic services, frontend processing, IR, transformations,
compilation workflows and command handling. Arrows mean “depends on”:

```text
Compiler (interface aggregate) → CompilerCore, Driver
Driver → CompilerCore, FrontendLoading, MLIR parser
CompilerCore → Transforms, Frontend
Transforms → IR, MLIR passes and conversions
IR → Claims, MLIR IR and interfaces
Claims → Protocol → Relation → Contracts → Support → LLVM
Frontend → Protocol
FrontendLoading → Frontend
```

| Target | Responsibility and implementation homes |
|---|---|
| `Zkc::Support` | Bounded input, JSON/natural encoding and structured refusals in `Support` |
| `Zkc::Contracts` | Requirements, generic signatures, installed domains, operation contracts, representations and binding applications in `Contracts` |
| `Zkc::Relation` | R1CS/AIR data, identities, sparse matrices and AIR polynomial evaluation in `Relation` |
| `Zkc::Protocol` | Common `Source` records/codecs/snapshots, generated relation views, admission, generic preparation, source analyses and physical selection requests |
| `Zkc::Claims` | MLIR-free conditional claim analysis, derivation and checking in `Claims` |
| `Zkc::IR` | Dialects, operation interfaces, binding adapters, translation and mandatory root verification in `Dialect`, `Interfaces` and `Translation` |
| `Zkc::Frontend` | Captured-input resolution, checked authoring, static selection, retained analysis and common lowering in `Frontend` |
| `Zkc::FrontendLoading` | Bounded project and relation-asset loading in `Frontend/Loading` |
| `Zkc::Transforms` | SSA expansion, projection, physical conversion, target selection and storage in `Transforms`, `Conversion` and `Target` |
| `Zkc::CompilerCore` | Typed compilation, checked construction/claim workflows, inspection and pipeline/pass registration in `Compiler` |
| `Zkc::Driver` | Command options, file loading and output rendering in `Driver` |

The foundations have no MLIR, frontend or driver dependency. A contract
application contains the contract, static arguments and optional implementation;
a source binding adds its symbol and provenance. `Dialect/Bindings.h` adapts
those values to MLIR and owns the contract-to-operation mapping. Canonical type/codec/default implementation facts remain
in Contracts; these facts are not optimization policy.

Relation data can be used independently of a source program. Generated views,
portable codecs and admission stay together in Protocol because their checks
are mutually dependent: decoding materializes views, while generation and
admission validate their exact correspondence. Splitting those checks into
separate libraries would create a dependency cycle or weaken validation.

The IR target has no frontend, pass or driver dependency. Translation and root
verification stay together: reconstructing common source and admitting it is
part of checking a whole protocol, including exact generated relation bodies.
Public export remains checked. A valid local operation or root does not establish
source/candidate correspondence or readiness for every lowering.

Frontend has no MLIR, driver or filesystem dependency. It analyzes immutable
captured inputs and publishes an immutable checked snapshot; common admission
remains a separate judgment. `Frontend/Loading.h` provides the optional loading
API. Pure relation-asset decoding belongs to `Source/Relations.h` in Protocol.
The [frontend architecture](../docs/compiler/frontend.md) describes phase results,
generated entry checking and recovery. The component dependency check enforces
both library edges and private frontend layer dependencies.

IR registration lives under `Dialect/<Name>/IR`; interfaces live under
`Interfaces`. Shared type and operation declarations remain coordinated because
cross-dialect parent traits need shared forward declarations. `Dialect/IR.h` is
the convenience aggregate, while `Dialect/Registry.h` supports registration
without importing every operation declaration. `Translation/{Protocol,Table,Relations}.h`
exposes import/export and relation adapters; transformation APIs are separate.

[Compilation.h](include/zkc/Compiler/Compilation.h) provides typed protocol and
table requests. A `Compilation` owns its context and module; protocol results
also retain original source spelling and expansion origins. Table results have
no source `Document`. Moves preserve these lifetimes. `compileProtocol` checks
source-bound implementation choices before specialization and projection. Failed
calls return owned diagnostics, never a partially compiled artifact. The CLI uses
the same API. `Compiler/Source.h` freezes retained frontend output and prepares
source-name-preserving local algorithms.

Every failed coarse compilation or construction request returns one
`CompilationError`, carrying owned text, refusal identifiers/details and available
file coordinates after the MLIR context is destroyed. Upstream diagnostics
without a zkc code remain unclassified. An extension that emits an error but
reports success still fails the request; no partial artifact is published.

Construction retains both IR boundaries: the prepared original is imported and
verified before dependency analysis, and the emitted source is imported and
verified before publication. The pure preparation bridge is package-private;
[Compiler/Construction.h](include/zkc/Compiler/Construction.h) exposes the checked
low-level workflow with an explicitly initialized caller-owned context.
`constructProtocol(analysis, descriptor, registry)` in `Compilation.h` binds and
lowers from one captured frontend analysis, initializes an owned context, and
returns the constructed compilation and its certificate. This avoids pairing a
source-bound descriptor with another subject. Empty extension registries are
valid for the coarse workflows and `runCompiler`; table libraries remain opt-in.
[Compiler/Claims.h](include/zkc/Compiler/Claims.h) composes independent
caller contracts with construction and physical candidate checking.
[Translation/Claims.h](include/zkc/Translation/Claims.h) owns the analysis IR;
claim derivation itself needs no MLIR context.

Pass factories live in [Transforms/Passes.h](include/zkc/Transforms/Passes.h).
Aggregate registration lives in [Compiler/Passes.h](include/zkc/Compiler/Passes.h),
and pipeline builders in [Compiler/Pipelines.h](include/zkc/Compiler/Pipelines.h).
Linking transformation code does not register command-line passes. Target policy
selects among legal installed implementations; Contracts retains legality and
canonical authoring defaults.

The corresponding public headers live under `include/zkc/` and implementations
under `lib/`. A directory can contain files owned by different build libraries;
[Components.cmake](cmake/Components.cmake) assigns each translation unit exactly
once. `tools` contains thin entry points. `test` contains native API and CLI
checks, including a fast component dependency check. The independent
[service consumer](examples/service) exercises the finite table extension
interface; cross-language checks live in [tests](../tests/README.md).

An embedding application can request a particular component:

```cmake
find_package(ZkcCompiler REQUIRED CONFIG COMPONENTS CompilerCore)
target_link_libraries(my_compiler PRIVATE Zkc::CompilerCore)
```

For example, compile already-captured text without file loading or CLI options:

```cpp
#include "zkc/Compiler/Compilation.h"
#include "zkc/Compiler/Source.h"
#include "zkc/Frontend/Protocol.h"

llvm::Expected<zkc::Compilation> compile(llvm::StringRef text) {
  auto analysis = zkc::frontend::analyzeProtocol(text, "input.pir");
  auto source = zkc::lowerSource(analysis);
  if (!source)
    return source.takeError();
  mlir::DialectRegistry extensions;
  return zkc::compileProtocol(std::move(*source), {}, extensions);
}
```

The returned result retains its context and source after the local variables
above are destroyed. Access to `module()` borrows that result's context; a caller
must discard conclusions about the old module after mutating it. The default
request projects participants and selects a physical plan. `ProtocolAction`
also supports import, expansion and projection as stopping points.

`compileTable` is the separate finite-table route. Its registry must install the
chosen source-library interface, such as `registerTableLibrary`; an interactive
protocol's built-in operations do not select a table library implicitly.
`Zkc::Transforms` supports caller-owned MLIR contexts and pass factories without
frontend or driver linkage. `Zkc::Claims` supports conditional claim checking
without MLIR. `Zkc::Driver` preserves the command dispatcher for tool embedders.
`Zkc::Compiler` remains an optional aggregate of the application components.

The [installed consumers](../tests/consumer) exercise these targets separately,
including a service dialect generated from the installed TableGen declarations.
The installed-consumer build compiles each public header independently. Its
package tests reject unknown required components and allow unknown optional ones.
Private construction and claim-analysis records are deliberately not installed.

Interactive ODS is grouped by responsibility in shared `Types.td`/`Kernels.td`,
`PIR/IR/{Protocol,Participant}.td` and `Plan/IR/Physical.td`. Native symbol-use interfaces
resolve actual declarations and verify call signatures; kernel verifiers check
actual SSA kinds, profiles and representation parameters. Local region verifiers
check callable returns, message types and loop signatures even for standalone
declarations. Whole-module admission
retains ownership, affine-use, loop/capture, schema and instance-closure checks.
Physical conversion preflights representation changes before mutating SSA.
These checks establish structural admission; the independent source/candidate
checker supplies the separate portable correspondence check.

Owned MLIR properties (`<{...}>`) reject unknown keys before ODS conversion
can discard them (`mlir-unknown-property`). The shared dialect registration
adapter applies this check to both compiler and optimizer input and preserves
the generated operation identity and property layout. Ordinary discardable
attributes (`{...}`) remain a separate surface governed by each operation's
admission policy; a namespaced key does not make an unknown owned property valid.

[IR verification](../docs/compiler/ir-verification.md) maps local, whole-root,
stage and source-relative checking to their owners. Native refusals emitted
through [Dialect/Diagnostics.h](include/zkc/Dialect/Diagnostics.h) carry structured
identifiers in nonprinting MLIR metadata. Diagnostic handlers can inspect those
fields without parsing error text; unclassified MLIR/LLVM errors remain unclassified.

`cmake --install build/compiler --prefix PREFIX` installs tools, public headers
including generated headers under `include/zkc/`, and all component targets above.
Build-tree consumers can use the same `Zkc::` aliases. `Zkc::Compiler` links the
upper compiler and its dependencies without recompiling sources; a source-only
client links `Zkc::Protocol`; a direct IR client links `Zkc::IR` without the
frontend or passes. A captured-source client links `Zkc::Frontend`, adding
`Zkc::FrontendLoading` only to load external files. Static and shared builds use
the same target graph.
The package currently discovers the matching LLVM/MLIR installation even for a
foundation-only consumer; that consumer does not link MLIR or CompilerCore.
The independent [consumer](../tests/consumer/CMakeLists.txt) checks that API;
`just test-install` builds, installs and runs all component consumers and the
standalone service extension. Use `just test-install "" shared` for the shared
library variant. Physical table conversion is exposed through the pass factory;
its mutation helper `lowerToPhysical` is private to the conversion implementation.
This finite path does not yet
provide optimized protocol compilation, endpoint projection or cryptographic
challenge providers.

## Vector and polynomial domains

The explicit-binding compiler supports BLS12-381 Fr/G1 and
`ristretto255.scalar`/`ristretto255.group`. The latter group derives its scalar
field through the immutable installed domain catalog. The Ristretto transcript
identity is `merlin3.ristretto255.scalar64le/1`. Logical signatures, codecs and
representation applicability are independently checked in C++; native execution
and formal interpretations remain separate consumers.

Source `Vector<F::Element>` and `Vector<G::Element>` (common JSON `vector:F`
and `groups:G`) lower
to builtin `tensor<?x!algebra.field<F>>` and `tensor<?x!algebra.group<G>>`.
Only dynamic rank-one tensors with exact nominal field/group elements and no
encoding attribute are admitted. The old `!algebra.groups` MLIR type is removed;
logical source and JSON group-sequence spellings are unchanged. Static dimensions,
other ranks and other element types refuse. Tensor types do not assert equal
runtime lengths: each domain operation retains its shape obligations.

`Polynomial<F>` lowers to `!poly.univariate<F>` and denotes normalized ascending
coefficients. `poly.from_coefficients`, `poly.coefficients`, `poly.degree_check`,
`poly.univariate_evaluate` and `poly.univariate_boundary` operate on that carrier.
`Round<F>` remains the separate degree-two carrier, with fixed three coefficients.
General polynomials, rounds, scalar/vector arithmetic, scalar-action group
operations and matching transcript observations support both fields. Multilinear
tables, points/conversions and PCS remain BLS-only. Closed unsupported bindings
refuse before physical execution is advertised.

Installed logical contracts map to registered dialect operations through
[Dialect/Bindings.cpp](lib/Dialect/Bindings.cpp). Multiple payload contracts can
share an operation. The signature home is
[Kernels.cpp](lib/Contracts/Kernels.cpp); [Bindings.cpp](lib/Contracts/Bindings.cpp)
instantiates the generic contracts and checks independently installed physical
choices. [Domains.cpp](lib/Contracts/Domains.cpp) owns nominal identities,
associations, field moduli, codecs and applicable representations.

The shared local Boolean vocabulary includes `bool.and`, `bool.not` and
`bool.or`. All operands are already evaluated; these operations do not implement
short-circuit control or resource selection. They use no domain arguments or
attributes. Explicit bindings select the existing `arkworks/` provider with
`native.bool/1` representation, also in protocols using other field families.

`curve::get::<G>(groups, index)` and `curve::length::<G>(groups)` support BLS12-381
and Ristretto with exact nominal group bindings, no attributes, and the common
u64 `index` carrier. Static `curve.at` is unchanged. The generic
[batch-check fixture](../tests/fixtures/local-vocabulary.pir) composes a dynamic
lookup, group equality and a Boolean implication; a disabled check still
performs its lookup and preserves failure. Reference scalar-group execution has been retired; it is not another installed
curve backend.

Natural operation attributes are canonical unsigned decimal strings within the
64-bit unsigned range. `vector.gather` accepts zero or more indices;
`vector.matvec` requires exactly rows, columns and transpose (`0` or `1`).
Splat/powers/random-vector lengths, vector indices/exact-length checks and polynomial
degree bounds each require one attribute. Other new contracts take none. Generic
field constants are natural casts reduced at specialization using the selected
field modulus; closed constants must already be canonical for that field.

### Opt-in linear contraction selection

```sh
build/compiler/zkc-compile protocol-compile \
  tests/fixtures/linear-contractions.pir --linear-contractions > /tmp/linear.json
build/compiler/zkc-compile protocol-physical-ir \
  tests/fixtures/linear-contractions.pir --linear-contractions > /tmp/linear.mlir
```

The flag is off by default and prints producer, eligible-pair and selected-pair
counts on stderr, plus eligible/selected producer counts. A shared producer with
two consumers counts as two pairs and one producer. These are static counts
including retained, uncalled source functions, not execution counts. The
example selects two pairs:

| Logical producer → contraction | Selected representation | Implementation prefix |
|---|---|---|
| BLS `vector.mul` → `vector.dot` | `arkworks.fr-diagonal/1` | `arkworks-diagonal/` |
| Ristretto `curve.scale_each` → `curve.msm` | `dalek.ristretto-diagonal/1` | `dalek-diagonal/` |

The existing participant physical planner invokes the same optional-interface
analysis for both pairs. Every use of a producer result must be a same-function,
same-block contraction **values** operand, with matching
coefficient and element domains. Both logical operations, original sites,
attributes and operand order remain. Nothing moves across role actions,
random draws, transcript operations or stops. Each selected operation gets a
fresh binding; one producer and all its consumers are selected atomically.
Insufficient binding capacity or one fixed consumer leaves the entire group dense.
Unrelated uses of a source binding retain their dense choice.
Explicit source and `--implementations` selections take precedence.

The representation has depth one and dense factors/backing values. Function
results, serialization, loop/call escapes, unknown interfaces,
unsupported domains and unsupported consumers do not acquire a diagonal view.
Physical admission rejects diagonal ports, unsupported uses and unused diagonal
results, including in independently authored MLIR/JSON. A shared view is immutable
data; its reuse has no affine cryptographic semantics. These interfaces do not
mark operations pure/speculatable or implement the buffer `ViewLike` interface.

C++ callers use `zkc::protocol::lowerPhysical(module, selections, true, &stats)`;
`LinearContractionStats` and the read-only analysis are declared in
[LinearContraction.h](include/zkc/Transforms/LinearContraction.h). In a standard
MLIR pass pipeline, use `--zkc-plan-participants=linear-contractions=true` after
`--zkc-project-participants`. The pass prints the same stderr count summary;
`--mlir-pass-statistics` also exposes standard counters when the MLIR distribution
was built with statistics enabled.

The algebraic motivation is `Zkc.Algebra.linearCombination_smul`; this pass does
not automatically check that theorem or certify a native implementation.
Compare successful native runs with explicitly sufficient capacity and account
for retained factors/backing values. Under the installed conservative accounting,
a diagonal result charges strictly more bytes than its materialized result; the
intended benefit is avoided arithmetic/allocation, not reduced charged storage.
Equal exhaustion behavior is not asserted.
Compiler validation alone does not validate a protocol client. See the
[extension guide](../docs/compiler/protocol-libraries.md) for library, dialect
and backend responsibilities.


### Construction and local computations

Explicit-binding source supports the installed BLS and Ristretto construction
suites with exact or normalized source identity. The selected validator RNG and
every selected draw must have the suite's associated challenge field. BLS profile text elaborates to the same explicit-binding source. Catalog membership alone does
not imply constructor support; no encoding/reduction convention is changed.

Construction preserves a whole local call when none of its operations needs
challenge substitution or other-role recipe replay and all argument/result and
operation ports have duplicable custody. Resource-bearing calls keep
the existing expansion path. Each preserved occurrence gets a distinct cloned
function, every operation retains its original site/order/attributes, and the
manifest contains one original-source origin row per operation. Guards remain
at their source positions; unknown replay recipes are not inferred from algebra.

The prescribed output and generated names change when a call is preserved.
Recompute the construction manifest and physical candidate from original source;
exact candidate checking is unchanged. The manifest's eight-column origin-row
schema is unchanged. Preservation changes local frame counts and intermediate
value lifetimes, so resource-limit equality with old construction is not claimed.
Always inspect selected operations in reached constructed calls as well as static
selection counts. Native execution and independent source/candidate checking
remain separate validation obligations.

### Local immutable storage release

Add `--release-storage` to `protocol-compile` or `protocol-physical-ir` to emit
physical `plan.release` instructions after the last SSA use of discardable local
values. Unused discardable inputs release at local entry, unused discardable results
just after production, and returned values escape. The corresponding pass option
is `--zkc-plan-participants=release-storage=true`.

Kernels, original observations, ticks, logical live/cumulative charges and budget
failures remain unchanged. Rust keeps scalar ghost charges until local exit while
dropping environment references. Affine resources never release early. Immutable private keys and opening states
may release their local references without acquiring a wire codec. The [storage contract](../docs/compiler/interactive-execution.md#ordinary-local-storage-lifetime)
defines admission, inert destruction assumptions and the distinction between
physical storage and logical accounting.

`PhysicalOptions.releaseStorage` is also accepted by `claims::checkLowering`;
its CLI flag is `claim-check-lowering ... --release-storage`. Candidate checking
recomputes the selected pipeline against original source and caller authority.
Independent Rust/Lean admission rejects early or resource releases even when an
external compiler or checker supplies the candidate.

## Authored compiled relations and Groth16

The [relation authoring guide](../docs/language/relations.md)
defines explicit source declarations, bounded resolution, frozen snapshots,
native relation symbols and checked view materialization. The
[composition example](../examples/relations/README.md) exercises R1CS and AIR
through ordinary local/subprotocol calls. The Groth16 consumer compiles visible
PIR algorithms and imports snarkjs prepared keys into arkworks-backed operations;
it does not call an opaque prover. Its verifier can run independently from cached
code and public inputs.
