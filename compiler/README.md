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

- `include/zkc/Dialect`, `lib/Dialect`: ODS types, concrete operations and verifiers.
- `Frontend`: recoverable syntax, static construction, retained source semantics
  and queries, explicit common lowering, shared admission, readable printing and
  comment-preserving formatting. Portable common JSON has a separate decoder.
- `Source`: owned common records, immutable documents, diagnostic origins and
  portable codecs. Semantic algorithms consume records rather than JSON slots.
- `Interfaces`: source descriptor export from actual operations.
- `Analysis`: bounded reusable obligation closure, independent of MLIR.
- `Claims`: caller-owned requirements, source-bound predicates and registered
  analysis IR; see [claim composition](../docs/compiler/claim-composition.md).
- `Relation`: structured R1CS/AIR ingestion, checking and protocol-consumer emission.
- `Compiler/Library`: closed dependency resolution and shared library interface.
- `Compiler/TableLibrary`: the finite table implementation of that interface.
- `Compiler/Requirements`, `Compiler/Instantiation`: finite public requirement
  checking and source-owned generic configuration/specialization.
- `Protocol`: interactive source/participant admission, actual SSA import/export,
  mechanical participant projection and physical backend selection. `Kernels.h`
  owns the kernel/type registry API; `Module.h` exposes import/export,
  projection and physical-lowering functions.
  Construction separates availability, resource-origin analysis and emission
  into private implementations sharing one invocation and work budget.
- `Target`: exact array/natural parsing, structured import and actual plan export.
- `Conversion`: direct control selection and physical scalar type/operation conversion.
- `Transforms`: logical rewrites under an installed interpretation, before representation lowering.
  [Passes.h](include/zkc/Transforms/Passes.h) exposes factories and explicit registration.
- [Compiler/Pipelines.h](include/zkc/Compiler/Pipelines.h): shared table/participant
  builders and named optimizer pipelines, used by tools and installed consumers.
- `tools`: thin compiler and optimizer entry points.
- `test`: tool-level roundtrip and malformed-IR controls; cross-language tests live
  in the repository's top-level [tests directory](../tests/README.md).
- `examples/service`: independently registered count/vector/predicate operations;
  also builds against the installed package. See [library boundaries](../docs/compiler/libraries.md).

Interactive ODS is grouped by responsibility in `Types.td`, `Protocol.td`,
`Participant.td`, `Kernels.td` and `Physical.td`. Native symbol-use interfaces
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

`cmake --install build/compiler --prefix PREFIX` installs tools, public headers
including generated headers under `include/zkc/`, and `Zkc::Compiler`. Build-tree
consumers link `ZkcCompiler`; dependency includes propagate through that target.
The independent [consumer](../tests/consumer/CMakeLists.txt) checks that API;
`just test-install` builds, installs and runs it. This finite path does not yet
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

All new contracts have individual logical dialect operations. The signature home
is [Library.cpp](lib/Protocol/Library.cpp); [Bindings.cpp](lib/Protocol/Bindings.cpp)
instantiates the generic contracts and checks independently installed physical
choices. [Domains.cpp](lib/Protocol/Domains.cpp) owns nominal identities,
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
