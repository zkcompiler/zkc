# Repository layout

Only directories containing implemented components exist. This separates build
ecosystems while keeping each component's implementation and tests together. The
selected semantics live in `docs/` and `formal/`, and the name of a study never
becomes the name of a module. Final production carriers and APIs remain under the
[compiler design](../compiler/design.md).

## 1. Source tree

```text
docs/                         selected model and engineering reference
  language/                        protocol authoring and source libraries
  guides/                          semantic explanations and worked examples
  compiler/                        compiler representations and transforms
  runtime/                         execution, backends and concrete formats
  spec/                            normative contracts and clause ownership
  rationale/                       why a choice is the way it is
  development/                     setup, repository conventions and maintenance
    README.md                      build, test and editor entry points
    configuration.md               tool selection, concurrency and reports
    layout.md                      source tree, naming and dependencies
    extensions.md                  adding implementations and integrations
    maintenance.md                 toolchain upgrades, caches and CI
    documentation.md               document ownership and editing rules
formal/
  lakefile.toml, lean-toolchain, lake-manifest.json
  Zkc.lean                         small semantic foundation import
  Zkc/
    Semantics/                     outcomes, interaction, contracts, observation
    Source/                        finite typed source, admission, denotation
    Modules/                       state, frames, installation, preparation
    Compiler/                      analyses, transformations, evidence checking
    Probability/, Properties/      laws, experiments, property transport
    Realization/                   value/state relations and lowering contracts
    Protocols/                     actual protocol theorem clients
  Tests/                           discriminating controls and axiom audits
  Tools/                           executable checkers and reference interpreters the tests run
  Examples/                        worked clients of the library
  checks/                          drivers for the formal controls
  design/                          design records for the formal package
  consumers/                       independent packages that build against the library
  integrations/                    separate optional packages when implemented
    arklib/                        external mathematics
compiler/
  CMakeLists.txt, CMakePresets.json
  cmake/
  include/zkc/
    Dialect/                       registered dialects
    Frontend/, Source/             authoring language and common source
    Protocol/, Relation/, Claims/  protocols, relations and claims
    Analysis/, Transforms/, Compiler/, Target/, Interfaces/, Support/
  lib/                             mirrors public include components
  tools/                           zkc-opt.cpp, zkc-compile.cpp
  test/                            tool-level roundtrip and malformed IR
  adapters/                        optional external toolchains, built separately
crates/
  zkc-runtime/src/                 admission, plans, tables, execution and the interactive runner
  zkc-tools/src/                   artifacts, protocol hosting, checker processes and the zkc command
  zkc-arkworks/, zkc-backends/     concrete cryptographic and numerical adapters
  zkc-test-support/                where the tools, the corpus and a test's
                                   evidence are, for the tests that cross a build
Cargo.toml, Cargo.lock              root Rust workspace
examples/                           complete small public compiler clients
  protocols/                       closed protocols authored in one source
  libraries/, projects/            reusable source libraries and the applications that select from them
tests/
  fixtures/                        shared inputs and expected results for all builds
    air/, blocks/, identity-vectors/  finite relations and checker vectors
    external-transcript/, archived-shapes/    frozen upstream proofs and extracted metadata
  admission/, artifact/, execution/    the tests that cross a build, by subject
  identity/, kernels/, physical/, protocol/
  harness/                         configuration, runner and evidence controls
  support/                         the vocabulary they import and the cases they share
  consumer/                        a separate project built against the installed package
  groth16/                         Circom and snarkjs fixture generation
  external-transcripts/            regeneration of the replies recorded from archived transcripts
bench/                              measurements against matched direct implementations
justfile                            common development commands and prerequisites
flake.nix, flake.lock                pinned development and package environment
nix/                                language packages, checks and integration closures
scripts/                            environment diagnostics and pin maintenance
```

The three builds remain independent. Cross-language tests select completed
outputs through the [configuration contract](configuration.md),
and the [test guide](../../tests/README.md) owns suite discovery and prerequisites.
Just forwards common commands; native build tools and shared drivers are also
directly callable. Measurements live apart from tests because they answer a
different question. Raw run records remain local; maintained comparison pages
state the scope of selected observations.

No `v2`, `new`, `misc`, `Compat` or numbered research namespace
is part of the API. `PIR` names the protocol representation. A physical
plan's production name follows its selected responsibility; the direct reference
`Compiler.Plan` in Lean does not require a same-shaped native IR.

## 2. Naming and dependencies

C++ follows LLVM/MLIR conventions: descriptive CamelCase classes and filenames,
lower-camel functions, namespace `zkc`, generated TableGen files in the build tree,
public headers under `include/zkc`, implementation under `lib`. Conversion libraries
name both endpoints, for example `Conversion/PIRToPlan`; dialect-local rewrites
stay with their dialect. Use C++17 for the tested LLVM 23 baseline unless an
adopted upstream version requires otherwise. Thin tools link reusable libraries.
[LLVM coding standards](https://llvm.org/docs/CodingStandards.html).

Rust uses kebab-case package names, snake_case modules/functions and UpperCamelCase
types. Keep fields private at custody/admission boundaries, use newtypes for
different identities, and use ordinary modules before independent crates. There
is no Rust analysis/search service or per-operation C++ round trip. Later C FFI,
if needed, exchanges complete requests and opaque result ownership rather than
`Operation *` or Rust enum layouts.
[Rust API guidelines](https://rust-lang.github.io/api-guidelines/checklist.html).

Lean uses semantic module and declaration names, a small `import Zkc`, and explicit
imports for source, compiler, realization and protocol consumers. The current
semantic namespaces include `PIR` for shared protocol meanings and `Zkc` for
source, compiler and domain libraries. Numbered and `Compat` APIs have been
removed. Module homes follow mathematical ownership; a namespace spelling is
not a separate implementation layer.
[Formal library design](../../formal/DESIGN.md).

The dependency direction is contracts/IR → analysis and conversion → compiler
facade → tools. Protocol examples use those interfaces, not the reverse. Rust
runtime modules do not import the SDK or launch tools. Formal core imports no
native generated source. Optional proof integrations depend on the common
semantics and external libraries, never become dependencies of `import Zkc`.
The main Lake package resolves Mathlib without ArkLib/VCVio. The ArkLib integration
has its own manifest and brings those external libraries; separate downstream
clients exercise both package boundaries.

## 3. Build ownership

Pin and record a tested LLVM/MLIR distribution or source revision, Rust toolchain,
Lean toolchain and dependency locks. A floating `LLVM >= 23` condition is not a
reproducible support claim. The compiler builds standalone from its CMake
presets; Cargo and Lake are independent builds.
An integration command coordinates completed tool invocations without turning
Cargo into a hidden CMake/prover installer. Test supported build-feature combinations,
install/export libraries, and a standalone runtime consumer.

The [development guide](README.md) owns daily commands and supported
environments. [Configuration](configuration.md) owns paths and
environment variables; [maintenance](maintenance.md) owns pins,
caches and upgrades. `scripts/` holds workspace operations; `tests/run.py`
executes shared test scopes against built outputs.

[Implementation maintenance](extensions.md) maps dialect, pass, backend
and integration changes to their owners and required checks.
