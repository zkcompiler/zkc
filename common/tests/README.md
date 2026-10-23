# Tests

The execution toolkit checks `.zkc` applications through Entry control and
Protocol IR (PIR), built on MLIR. Their numerical work lowers to `zkc.program/0`;
the common Entry, proof and joint Hosts share the native VM. Shared Python
tests exercise that path and its installed tools. The optional Lean package
maintains independent research models and checks.

## Selecting checks

Retained structured protocol changes use the compiler's `structured-source`,
`structured-applications` and `structured-repeats` CTest cases. The repeat case
captures complete original sources and interfaces, checks optional participant
execution and exact refusals, and exercises native preparation, projection,
Math lowering and physical export. Runner integration and the native affine
resource suites provide separate evidence; reference agreement is not a
production correctness theorem.

| Change | Command | Scope |
|---|---|---|
| Harness, configuration or command wiring | `just test-harness` | Python controls without compiled project tools |
| C++ compiler, dialects or passes | `just test-compiler` | CMake/CTest; accepts `dev`, `sanitize` or `shared` |
| Runner, Host or backends | `just test-rust` | Root Cargo workspace, all features |
| Source-to-execution integration | `just test-integration` | Protocol and kernel pytest suites against built compiler and Rust tools |
| Compact family execution | `python3 common/tests/run.py smoke` | Package boundaries, literal README recipes and small valid/invalid protocol controls; `--family NAME` selects one family |
| SDK discovery and dependency isolation | `just test-sdk` | Small static/shared CMake fixtures; no LLVM installation needed |
| Installed SDK | `just test-install` | Fresh compiler installation and independent consumer |
| Installed domain contribution | `just test-install-domain` | Separate base/domain installations and consumers |
| Documentation | `just test-docs` | Links, fragments and reachability |
| Installed Rust SDK | `nix build .#checks.x86_64-linux.rust-consumer` | Staged SDK and Unicode sources, independent normal-feature Rust consumer; prepared execution outside checkout without compiler or CLI |
| Installed CLI | `nix build .#checks.x86_64-linux.application` | Check source, compile, inspect, prove and verify outside the checkout |
| Formatting and lint | `just lint` | C++, Rust and Nix formatting; Clippy, Ruff, Just and workflow syntax |
| Broad native integration | `just test` | Harness, SDK, compiler, Rust, integration, installation, docs and lint |
| Plonky3 AIR adapter | `just test-plonky3` | Pinned upstream adapter and native differential controls |
| OpenVM relation adapter | [Standalone workspace commands](../../compiler/adapters/openvm/README.md#run-the-checks) | Pinned branch-subsystem export, upstream comparisons and both native Bundle evaluators |
| Independent Lean research | `just test-lean` | Optional formal build, controls and consumers |

`just setup` prepares locked Python and Cargo dependencies. `just build` builds
only the compiler and default-feature CLI. `just build-test-drivers` separately
builds integration drivers with test providers; `just test-integration` builds both. No default build, test or installation invokes a Lean checker. `just test-sanitize` selects the compiler sanitizer profile.

The driver uses existing project tools. Cargo tests and SDK checks compile their own test targets and consumers:

```sh
python3 common/tests/run.py harness
python3 common/tests/run.py sdk
python3 common/tests/run.py integration
python3 common/tests/run.py smoke
python3 common/tests/run.py smoke --family sigma
python3 common/tests/run.py compiler --profile dev
python3 common/tests/run.py rust
python3 common/tests/run.py install --profile dev
uv run --no-sync --locked pytest common/tests/kernels
uv run --no-sync --locked pytest common/tests --collect-only
```

The `harness`, `sdk` and `integration` selections are disjoint. `checks.project` in Nix invokes `integration` against packaged tools; separate derivations own the harness, SDK discovery, compiler, Rust, installed consumer and style checks. The integration suite executes the [published walkthrough](../../docs/getting-started.md) directly.

`python3 common/tests/run.py style` checks source formatting and syntax without project builds. `lint` adds C++ formatting and Clippy. Install checks live in `check_sdk.py` and `check_domain.py`; `check_install.py` exercises the packaged application outside the checkout. Domain checks prepare isolated base/domain builds or validate explicitly selected existing builds with `--skip-build`.

## Coverage and ownership

The [native validation map](native.md) connects compiler boundaries to
representative controls and states their evidence limits.

- `protocol/` covers compiler-generated mathematical programs, native proofs,
  Entry Host commands, [generated Rust SDK calls](protocol/test_rust_sdk.py), public `.zkc` projects, CLI discovery
  and executable documentation. Native generators run into fresh directories;
  a previous CTest run cannot satisfy their inputs.
  Contract conformance compares C++ Contracts, Rust admission and native backend
  signatures, including independently authored witnesses and deliberate drift.
  Relation-bundle and machine relation tests send the same carriers to the C++
  and Rust evaluators and require identical reports.
- `kernels/` compares extension-field and binary-field arithmetic, sparse matrices, vector
  scatter, coset evaluation/interpolation/folding and pointwise maps beside the
  Ring provider and formal products against independent integer calculations
  through `.zkc` Entries, including disabled simplification, storage release
  and malformed wire inputs. Cargo owns the broader backend/kernel unit suites.
- `harness/` checks tool selection, process cancellation, refusal exit statuses,
  concurrent report allocation, installation isolation and command wiring.
- `support/` provides tool resolution, journals, the Entry helper and direct
  integer reference arithmetic. The compiler and Lean fixture generators share `variant_codec.py`; independent production readers keep their own implementations.
- `consumer/` also owns the Rust consumer source used by `check_rust_sdk.py`; the
  `rust-consumer` Nix check provides the pinned Cargo toolchain and dependency closure.
  Preparation builds `Twice`, `Echo`, `Core`, `Checked` and `Withhold` packages
  for numerical, joint, proof, execution-failure and withheld-result controls.
  `consumer/` owns SDK discovery fixtures and the separately configured installed C++ consumers. Small fixtures cover package selection and refusal cases; real installed consumers cover upstream LLVM/MLIR variables, linkage and public headers.
- `fixtures/` contains independently retained reference vectors; its README
  identifies their owners.

## Tools and reports

`ZKC_COMPILER_BIN` selects the directory containing `zkc-compile` and `zkc-opt`;
`ZKC_NATIVE_BIN` selects the Rust CLI and integration driver binaries. Defaults are
`build/compiler` and `target/release`. With no native override, Cargo's
`CARGO_TARGET_DIR` selects its `release` directory. Missing tools fail explicitly;
the harness does not substitute tools from `PATH`.

`ZKC_REPORTS_DIR` defaults to `build/reports`. Each driver invocation allocates a
new directory with `run.json`, and each pytest case receives its own directory.
Journals retain command arguments, exit statuses and output even after failure
or cancellation. `just clean-reports` explicitly removes generated reports;
ordinary commands never clear earlier evidence.

Direct driver calls never synchronize dependencies. `just setup` performs that
step explicitly. `PYTEST_XDIST_AUTO_NUM_WORKERS` controls pytest workers and
must be a positive integer. The driver defaults to one worker outside the Nix
shell. Tests retain their individual timeouts and do not implicitly filter slow
cases.

## Optional formal checks

Use `nix develop .#lean`, then `just fetch-lean` and `just test-lean` to build and check the independent package. Prepare optional dependencies with `just fetch-lean arklib` or `just fetch-lean clean`, then use `just test-lean-integration` or `just test-lean-clean` to build and check that package. The Clean check requires
[its native control](fixtures/clean/air-control.json) and the
[Bundle fixtures](../../compiler/adapters/clean/README.md) to be the producers'
current outputs; the [native comparison](protocol/test_clean_air_conformance.py)
of that control runs in `just test-integration` without Lean.
`just test-lean-fresh` rebuilds research packages without previous
project/dependency objects. These can be expensive.

`just test-lean-native` prepares the native compiler, the runtime CLI, the main Lean package and the ArkLib integration, then
runs independent scalar and structured SSA/Lean comparisons, including primitive
bindings and unchanged table helpers, the source/property
request matrix, and authored-target controls. The [structured bridge](../../lean/bridges/structured/README.md)
also has a standalone command and optional production Runner comparisons.
The separate [participant probe](../../lean/bridges/structured/participant.md)
compares actual Schnorr endpoints, native G1 codecs, pending actions and provider
state; build its test driver explicitly and run the documented standalone command.
It requires the structured open replay executable and is not a default native check.
`lean-native` also runs the [transcript-construction bridge](../../lean/bridges/construction/README.md),
which checks the validators of the compiled Schnorr, Sumcheck, composed Sumcheck,
Schnorr AND and Chaum–Pedersen proof Entries with the Lean rules, and the
[executable bridge](../../lean/bridges/executable/README.md), which checks the validator
program the runtime admits with the Lean lowering rule and compares the runtime CLI
selected by `ZKC_NATIVE_BIN` with the Lean executable meaning.
To use an existing build, run
`python3 common/tests/run.py lean-native --compiler-build=build/compiler`.
This scope exercises wrong-program, wrong-relation and unproved-certificate
refusals as well as successful claims. Reports are retained under
`build/reports/lean/native` (or the selected report root).

Sandboxed optional packages are `.#lean`, `.#lean-checks`, `.#arklib` and
`.#lean-toolchain-checks`. They are outside `nix flake check`'s native check graph.
The retained research sources and their vectors do not establish correspondence
or security for the current compiler merely because their checks pass.

## Offline arithmetic model validation

The optional [arithmetic command](check_arithmetic.py) checks independent models
of unsigned-word centering and exact centered CRT reconstruction. It uses Z3
and LLVM's SMT dialect/exporter with versions selected by the
[owning manifest](fixtures/arithmetic/pins.json). Supply those tools explicitly:

```sh
python3 common/tests/check_arithmetic.py \
  --solver /path/to/z3 \
  --mlir-translate /path/to/mlir-translate \
  --output build/reports/arithmetic-models
```

The output directory must be new. The command downloads nothing and does not
participate in ordinary builds or runtime/compiler admission. The manifest
records a reference solver archive; verify its SHA-256 when acquiring that
binary. A locally built tool with the selected version is also accepted as a
trusted host tool. Version reporting alone does not establish its source or
binary provenance. Each report records actual executable hashes and versions,
the checker hash, query files and digests, complete process output, and replayed
counterexamples. LLVM's owning dependency remains the compiler toolchain;
this optional check does not upgrade it or change Nix's solver package.

The command runs fourteen solver queries: two word-model controls and six
integer CRT controls in both authored SMT-LIB and exported MLIR forms. The
valid interval checks equality of the reconstructed integer itself, so reduction
into any protocol modulus follows from that identity. Every
SAT control must replay its premises and arithmetic disagreement in Python
integers. A concrete extra-column control exposes why reconstruction must be
chunked before its integer range exceeds the CRT capacity. A separate tiny
interval is exhaustively checked without a solver. Unknown, timeout, process
failure, unsupported versions, unexpected status and invalid models fail the
command; each solver receives a ten-second and 512-MB limit, with a fifteen-second
process deadline. Harness tests cover these refusal paths without requiring
Z3 or MLIR installations.

These are independently authored formulas, not a translation of the Rust kernel
or a compiler candidate. UNSAT trusts the formula, exporter and solver; no proof
certificate is checked. The [validation rationale](../../docs/rationale/validation.md#solver-checks-and-schedule-authoring)
states how this tool and prospective Transform/PDL scheduling fit the existing
independent candidate readers.
