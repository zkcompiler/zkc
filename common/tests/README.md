# Tests

The execution toolkit checks `.zkc` applications through Entry control and
Protocol IR (PIR), built on MLIR. Their numerical work lowers to `zkc.program/0`;
the common Entry, proof and joint Hosts share the native VM. Shared Python
tests exercise that path and its installed tools. The optional Lean package
maintains independent research models and checks.

## Selecting checks

Retained source value replay changes use the compiler's `source-value-replay`
and `total-computation` CTest cases, with affected scoped/control/oracle cases.
These check source event snapshots, literal semantics and typed administrative
carriers, including complete literal producer envelopes and eager recipe
captures under participant restriction. The replay case also checks its exact
work allowance independently of the earlier formation-budget floor.
`protocol/test_language_total_computation.py` provides separate Host execution
evidence for literals, natural statics and nested restricted recipe captures.

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
| Documentation | `just test-docs` | Links, fragments, reachability and fixture digest tables |
| Installed Rust SDK | `nix build .#checks.x86_64-linux.rust-consumer` | Staged SDK and Unicode sources, independent normal-feature Rust consumer; prepared execution outside checkout without compiler or CLI |
| Installed CLI | `nix build .#checks.x86_64-linux.application` | Check source, compile, inspect, prove and verify outside the checkout |
| Formatting and lint | `just lint` | C++, Rust and Nix formatting; Clippy, Ruff, Just and workflow syntax |
| Broad native integration | `just test` | Harness, SDK, compiler, Rust, integration, installation, docs and lint |
| Plonky3 AIR adapter | `just test-plonky3` | Pinned upstream adapter and native differential controls |
| OpenVM relation adapter | [Standalone workspace commands](../../compiler/adapters/openvm/README.md#run-the-checks) | Pinned branch-subsystem export, upstream comparisons and both native Bundle evaluators |
| Deployed EVM target | [Pinned runner and real native-proof commands](evm/README.md) | Optional isolated revm workspace; exact deployed bytecode, canonical ABI, outcome and full primitive-trace controls |
| Independent Lean research | `just test-lean` | Optional formal build, controls and consumers |

`just setup` prepares locked Python and Cargo dependencies. `just build` builds
only the compiler and default-feature CLI. `just build-test-drivers` separately
builds integration drivers with test providers; `just test-integration` builds both. No default build, test or installation invokes a Lean checker. `just test-sanitize` selects the compiler sanitizer profile.

The Rust scope checks the all-features workspace, then the benchmark worker's
normal build and the runtime's disabled execution collector. Provider timing
controls reject instrumented builds; both configurations need their own checks.

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

### Fresh compiler pairing

Seven ignored Cargo tests pair the SDK with a freshly built compiler. They
compile real sources through `language-package`, then admit and execute the
actual packages: published common-input inventories and the contexts the SDK
produces for them, collection extents, Entry component families, typed Host
children, a Function's proof child completing on a later attempt and the
generated Host of a full 1,024-role roster under a raised interface selection.
One more pairs the CLI with the compiler: it compiles, inspects, prepares and
runs that Host under `--interface-limits`.
Hand-built SDK fixtures cannot satisfy them. Build the compiler first, then run them explicitly:

```sh
ZKC_COMPILER_BIN=build/compiler cargo test --locked -p zkc --features cpu,files --test common_inventory_compiler --test entry_components -- --ignored
ZKC_COMPILER_BIN=build/compiler cargo test --locked -p zkc-cli -- --ignored
```

### Compiler-produced interface fixtures

The [language-interface](../../compiler/test/fixtures/language-interface/README.md),
[Entry component](../../compiler/test/fixtures/entry-components/README.md),
[common-input](../../compiler/test/fixtures/common-inputs/README.md) and
[FRI interface](../../crates/zkc/src/entry/interface/tests/fixtures/README.md)
fixtures are compiler output, and each JSON interface records the producing
build's toolchain identity. Consumers testing schema structure take that
identity as a fixture parameter, so a compiler edit that changes only the
identity needs no regeneration. After a change to the interface schema, the
native printing or a fixture's construction, regenerate all of them from one
named build:

```sh
python3 scripts/regenerate-interface-fixtures.py build/compiler
```

The [script](../../scripts/regenerate-interface-fixtures.py) runs the compiler
producers and `zkc-compile`, then recomputes the `Current fixture SHA-256` table
of each fixture guide. `just test-docs` compares every such table with the
retained bytes, so an edited fixture or a stale table fails.

### CPU worker confinement

Portable Cargo checks cover numerical agreement under different worker counts.
The explicit Linux gates also require `strace` and ptrace permission:

```sh
cargo test --locked -p zkc-kernels --test cpu_thread_creation provider_workloads_create_only_owned_workers -- --ignored
cargo test --locked -p zkc-cpu --test cpu_thread_creation installed_polynomial_operations_create_only_owned_workers -- --ignored
cargo test --locked -p zkc-cpu --test cpu_thread_creation installed_resident_scaling_creates_only_owned_workers -- --ignored
cargo test --locked -p zkc-benchmarks output_checks_create_no_additional_workers -- --ignored
```

They count successful task creation over each child process's full lifetime,
including workers that exit before the numerical call returns. Known caller and
test threads are included separately from the owner budget. These gates check
the selected installed/provider workloads; the owner does not limit foreign code
or total process CPU use.

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

Use `nix develop .#lean`, then `just fetch-lean` and `just test-lean` to build and check the maintained packages. Select dependencies with `just fetch-lean --package verification`, `just fetch-lean --package arklib` or `just fetch-lean --package clean`, then use `just test-lean-verification`, `just test-lean-integration` or `just test-lean-clean` to build and check that package. The Clean check requires
[its native control](fixtures/clean/air-control.json) and the
[Bundle fixtures](../../compiler/adapters/clean/README.md) to be the producers'
current outputs; the [native comparison](protocol/test_clean_air_conformance.py)
of that control runs in `just test-integration` without Lean.
`just test-lean-fresh` rebuilds research packages without previous
project/dependency objects. A dependency-free package is built and its test driver run
without Program; Program's sources and dependencies are prepared, not built, only for
its consumer-workspace audit. These can be expensive. `just test-lean` also builds the
Core and Formal packages, which are outside Program's closure, runs their kernel checks
and Formal's test driver, and checks their sources.

The core lane checks maintained source ownership, declaration/axiom records and
external consumers. The optional integration lane includes the retained ArkLib and
Clean mathematical adapters. These checks no longer generate protocol subjects or
assemble native security receipts.

`just test-lean-native` prepares the native compiler; its driver incrementally builds
only the structured reader it uses. It compares actual frontend exports and selected
service fixtures against independent SSA and Lean execution, retaining returned rows,
reached stops, ordered replies and failures. Capacity is sufficient for both
interpreters and does not claim identical step accounting. See
[formal support](../../lean/docs/support.md).

The old `--stage`, `--subject` and `--fresh-bodies` generator switches are removed.
Use focused Lake modules while repairing proofs, then run required affected package
checks once. Reuse declaration records only with the checker's exact current input
receipt. A timeout or signal death is not a semantic refusal.
