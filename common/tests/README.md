# Tests

The execution toolkit has one path: `.zkc` source lowers through Protocol IR
(PIR), built on MLIR, to `zkc.program/0`, which the common Runner and Host execute. Shared Python
tests exercise that path and its installed tools. The optional Lean package
maintains independent research models and checks.

## Selecting checks

| Change | Command | Scope |
|---|---|---|
| Harness, configuration or command wiring | `just test-harness` | Python controls without compiled project tools |
| C++ compiler, dialects or passes | `just test-compiler` | CMake/CTest; accepts `dev`, `sanitize` or `shared` |
| Runner, Host or backends | `just test-rust` | Root Cargo workspace, all features |
| Source-to-execution integration | `just test-integration` | Protocol and kernel pytest suites against built compiler and Rust tools |
| SDK discovery and dependency isolation | `just test-sdk` | Small static/shared CMake fixtures; no LLVM installation needed |
| Installed SDK | `just test-install` | Fresh compiler installation and independent consumer |
| Installed domain contribution | `just test-install-domain` | Separate base/domain installations and consumers |
| Documentation | `just test-docs` | Links, fragments and reachability |
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
  Entry Host commands, generated bindings, public `.zkc` projects, CLI discovery
  and executable documentation. Native generators run into fresh directories;
  a previous CTest run cannot satisfy their inputs.
  Contract conformance compares C++ Contracts, Rust admission and native backend
  signatures, including independently authored witnesses and deliberate drift.
  Relation-bundle and machine relation tests send the same carriers to the C++
  and Rust evaluators and require identical reports.
- `kernels/` compares extension-field arithmetic, sparse matrices, vector
  scatter, coset evaluation/interpolation/folding and pointwise maps beside the
  Ring provider and formal products against independent integer calculations
  through `.zkc` Entries, including disabled simplification, storage release
  and malformed wire inputs. Cargo owns the broader backend/kernel unit suites.
- `harness/` checks tool selection, process cancellation, refusal exit statuses,
  concurrent report allocation, installation isolation and command wiring.
- `support/` provides tool resolution, journals, the Entry helper and direct
  integer reference arithmetic. The compiler and Lean fixture generators share `variant_codec.py`; independent production readers keep their own implementations.
- `consumer/` owns SDK discovery fixtures and the separately configured installed C++ consumers. Small fixtures cover package selection and refusal cases; real installed consumers cover upstream LLVM/MLIR variables, linkage and public headers.
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
[its native control](fixtures/clean/air-control.json) to be the producer's
current output; the [native comparison](protocol/test_clean_air_conformance.py)
of that control runs in `just test-integration` without Lean.
`just test-lean-fresh` rebuilds research packages without previous
project/dependency objects. These can be expensive.

Sandboxed optional packages are `.#lean`, `.#lean-checks`, `.#arklib` and
`.#lean-toolchain-checks`. They are outside `nix flake check`'s native check graph.
The retained research sources and their vectors do not establish correspondence
or security for the current compiler merely because their checks pass.
