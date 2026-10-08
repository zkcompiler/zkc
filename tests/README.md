# Tests

The execution toolkit has one path: `.zkc` source lowers through mathematical
MLIR to `zkc.program/1`, which the common Runner and Host execute. Root Python
tests exercise that path and its installed tools. The optional Lean package
maintains independent research models and checks.

## Selecting checks

| Change | Command | Scope |
|---|---|---|
| Harness, configuration or command wiring | `just test-harness` | Python controls without compiled project tools |
| C++ compiler, dialects or passes | `just test-compiler` | CMake/CTest; accepts `dev`, `sanitize` or `shared` |
| Runner, Host or backends | `just test-rust` | Root Cargo workspace, all features |
| Source-to-execution integration | `just test-integration` | Root pytest suite against built compiler and Rust tools |
| Installed SDK | `just test-install` | Fresh compiler installation and independent consumer |
| Installed domain contribution | `just test-install-domain` | Separate base/domain installations and consumers |
| Documentation | `just test-docs` | Links, fragments and reachability |
| Rust/Python style | `just lint` | Rust formatting, Clippy and Python lint |
| Broad native integration | `just test` | Compiler, Rust, root integration, installation, docs, lint and demo |
| Independent Lean research | `just test-lean` | Optional formal build, controls and consumers |

`just setup` prepares locked Python and Cargo dependencies. `just build` builds
only C++ and Rust. No default build, test, installation or demo invokes a Lean
checker. `just test-sanitize` selects the compiler sanitizer profile.

The driver runs tests against existing outputs without building dependencies:

```sh
python3 tests/run.py harness
python3 tests/run.py integration
python3 tests/run.py compiler --profile dev
python3 tests/run.py rust
python3 tests/run.py demo
uv run --no-sync --locked pytest tests/kernels
uv run --no-sync --locked pytest tests --collect-only
```

`tests/run.py project` is the Nix integration scope: root pytest plus the source
Entry demo. Nix separately owns compiler, Rust, installed-consumer and style
checks. The retired `cross`, `artifact`, `bench`, `evidence` and `groth16` scopes
are not aliases.

## Coverage and ownership

- `protocol/` covers compiler-generated mathematical programs, native proofs,
  Entry Host commands, generated bindings, public `.zkc` projects, CLI discovery
  and executable documentation. Native generators run into fresh directories;
  a previous CTest run cannot satisfy their inputs.
  Contract conformance compares C++ Contracts, Rust admission and native backend
  signatures, including independently authored witnesses and deliberate drift.
- `kernels/` compares extension-field arithmetic, sparse matrices, vector
  scatter and coset evaluation/interpolation/folding against independent
  integer calculations through `.zkc` Entries, including disabled
  simplification, storage release and malformed wire inputs. Cargo owns the
  broader backend/kernel unit suites.
- `harness/` checks tool selection, process cancellation, refusal exit statuses,
  concurrent report allocation, installation isolation and command wiring.
- `support/` provides tool resolution, journals, the Entry helper and direct
  integer reference arithmetic.
  `support/formal/` contains fixture construction used only by the optional Lean
  checks; the formal driver adds it to those subprocesses' Python path.
- `consumer/` is the separately configured installed C++ SDK consumer.
- `fixtures/` contains independently retained reference vectors; its README
  identifies their owners.

Source-bound artifacts, `.pir` Frontend tests, table/plan execution,
compiler-to-old-Lean correspondence and Groth16/snarkjs fixture regeneration
have been retired. They are not alternative execution scopes. Native vectors,
matrices and backend numerical kernels remain part of program execution.

## Tools and reports

`ZKC_COMPILER_BIN` selects the directory containing `zkc-compile` and `zkc-opt`;
`ZKC_NATIVE_BIN` selects the Rust tools and `examples/` executables. Defaults are
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

Use `nix develop .#formal`, then `just fetch-lean`, `just build-lean` and
`just test-lean` for the independent package. `just test-lean-integration` checks
the optional ArkLib integration; `just test-lean-fresh` rebuilds research packages
without previous project/dependency objects. These can be expensive.

Sandboxed optional packages are `.#formal`, `.#formal-checks`, `.#arklib` and
`.#lean-toolchain-checks`. They are outside `nix flake check`'s native check graph.
The retained research sources and their vectors do not establish correspondence
or security for the current compiler merely because their checks pass.
