# Development configuration

Nix owns tool acquisition, the development environment, immutable packages and
sandboxed checks. Native manifests own language dependencies; CMake presets
and Cargo/Lake configuration own build profiles. `just` supplies everyday
command names and forwards arguments. It neither chooses tool versions nor
exports an alternative environment.

| Owner | Files | Responsibility |
|---|---|---|
| Nix | `flake.nix`, `flake.lock`, `nix/default.nix` | Pinned inputs and package/check composition |
| Environment | `nix/environment.nix`, `nix/shell.nix` | Tool paths, development defaults and explicit check environments |
| Source selection | `nix/source.nix` | Exclude generated/private data; isolate component inputs |
| Native builds | `compiler/CMakePresets.json`, Cargo/Lake manifests | Build graph, profiles and dependency versions |
| Workspace operations | `scripts/develop.py`, `scripts/workspace.py` | Explicit setup, profile resolution and mutable checkout paths |
| Test execution | `tests/run.py` and the existing test drivers | Ordered integrations and report routing, shared by local commands and Nix |
| Everyday interface | `justfile` | Short commands and simple prerequisites |

The `justfile` does not load `.env`, discover installations, update locks or
re-enter Nix. Shell entry installs/resolves tools but does not sync Python,
fetch Lake dependencies, or build the project. Use `just setup` explicitly;
the same operation is available as
`nix develop --command python3 scripts/develop.py setup`.

## Toolchain and concurrency

Toolchain settings (`CC`, `CXX`, `MLIR_DIR`, `LLVM_CONFIG`, `UV_PYTHON`,
`UV_PYTHON_DOWNLOADS` and `TZDIR`) are supplied by Nix. Lean's package wrapper
owns its `LEAN_CC` default. Do not redefine these in just or a local `.env`.
An intentional toolchain change belongs in the owning manifest or Nix input.
Native builds outside Nix require an explicitly supplied compatible toolchain.
The configure driver requires `CC` and `CXX` to name executable files (including
executable wrappers), and `MLIR_DIR` to contain `MLIRConfig.cmake`. Put compiler
flags in `CFLAGS`/`CXXFLAGS`, not in executable names. It passes these selections
explicitly to CMake. Doctor compares them with the configured cache and reads
MLIR's version from the selected CMake package; `llvm-config` is only an auxiliary
tool. LLVM/MLIR major 23 is required; a difference from the tested version is
reported separately. Raw CMake invocations follow the compiler's CMake manifests.

Tests and lint use `uv run --no-sync --locked`; dependency preparation belongs to
the explicit setup command, which runs `uv sync --locked`.

Development concurrency defaults are set only when entering the Nix shell,
using the native variables below. Each can be overridden for an individual
command. `just` does not recalculate or override them.

| Variable | Controls |
|---|---|
| `CMAKE_BUILD_PARALLEL_LEVEL` | CMake/Ninja build concurrency |
| `CTEST_PARALLEL_LEVEL` | Compiler test concurrency |
| `CARGO_BUILD_JOBS` | Cargo build concurrency |
| `RUST_TEST_THREADS` | Rust test concurrency |
| `LEAN_NUM_THREADS` | Lean worker threads |
| `PYTEST_XDIST_AUTO_NUM_WORKERS` | Cross-language pytest workers |

The development default is four for each. Without that environment, native
tools retain their own defaults; the cross-language driver uses one pytest
worker unless explicitly configured. Builds and tests may themselves start
threaded subprocesses, so increase these values deliberately. Nix checks use
their allocated `NIX_BUILD_CORES`, with one worker when that budget is zero or
unspecified. Check derivations receive their own declared inputs/environment;
they do not inherit `devShell` settings.

## Built tool selection

Only three public directory settings select already-built executables:

| Variable | Checkout default | Contents |
|---|---|---|
| `ZKC_COMPILER_BIN` | `build/compiler` | Compiler tools and their test/example subdirectories |
| `ZKC_NATIVE_BIN` | `target/release` | Rust tools and `examples/` |
| `ZKC_LEAN_BIN` | `formal/.lake/build/bin` | Named Lean checker executables |

Explicit directories take precedence over defaults and must be nonempty.
Relative `ZKC_*` paths are resolved from the checkout root in Python and Rust,
including when invoked from another directory. A missing or nonexecutable tool
fails; it never falls back to another build or `PATH`. These variables select
inputs to tests, not where a native build writes its outputs. Cargo's native
`CARGO_TARGET_DIR` is honored when `ZKC_NATIVE_BIN` is absent and retains Cargo's
cwd-relative meaning. Prefer absolute Cargo target paths when invoking tools
from different directories. Native runtime examples use the release profile.

These directory inputs select tools for cross-language and artifact tests.
Formal package audits and independent Lake consumers inspect the selected
source package and its own build outputs; their `--formal`, `--lake` or
explicit checker arguments retain that package boundary.

CTest privately passes exact target files using `ZKC_CTEST_*`, so a test of a
`dev` or `sanitize` build uses that build even if the shell names another
compiler directory. Those settings are supplied by CMake and are not public
cross-language overrides. Standalone compiler scripts use the public compiler
directory when no exact CTest target was supplied. Python import paths needed
by test scripts are confined to test processes and CTest; the shell does not
export a global `PYTHONPATH`.

## Reports and integration inputs

`ZKC_REPORTS_DIR` selects the report root, defaulting to `build/reports`.
Python, Rust, CTest, formal controls and artifact drivers place their reports
under this root. Relative values are checkout-relative. `tests/run.py` creates
a new `runs/<scope>-…` directory, prints its path and passes it to children via
the same `ZKC_REPORTS_DIR`; there is no second report-root variable. Direct
pytest and compiler Python cases also allocate exclusive directories. Rust allocates
an exclusive root per process and keeps repeated or nested case records. Setup,
Lean reproduction and installed-SDK checks likewise allocate a fresh operation
root. These paths preserve evidence; native build directories and dependency
stores are still shared. Concurrent builds of one profile or Lake package are
not isolated by report allocation. The
[test guide](../../tests/README.md) owns the report and cancellation contract.

A test's explicit `--output` overrides its default where supported. Artifact
drivers require an absent output directory, preserving previous evidence on
reruns. `just test` does not delete reports; `just clean-reports` explicitly
removes them and must not run concurrently with tests. Cleanup refuses a
symlink destination, home/ancestor directories, the entire build directory and
checkout source directories. Generated report locations inside the checkout
must be below `build/`. Use a dedicated external directory for reports outside
the checkout. `ZKC_GROTH16_FIXTURE` remains a separate, scoped input for
reproduced interoperability fixtures.

## Replacing removed settings

Removed settings fail with migration guidance instead of being ignored:

| Removed setting | Replacement |
|---|---|
| `ZKC_JOBS` | The native concurrency settings above |
| `ZKC_BUILD_PRESET` | A command argument, e.g. `just test-compiler dev` |
| `ZKC_COMPILER_BUILD` | CMake presets for builds; `ZKC_COMPILER_BIN` for tests |
| `ZKC_COMPILER`, `ZKC_OPTIMIZER` and old compiler example/test file overrides | `ZKC_COMPILER_BIN` |
| `ZKC_LEAN`, `ZKC_PHYSICAL_CHECKER` | `ZKC_LEAN_BIN` |
| `ZKC_TEST_RECORDS=/path/tests` | `ZKC_REPORTS_DIR=/path` |

Keep credentials and machine-wide Nix daemon settings outside the source
flake. GitHub runner labels remain repository variables, documented in the
[maintenance guide](maintenance.md).
Neither just nor shell entry modifies host configuration.
