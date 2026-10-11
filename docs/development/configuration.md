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
| Source selection | `nix/sources.nix`, `nix/source.nix` | Declare package/check inputs and exclude generated/private data |
| Native builds | `compiler/CMakePresets.json`, Cargo/Lake manifests | Build graph, profiles and dependency versions |
| Workspace operations | `scripts/develop.py`, `scripts/workspace.py` | Explicit setup, profile resolution and mutable checkout paths |
| Test execution | `common/tests/run.py` and the existing test drivers | Ordered integrations and report routing, shared by local commands and Nix |
| Everyday interface | `justfile` | Short commands and simple prerequisites |

The `justfile` does not load `.env`, discover installations, update locks or
re-enter Nix. Shell entry installs/resolves tools but does not sync Python,
fetch Lake dependencies, or build the project. Use `just setup` explicitly;
the same operation is available as
`nix develop --command python3 scripts/develop.py setup`.

Compiled package source sets exclude Python test orchestration and unrelated integration fixtures. Test derivations add their own inputs. `checks.sources` verifies representative inclusions and exclusions. Documentation, style and harness discovery inspect the full maintained repository; optional Lean integrations have separate source sets. Update the owning list in `nix/sources.nix` when a package or check starts reading a new path.

## Toolchain and concurrency

Toolchain settings (`CC`, `CXX`, `MLIR_DIR`, `LLVM_CONFIG`, `UV_PYTHON`,
`UV_PYTHON_DOWNLOADS` and `TZDIR`) are supplied by Nix. The optional formal
environment separately owns Lean tools and its `LEAN_CC` default. Do not redefine these in just or a local `.env`.
Rust uses the exact release in `rust-toolchain.toml` in rustup, Nix and CI; doctor refuses a different release. An intentional toolchain change belongs in the owning manifest or Nix input.
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
| `LEAN_NUM_THREADS` | Optional formal environment worker threads |
| `PYTEST_XDIST_AUTO_NUM_WORKERS` | Cross-language pytest workers |

The development default is four for each. Without that environment, native
tools retain their own defaults; the integration driver uses one pytest
worker unless explicitly configured. Builds and tests may themselves start
threaded subprocesses, so increase these values deliberately. Nix checks use
their allocated `NIX_BUILD_CORES`, with one worker when that budget is zero or
unspecified. Check derivations receive their own declared inputs/environment;
they do not inherit `devShell` settings. Standard GitHub runners give one Nix derivation four cores at a time. Compiler/package and Rust checks run in separate jobs. Full packaged integration runs resource-boundary cases with one worker after the remaining cases, preserving their coverage without competing large allocations.

## Incremental builds and input boundaries

The main Nix C++ toolchain uses the matching LLVM LLD linker through its Nix wrapper, retaining runtime-library paths and the existing libstdc++ ABI. This applies to local builds, packages and installed-consumer checks without raising the CMake minimum version. Outside Nix, the selected compiler retains its own linker policy.

The development shell enables ccache through CMake's C/C++ compiler launchers. Its normal user cache can be shared between worktrees, while each worktree keeps its own CMake outputs. `CCACHE_BASEDIR` defaults to the shell-entry directory, and `CCACHE_NAMESPACE` includes the pinned Clang package. ccache still checks compiler inputs and flags; it never replaces CMake's dependency graph. Inspect reuse with `ccache --show-stats`. To disable it, set `CMAKE_C_COMPILER_LAUNCHER=` and `CMAKE_CXX_COMPILER_LAUNCHER=` before configuring. Nix package builds do not read this mutable cache.

Configure writes a root compilation-database symlink for the selected CMake profile, replacing only a previous link into this checkout's `build/` directory. A regular file or external symlink remains user-owned. Switching a profile updates clangd's selected commands without changing integration-test tool selection.

Nix uses Crane to cache compiled external Rust dependencies separately from workspace sources. Release product, release test-driver and development-profile all-feature test artifacts have separate caches, so tests cannot add provider features to the distributed CLI. Cargo manifests, the lockfile and toolchain remain cache inputs; no manually maintained vendor hash is needed. Source changes rebuild the relevant workspace crates. Libraries and examples are integration inputs, not Rust-only test inputs.

`python3 .github/scripts/check-nix-inputs.py` verifies derivation invalidation in a temporary tracked-source snapshot: documentation changes preserve compiled outputs, library changes invalidate execution checks, C++ changes invalidate the compiler, Rust changes preserve external dependency artifacts, and Cargo manifest changes invalidate those artifacts. It evaluates derivations without compiling them. Keep these controls aligned with `nix/sources.nix` when changing ownership.

## Built tool selection

Two public directory settings select already-built executables:

| Variable | Checkout default | Contents |
|---|---|---|
| `ZKC_COMPILER_BIN` | `build/compiler` | Compiler tools and their test/example subdirectories |
| `ZKC_NATIVE_BIN` | `target/release` | Rust CLI and integration driver binaries |

Explicit directories take precedence over defaults and must be nonempty.
Relative `ZKC_*` paths are resolved from the checkout root by the test drivers,
including when invoked from another directory. A missing or nonexecutable tool
fails; it never falls back to another build or `PATH`. These variables select
inputs to tests, not where a native build writes its outputs. Cargo's native
`CARGO_TARGET_DIR` is honored when `ZKC_NATIVE_BIN` is absent and retains Cargo's
cwd-relative meaning. Prefer absolute Cargo target paths when invoking tools
from different directories. Native runtime examples use the release profile.

These directory inputs select C++/Rust tools for native integration tests.
Formal package audits and independent Lake consumers inspect the selected
source package and its own build outputs; their `--lean`, `--lake` or
explicit checker arguments retain that package boundary.

CTest privately passes exact target files using `ZKC_CTEST_*`, so a test of a
`dev` or `sanitize` build uses that build even if the shell names another
compiler directory. Those settings are supplied by CMake and are not public
integration overrides. Standalone compiler scripts use the public compiler
directory when no exact CTest target was supplied. Python import paths needed
by test scripts are confined to test processes and CTest; the shell does not
export a global `PYTHONPATH`.

## Reports and integration inputs

`ZKC_REPORTS_DIR` selects the report root, defaulting to `build/reports`.
Python, Rust, CTest, optional formal controls and integration drivers place their reports
under this root. Relative values are checkout-relative. `common/tests/run.py` creates
a new `runs/<scope>-…` directory, prints its path and passes it to children via
the same `ZKC_REPORTS_DIR`; there is no second report-root variable. Direct
pytest and compiler Python cases also allocate exclusive directories. Rust allocates
an exclusive root per process and keeps repeated or nested case records. Setup,
Lean reproduction and installed-SDK checks likewise allocate a fresh operation
root. These paths preserve evidence; native build directories and dependency
stores are still shared. Concurrent builds of one profile or Lake package are
not isolated by report allocation. The
[test guide](../../common/tests/README.md) owns the report and cancellation contract.

A test's explicit `--output` overrides its default where supported. Drivers that capture published artifacts require an absent output directory, preserving previous evidence on
reruns. `just test` does not delete reports; `just clean-reports` explicitly
removes them and must not run concurrently with tests. Cleanup refuses a
symlink destination, home/ancestor directories, the entire build directory and
checkout source directories. Generated report locations inside the checkout
must be below `build/`. Use a dedicated external directory for reports outside
the checkout.
