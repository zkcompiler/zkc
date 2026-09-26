# Development guide

Nix selects the repository's toolchains and builds sandboxed packages. CMake
and Ninja own C++, Cargo owns Rust, Lake owns Lean, and uv owns Python tools.
The [justfile](../../justfile) coordinates their ordinary commands. These native
builds remain usable outside Nix when the required tools are supplied explicitly.

The supported Nix system is **x86_64-linux**. NixOS is not required. Other Linux
architectures, macOS, Windows, cross compilation and deployment images are not
validated targets. The host kernel, Nix installation and editor remain outside
the flake. Nix fixes build inputs; it does not establish compiler correctness or
bit-for-bit determinism of every generated report.

The full suite includes an 8,190-draw resource-boundary case whose Lean checker
peaked at approximately 19 GiB resident memory in both native and Nix builds.
Use a machine with at least 24 GiB RAM; 32 GiB or more is recommended when builds
run concurrently. Focused compiler and ordinary development checks need much
less memory. The full test retains its original workload and timeout.

## Set up the development checkout

Install a current stable upstream Nix using its
[multi-user installation guide](https://nix.dev/manual/nix/stable/installation/installing-binary.html).
Enable `nix-command` and `flakes` in the local Nix configuration, retain Linux
sandboxing and set `sandbox-fallback = false`. Existing installations need not
match the workflow's installer version; the required commands and isolation
checks determine compatibility.

From a checkout:

```sh
nix develop
just doctor
just setup
just build
just test-harness   # configuration and runner checks without compiled project tools
just test           # full main suite; observe the resource requirement above
```

Entering the shell resolves its locked tool packages. It does not run uv, Cargo
or Lake downloads in a shell hook. `just setup` explicitly installs locked Python
tools, fetches Cargo sources and requests pinned Lean dependency objects for
interactive development. `just build` then builds the owned sources. Network
access is expected for that first development setup.

For sandboxed builds, without a project virtual environment or host toolchains:

```sh
nix build .#compiler .#tools .#formal
nix flake check -L --keep-going
```

Fixed-output fetchers obtain hash-checked source inputs. The ordinary build and
check phases use those inputs without network access. Cargo uses its vendored
lock closure, Python tools are constructed from `uv.lock`, and Lake compiles its
pinned dependencies from source with `--no-cache`. The first Lean source build
is substantial; completed Nix outputs can be reused by subsequent builds.

Nix flakes in Git repositories see tracked files. Add a new build input to Git
before expecting ordinary flake evaluation to include it. During an uncommitted
packaging experiment, `path:.` explicitly includes the working tree; it should
not become a workaround for a missing tracked input in CI.

## Configuration and maintenance

| Task | Reference |
|---|---|
| Select built tools, configure concurrency or locate reports | [Configuration](configuration.md) |
| Upgrade dependencies, maintain caches or operate CI | [Maintenance](maintenance.md) |
| Find implementation homes and naming conventions | [Repository layout](layout.md) |
| Add operations, passes, backends or integrations | [Implementation extensions](extensions.md) |
| Write, organize or validate documentation | [Documentation maintenance](documentation.md) |

These references own their detailed policies. The justfile forwards ordinary
commands to the native builds and shared drivers.

`just doctor` reports the actual tool versions, selected output/report paths and
differences from the configured CMake toolchain. Use
`python3 scripts/doctor.py --profile dev` to inspect another build profile.
`python3 scripts/doctor.py --json` emits the same information for a run record.
Outside Nix, the configure driver requires compatible `MLIR_DIR`, `CC` and `CXX`;
supply `LLVM_CONFIG` when needed. Recreate a CMake build directory when changing its
compiler or ABI. Native compiler commands remain in the
[compiler guide](../../compiler/README.md#build).

Configuration also selects Ninja from `PATH` explicitly, so an existing CMake
cache cannot silently retain an older Ninja installation. `just doctor` reports
any difference between the cached and selected paths.

## Build profiles and editor tools

The checked-in [CMake presets](../../compiler/CMakePresets.json) define independent
`release`, `dev`, `sanitize` and `shared` build directories. `release` remains the default.

```sh
just test-compiler dev
just test-sanitize
nix build .#compiler-sanitize
```

The development profile uses optimization, debug information and project
assertions. The sanitizer profile enables ASan and UBSan for project C++ code
and runs the native C++ tests. The pinned LLVM/MLIR libraries are their release
builds, so this does not instrument upstream internals. The sanitizer preset and
Nix check disable manual allocator poisoning (`allow_user_poisoning=0`): LLVM
inline allocators otherwise poison memory that uninstrumented MLIR code cannot
unpoison consistently. [StableHLO uses the same mixed-build setting](https://github.com/openxla/stablehlo/blob/main/.github/workflows/buildAndTestCMake.yml).
Ordinary ASan allocation/access checks, UBSan and leak detection remain enabled;
LLVM arena suballocation poisoning is outside this profile's coverage. Checking
that boundary requires an instrumented LLVM/MLIR build. LeakSanitizer also needs
an execution environment that permits its thread inspection; a ptrace-restricted
supervisor cannot validate it. The complete ordinary compiler suite still runs
in the release profile.

The `shared` profile builds the same component graph as shared libraries. On
Linux, ordinary component links reject undefined symbols; sanitizer builds leave
their runtime hooks for the final executable. For changes to library ownership,
linkage or installed headers, run `just test-install` and
`just test-install "" shared`; this checks each installed component and the
standalone service extension in both linkage modes without running the full suite.

The profile argument selects the CMake preset; the preset owns its output
path. For integration tests using a development compiler, first build it and
then select its output explicitly:

```sh
just build-compiler dev
ZKC_COMPILER_BIN=build/compiler-dev python3 tests/run.py cross
```

The Rust tools and Lean checkers must already be built for that cross-language
command. Direct `tests/run.py` calls never build dependencies. `just test-cross`
adds the normal release-build prerequisites. GNU time is supplied for the
artifact driver's memory measurements.

Use `just test-harness` for configuration, command wiring and reporting
regressions without compiling project components. `just test-bench` explicitly
tests the separate benchmark Cargo workspaces. The [test guide](../../tests/README.md)
describes all execution owners and optional scopes. Main-suite commands retain
their resource-boundary cases; no implicit `slow` filter changes their coverage.

Output arguments remain available for individual operations:
`just test-artifact /tmp/zkc-artifact`, `just bench /tmp/zkc-bench`, and
`just test-install /tmp/zkc-sdk dev`. The last command installs and checks the
`dev` compiler; omitting its profile selects `release`. The SDK prefix must be
absent. With no output argument, the check allocates a new prefix and consumer
build beneath its report root and requires that installation's exported CMake
package before configuring the consumer; old installed headers cannot satisfy it.
The check also invokes help and version reporting from the installed compiler
tools by absolute path, so development binaries on `PATH` cannot mask a broken install.
Installed compiler tools retain runtime search paths to their selected LLVM/MLIR
libraries. Keep that dependency installation available; the SDK does not bundle
LLVM. Its shared component libraries are found relative to the tool prefix.

The shell supplies clangd, clang-format and rust-analyzer. Point clangd at
`build/compiler/compile_commands.json`, or at the selected development build's
database. Editor settings stay local. `cargo fmt` remains Rust's formatter;
`nix fmt` formats the Nix files and `nix fmt -- --check` checks them. Ruff checks
Python defects without imposing a new repository-wide formatting style.
Start the editor from the shell when it needs to inherit these tool paths.
The shell supplies time-zone data for Lean's language server. It preserves the
host zone or an explicit `TZ`; a minimal container without either uses UTC.
Use `clang-format -i PATH...` for selected C++ files with the repository's LLVM
style configuration; broad formatting changes should remain separate.

## Packages and checks

| Command/output | Meaning |
|---|---|
| `nix build .#compiler` | Installed compiler tools and CMake SDK; all compiler CTest cases run |
| `nix build .#tools` | Native Rust host/runtime tools; Rust and cross-language checks are separate |
| `nix build .#formal` | Compiled independent Lean checker executables |
| `nix build '.#formal^library'` | Lean sources, pinned dependencies and compiled library objects |
| `nix flake check` | Compiler, installed CMake consumer, native Lean smoke, Rust tests/Clippy, cross-language/artifact/formal controls, docs and lint |
| `nix build .#arklib` | Optional ArkLib source build and independent main/ArkLib consumers |
| `nix build .#llzk` | Separate LLVM 20 adapter build and adapter tests |
| `nix build .#groth16` | Regenerated deterministic test fixtures from pinned tools and npm inputs |
| `nix build .#groth16-checks` | Fixture reproduction plus maintained Rust and end-to-end interoperability checks |

Compiler and Rust `testSupport` outputs retain example/test executables for the
test harness. Ordinary consumers use their main outputs. Lean's `library`
output is separate from the runtime checker executables.

LLZK and Circom use separate revisions already selected by the integration
manifests. The Circom pin includes an LLZK backend even when generating ordinary
Groth16 fixtures. Its binding expects a combined LLVM/MLIR prefix; Nix supplies
that view over the separately packaged outputs. The LLZK build enables exceptions
for its own local throw/catch implementation. LLVM 20 remains isolated from the
main compiler's LLVM 23 process.

Groth16's deterministic setup and fixed randomizers are public test material.
The integration's existing scope and security limitations remain in its
[README](../../tests/groth16/README.md). A packaged reproduction does not expand
those claims.
