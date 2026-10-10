# Development guide

CMake/Ninja owns C++, Cargo owns Rust, Lake owns the independent Lean package,
and uv owns Python tools. Nix supplies pinned toolchains and packages; the
[justfile](../../justfile) coordinates checkout commands. Default builds and
execution tests target the C++/Rust path. Formal work is optional and standalone.

The supported Nix system is **x86_64-linux**. NixOS is not required. Other host
platforms and cross compilation are not validated targets. Nix fixes build inputs;
it does not prove compiler correctness or deterministic application reports.

## Set up the development checkout

Install Nix following its
[multi-user guide](https://nix.dev/manual/nix/stable/installation/installing-binary.html),
enable `nix-command` and `flakes`, and retain sandboxing with
`sandbox-fallback = false`. From the repository root:

```sh
nix develop
just doctor
just setup
just build
```

Shell entry resolves tools without implicit dependency downloads or builds. Setup prepares locked development dependencies; the initial setup needs network access. [Getting started](../getting-started.md) walks through compiling, proving and verifying a maintained Schnorr Entry, including the input-authority boundary.

Development operations expose their options through `python3 scripts/develop.py OPERATION --help`; validation scopes use `python3 common/tests/run.py SCOPE --help`. Each command rejects options belonging to another operation before execution.

Outside Nix, provide compatible `CC`, `CXX`, `MLIR_DIR` and, when needed,
`LLVM_CONFIG`, plus utf8proc 2.12.0 with its CMake package (select it through
`utf8proc_DIR` or `CMAKE_PREFIX_PATH`). Installed Language consumers also need
this external NFC dependency; they do not need MLIR. See the
[SDK dependency contract](../../compiler/README.md#installed-package-discovery).
Recreate a CMake build directory when changing compiler or ABI.
`just doctor` reports selected versions, output paths and cache/toolchain differences.
See [configuration](configuration.md) for directory and concurrency settings.

## Select checks

```sh
just test-harness
just test-compiler
just test-rust
just test-integration
just test-docs
```

Use the [test guide](../../common/tests/README.md#selecting-checks) to choose affected checks. `just test` is broad integration validation and includes resource-boundary cases; run it when changes justify that scope. Direct test drivers use existing outputs; Cargo tests and SDK checks build their own test targets and consumers. Domain installation checks explicitly prepare separate base/domain builds unless `--skip-build` selects existing ones. Record commands, revision, environment and actual results rather than treating documentation links as fresh evidence.

## Build profiles and installed consumers

[CMake presets](../../compiler/CMakePresets.json) provide separate `release`,
`dev`, `sanitize` and `shared` build directories. Release is the default.

```sh
just test-compiler dev
just test-sanitize
just test-install
just test-install "" shared
```

The development profile adds debug information and assertions. Sanitizers cover
project C++ code; the pinned LLVM/MLIR release libraries are not instrumented.
The mixed build disables manual allocator poisoning to avoid incompatible LLVM
arena annotations. This does not validate upstream allocator internals.
LeakSanitizer also requires an environment that permits thread inspection.

Install checks use fresh prefixes and independently built CMake consumers.
Every installed SDK component requires the exact LLVM version used to build it.
Support, Contracts, Program, Relation and Language discover and link without MLIR;
IR and its dependent components additionally require MLIR and installed contribution
dependencies. The SDK does not bundle these external dependencies. Static and
shared component changes need both linkage checks. Existing outputs can be selected with `ZKC_COMPILER_BIN` and
`ZKC_NATIVE_BIN` as described in [configuration](configuration.md).

## Packages and optional work

```sh
nix build                         # installed CLI with its companion compiler
nix run . -- --help
nix build .#compiler .#tools       # separate C++ SDK and runtime CLI
nix build .#test-drivers           # integration clients with test providers
nix flake check -L --keep-going
```

Nix build/check phases consume hash-checked dependencies without network access.
Git-backed flake evaluation sees tracked inputs; add new source files before
evaluating their packages. Generated checkout output is excluded.
The owning flake and test manifests define the exact checks.

Lean has separate build, control and reproduction commands in the
[formal guide](../../lean/README.md). Its tools and models do not validate the
native executable merely by being built. Optional ArkLib, generic
[LLZK](../../compiler/adapters/llzk/README.md) and pinned
[Plonky3 AIR](../../compiler/adapters/plonky3/README.md) and
[OpenVM relation](../../compiler/adapters/openvm/README.md) integrations keep their
own manifests and toolchains. LLZK remains separate from the main compiler process.

## Contributor references

| Task | Owner |
|---|---|
| Configure paths, parallelism and reports | [Configuration](configuration.md) |
| Locate components and dependency rules | [Repository layout](layout.md) |
| Add operations, passes or backends | [Extensions](extensions.md) |
| Maintain pins, packages and CI | [Maintenance](maintenance.md) |
| Write and validate documentation | [Documentation](documentation.md) |

The shell supplies clangd, clang-format and rust-analyzer. Point clangd at the
selected build's `compile_commands.json`. Use `cargo fmt`, `just fmt-cpp`,
Ruff and `nix fmt` through their owning scopes; keep unrelated formatting separate.
