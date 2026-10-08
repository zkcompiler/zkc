# Toolchain and CI maintenance

Native manifests own selected dependency versions; Nix locks the tools and package
inputs used to build them. Prefer current stable releases when upgrading unless
an actual compatibility constraint requires otherwise. Keep unrelated upgrades
separate and record selected versions in the owning manifest.

## Pins and source ownership

| Boundary | Owner |
|---|---|
| Main LLVM/MLIR and C++ packages | Compiler CMake requirements and Nix inputs |
| Rust workspace | Cargo manifests, lockfile and toolchain selection |
| Python tooling | `pyproject.toml` and `uv.lock` |
| Independent Lean package | `formal/lean-toolchain`, Lake manifests and lockfiles |
| Optional integrations | Their own manifests, source pins and compatible toolchains |

LLZK remains a generic optional relation adapter with a separate LLVM process.
Do not link incompatible LLVM versions into the main compiler. Formal source
builds, reached-axiom audits and optional ArkLib consumers retain their own scopes;
they are not default native execution prerequisites.

## Upgrade and validate

Update the owning pin and its resolved lock/hash together. Inspect API, schema,
codec and behavior changes at actual consumers. Reconfigure fresh build trees
when compiler ABI or toolchain identity changes. Run affected native tests,
installed static/shared consumers and package checks according to the change.
Use [configuration](configuration.md) to select explicit existing outputs.

Caches accelerate builds; they do not establish that a source reproduction ran.
Distinguish an incremental test, a clean native build and a sandboxed Nix package
in the result. Keep previous failure reports, exact commands and selected outputs
when diagnosing a disagreement.

## Workflow scopes and reports

The [test guide](../../tests/README.md) and CI manifests own current scopes.
Default execution checks cover C++/Rust. Formal checks and external integrations
are explicit standalone work. Groth16 application/fixture packages and legacy
Lean-host execution dependencies are retired.

A direct test driver requires built tools. Report directories are allocated
independently of shared build trees; concurrent reports do not isolate concurrent
CMake, Cargo or Lake mutations. Serialize writes to one build/profile. Use
bounded relevant checks before broad integration, and retain resource-boundary
cases in the scope that owns them.

## Public documentation

A published guide should describe current commands and support. Move durable
semantic decisions into their owning specification or design page; remove
superseded implementation guides instead of preserving a compatibility archive.
Private review/process records stay outside the public reference. Follow the
[documentation guide](documentation.md) and run its link/whitespace checks.
