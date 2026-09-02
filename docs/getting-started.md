# Getting Started

This guide builds the current zkc research snapshot on Linux.

## Prerequisites

- Git, a C/C++ toolchain, CMake 3.20 or newer, and Ninja
- MLIR 23 or newer, with its development files and `mlir-tblgen`
- [uv](https://docs.astral.sh/uv/) with Python 3.14 or newer available or
  managed by uv
- `lit`, and LLVM's `FileCheck`, `not`, and `count`
- network access for the initial package and Python fetches

The development workflow is tested on Linux. Other platforms may work but are
not currently tested.

## 1. Provide MLIR

zkc needs MLIR 23 or newer. That is a floor rather than a pin: any newer
toolchain that still builds the sources is acceptable, and the version is
checked at configure time. PIR represents its dependency edges as the builtin
`token` type, which MLIR gained in 23; nothing else here constrains the
toolchain, and artifact identity is computed over zkc's own canonical
encoding rather than anything MLIR emits.

On Debian or Ubuntu, take it from [apt.llvm.org](https://apt.llvm.org):

```sh
codename="$(. /etc/os-release && echo "$VERSION_CODENAME")"
wget -qO- https://apt.llvm.org/llvm-snapshot.gpg.key \
  | sudo tee /etc/apt/trusted.gpg.d/apt.llvm.org.asc > /dev/null
echo "deb http://apt.llvm.org/${codename}/ llvm-toolchain-${codename}-23 main" \
  | sudo tee /etc/apt/sources.list.d/llvm.list
sudo apt-get update
sudo apt-get install -y libmlir-23-dev mlir-23-tools llvm-23-tools ninja-build
```

That installs under `/usr/lib/llvm-23`, which is what the configure step
below points at. Other distributions ship MLIR under their own names; any
installation that provides `MLIRConfig.cmake`, `mlir-tblgen`, and the LLVM
test utilities will do.

Building LLVM and MLIR from source also works and is the only option where no
package exists. It is far slower, and nothing here requires a specific
revision.

## 2. Provide lit

The suite runs under LLVM's lit. Install it however you prefer — `pipx
install lit`, `uv tool install lit`, or the copy in an llvm-project checkout —
and point the build at it:

```sh
export LLVM_EXTERNAL_LIT="$(command -v lit)"
```

## 3. Prepare the reference environment

```sh
uv sync --locked --project reference
```

The compiler does not depend on Rust or Plonky3. The optional integration
harness lives under `evaluation/upstream/`.

## 4. Configure and build zkc

Point the environment-driven `ci` preset at the MLIR installation from step 1:

```sh
export MLIR_DIR=/usr/lib/llvm-23/lib/cmake/mlir

cmake --preset ci
cmake --build --preset ci
```

Configuring refuses an MLIR older than 23 and names the version it found.

The `dev` preset is a maintainer-local convenience preset and is not the public
setup interface.

## 4a. The shipped tools

Ten tools land in `build/bin`, beside the test-only pass driver. Each takes
`--help`; this is what they are for and which are load-bearing for the claims in
[Current Status](status.md).

Each answers one question, and its exit code says which of three things
happened. **0** — the question was answered affirmatively. **1** — the subject
was examined and the answer is negative: a registry that does not admit, a
witness that does not re-derive, a verifier that rejects, a contract that
disagrees with the bytes it pins. **2** — the invocation never reached its
subject: an unreadable file, a flag naming no job, a registry the environment
does not supply.

A caller that treats every non-zero exit alike cannot tell a protocol it should
fix from an invocation it should fix. Both write to stderr in the same spelling,
because the code is what a script reads and the message is what a person reads.

| Tool | What it does |
|---|---|
| `zkc-seal` | Seal one textual Open PIR protocol into a persisted artifact directory. The seal judgment runs here. |
| `zkc-artifact` | Load one persisted artifact through the fail-closed gate and report its identity. `--expect-id` refuses anything else. |
| `zkc-project` | Project an admitted artifact to an endpoint, carrying admission through. |
| `zkc-translate` | Emit one canonical encoding or identity — `--canonical`, `--id`, `--oir-canonical`, `--oir-id`, `--oir-semantic-id`, `--proof-size`, `--transcript-schedule`. Exactly one per invocation. |
| `zkc-run` | Execute an endpoint. `--vectors` checks a verifier against golden vectors, `--prove` runs a prover skeleton and can verify what it produced, `--replay-duplex` replays a pinned upstream transcript. This is the tool behind every "Verifier path" and "Prover path" cell. |
| `zkc-derive` | Derive a soundness or completeness judgment from an admitted artifact plus a signature. `--describe` lists the application sites an artifact offers; `--check` re-derives a recorded witness. |
| `zkc-registry-lint` | Load one registry fail-closed and print its normalized content — the carrier half of every registry parity test. |
| `zkc-relation` | Judge a relation contract against an admitted artifact, reporting what was computed, what two declarations agree on, and what remains asserted, apart. Reads the relation's bytes where the format has a reader. |
| `zkc-family` | Generate a parameterized protocol family (currently FRI). |
| `zkc-opt` | The MLIR pass driver, carrying the zkc dialects and passes. |

The golden-vector file `zkc-run --vectors` reads is a JSON document
`{artifact_id, source, vectors: [{name, statement, proof, challenges,
expect}]}`; the checked-in examples are under
[`test/Oir/Inputs/`](../test/Oir/Inputs/), and
`uv run --project reference python -m oracle.exec <name>` regenerates one.

## 5. Run the checks

These are what continuous integration runs.

```sh
tools/public-tree-guard.sh

cmake --build --preset ci --target check-zkc
uv run --locked --project reference python -m oracle.model
uv run --locked --project reference python -m unittest discover \
  -s reference/tests -v
uvx ruff check .

cargo test --locked --manifest-path emit/Cargo.toml -p zkc-emit
cargo test --locked --manifest-path emit/Cargo.toml -p zkc-rt --features toy,plonky3
cargo clippy --locked --manifest-path emit/Cargo.toml --all-targets --all-features -- -D warnings
(cd emit && cargo fmt --check)
```

The lit suite includes C++/MLIR checks, differential checks against the Python
reference twin, and Cargo-backed pinned replay checks when Cargo is available;
`oracle.model` runs the twin's semantic self-checks directly. The adjacent
unittest command checks its canonical facade and module dependency boundaries.
`ruff` reads every Python file in the tree, not only the twin's. The Cargo
commands cover the emit workspace and need Rust, which the compiler itself
does not.

Each `--locked` is deliberate: a dependency change lands together with its
updated lock file, or the check fails.

## 6. Exercise the persisted PIR handoff

The normal persisted path seals textual Open PIR once, then decodes and admits
the resulting artifact before each semantic consumer. From the repository
root after building:

```sh
ZKC_QUICKSTART_DIR="$(mktemp -d)"
mkdir -p "$ZKC_QUICKSTART_DIR/artifacts"

build/bin/zkc-seal test/Encoding/routed-schnorr.mlir \
  --protocol-vocabulary registry/protocol-vocabulary.json \
  --construction-profile-registry registry/construction-profiles.json \
  --output-dir "$ZKC_QUICKSTART_DIR/artifacts"

build/bin/zkc-project "$ZKC_QUICKSTART_DIR"/artifacts/*.mlirbc \
  --endpoint-kind verifier \
  --protocol-vocabulary registry/protocol-vocabulary.json \
  --construction-profile-registry registry/construction-profiles.json \
  -o "$ZKC_QUICKSTART_DIR/verifier.mlir"

build/bin/zkc-derive "$ZKC_QUICKSTART_DIR"/artifacts/*.mlirbc \
  --describe \
  --signature registry/soundness-signature.json \
  --protocol-vocabulary registry/protocol-vocabulary.json \
  --construction-profile-registry registry/construction-profiles.json
```

`zkc-project` emits one verifier OIR artifact. `zkc-derive --describe` lists the
soundness application sites derived from the same admitted PIR. The in-process
checked compiler accepts the same `AdmittedPirArtifact` capability through its
PIR artifact-semantics provider; this snapshot does not define a persisted
compiler-request schema or compiler CLI.

## Dependency policy

| Surface | Requirement | Authority |
|---|---|---|
| MLIR and lit | MLIR 23 or newer; any lit that runs the suite | [`CMakeLists.txt`](../CMakeLists.txt) |
| zkc build | CMake 3.20+, Ninja, C++17 | [`CMakeLists.txt`](../CMakeLists.txt) |
| Python reference twin | Python 3.12+ and **no dependencies at all** | [`reference/pyproject.toml`](../reference/pyproject.toml) and [`reference/uv.lock`](../reference/uv.lock) |
| Optional Plonky3 harness | stable Rust 1.85 or newer (the crate is edition 2024); the upstream revision | its `Cargo.toml` and `Cargo.lock` |
| ArkLib receipt reading | exact ArkLib revision | [`registry/upstreams.json`](../registry/upstreams.json) and the checkout's Lean/Lake files |

Each of these is as tight as what it guards, and no tighter.

The **toolchain** is a floor rather than a revision because nothing depends on
one. The identity a sealed artifact receives is computed over zkc's own
canonical encoding, and `.mlirbc` bytes are explicitly not a stable surface
([versioning](spec/versioning.md)), so a specific MLIR revision would buy only
"it compiled" — which the floor and the suite already establish.

The **reference twin** declares an empty dependency set, and `uv sync --locked`
is what keeps it empty: the lockfile is not pinning a dependency graph, it is
refusing one. The twin's byte parity is an acceptance gate only because it was
written independently, and a library shared with the compiler would quietly
weaken that. The Python floor is the oldest interpreter the twin is run on.

**ArkLib** is pinned to an exact revision for the opposite reason to the
toolchain: a receipt names a declaration *in* one revision, so reading a
different one is a different observation, and the reading driver refuses a
checkout that is not at the pin.

The **Plonky3** revision is likewise part of what the replay evidence claims,
and it is named once, in the harness's `Cargo.toml`, where Cargo enforces it.
The compiler's own transliterated constants are guarded by the permutation's
known-answer self-check rather than by any recorded revision.

The repository does not pin byte-identical native builds. The host compiler,
linker, Linux patch level, CPU, libc, CMake and Ninja versions above their
minimums, and uv executable are not frozen. CI currently covers Linux.

Raising the floor is a deliberate edit to the configure check, made after the
full suite and the relevant evaluation harness run against the newer toolchain
and artifact identity, encoded vectors, diagnostics, and upstream
correspondence are inspected for drift.

## Optional Plonky3 integration

When Cargo is on `PATH`, the lit suite also enables its Cargo-backed Plonky3
integration tests. The compiler build and the rest of the suite do not require
Cargo. To run the replay harness directly with the stable Rust toolchain on
your system and its locked dependency graph:

```sh
cd evaluation/upstream/plonky3-replay
cargo run --locked --quiet --bin replay -- fixtures/fib_babybear.json
```

## Common setup failures

- **`MLIRConfig.cmake` not found:** `MLIR_DIR` must end in `lib/cmake/mlir`
  inside the MLIR installation.
- **configuring refuses the toolchain version:** the installed MLIR is older
  than 23. The message names what it found.
- **lit is missing or not executable:** install it and point
  `LLVM_EXTERNAL_LIT` at the executable.
- **a Python differential is unsupported:** run `uv sync --locked --project
  reference` and ensure `uv` is on `PATH` before configuring.
