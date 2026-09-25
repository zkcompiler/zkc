# Groth16 test fixtures

This package generates the test suite's Groth16 fixtures: complete BN254
Poseidon Merkle membership circuits at depths 2 and 16, independent BigInt
reference arithmetic, and a pinned Circom/snarkjs reproduction pipeline.
`just test-groth16 WORKDIR` runs the three zkc-tools interoperability tests
against a generated workdir, the directory holding `artifacts/depth2` and
`artifacts/depth16`. [REPORT.md](REPORT.md) covers the fixtures alone and
[INTEGRATION.md](INTEGRATION.md) the relation-aware zkc integration. Both
records concern these two fixed fixtures and do not establish general Groth16
conformance. See [COMPATIBILITY.md](COMPATIBILITY.md) for exact encodings and
equations.

**Public deterministic trapdoors and fixed proof randomizers are test data.
This setup is deliberately insecure and must never protect real statements.**
The reference reconstructs the trapdoors to check algebra, and exports them in
the intermediate record.

## Preserved vectors

[`evidence/`](evidence) holds the known-answer data the suite checks without
regenerating anything: two fixed proofs per depth, their public inputs,
verification keys, calldata and hash vectors, with digests in `SHA256SUMS`.

```sh
python3 tests/groth16/reproduce.py check-evidence
python3 -m unittest discover -s tests/groth16/tests
```

The first compares every preserved artifact and vector digest and fails on any
difference. The second checks the reproducer itself: staged workdirs, immutable
source copies and the evidence comparison.

## Generate from a clean copy

The [Nix environment](../../docs/development/README.md) packages the complete pinned
toolchain and performs the maintained reproduction in a sandbox:

```sh
nix build .#groth16
nix build .#groth16-checks
```

The first output contains fixtures and reproduction records; the second also
runs the Rust interoperability tests and the relation-aware integration. The
source-pinned Circom includes an LLZK backend, so its Nix package also supplies
that backend's pinned LLVM/LLZK dependencies. The manual route below accepts an
already built binary from that source.

Requirements: Python 3.12+, Node.js 20+ and npm, Git, and Circom **2.2.2** built
from commit `5de739581d23ebe0bdb9c4255a106f6dc7d8a5cf`. The recorded run used
Node 24.20.0; other versions are not a tested compatibility claim. To build the
pinned compiler yourself, use `cargo build --release --locked` in that checkout.
Pass its binary explicitly:

```sh
python3 tests/groth16/reproduce.py all \
  --workdir /tmp/groth16-run \
  --circom /absolute/path/to/circom
```

`all` fetches the exact circomlib commit from [SOURCE_PINS.json](SOURCE_PINS.json),
runs `npm ci --ignore-scripts` against the maintained lock, compiles both
circuits, generates and checks the public test setup, proves, verifies and runs
all 80 controls. The source tree is hashed before and after. All dependencies,
generated code, keys, witnesses, vector buffers, logs and results live in the
chosen workdir. Omit `--workdir` for a fresh temporary directory, or use the
ignored `tests/groth16/.work`. A nonempty directory must carry this runner's
marker. No existing fixture directory is required for a full run.

An existing clean Circom checkout can instead be supplied with
`--circom-source /path/to/checkout`. Its exact commit and clean state are checked;
the runner uses `target/release/circom` if present or builds with `--locked` into
the workdir. You may combine `--circom-source` and `--circom` when your build uses
another target directory. Existing binaries remain caller-supplied build
artifacts: version and the **current** binary hash are recorded. The original
machine's native binary SHA-256 is an observation, not a cross-machine pin.
`--circom-sha256 HASH` optionally enforces the caller's selected binary hash.

For offline use, provide a clean circomlib checkout at the pinned commit and a
previously populated npm tarball cache:

```sh
python3 tests/groth16/reproduce.py all \
  --workdir /tmp/groth16-offline \
  --circom /absolute/path/to/circom \
  --circomlib-source /absolute/path/to/circomlib \
  --npm-cache /absolute/path/to/npm-cache --offline
```

The circomlib pin is nine commits after its 2.0.5 tag, **not** the npm release.
Local checkouts are exported with `git archive`; they are never modified. npm
still runs `ci` offline and verifies the locked tarball integrities. Dependencies
are not copied from an unchecked `node_modules` tree.

## Reuse a verified setup or fixture

```sh
# Recompile, regenerate witnesses and circuit keys, reuse only phase-1 setup.
python3 tests/groth16/reproduce.py reuse-setup \
  --workdir /tmp/groth16-rebuild --reuse-artifacts /path/to/previous-run \
  --circom /absolute/path/to/circom

# Recheck imported artifacts and rerun proof/reference/control calculations.
python3 tests/groth16/reproduce.py validate \
  --workdir /tmp/groth16-replay --reuse-artifacts /path/to/previous-run
```

Both modes accept the offline options above. A previous run has an
`artifacts/` child; pass the run directory, not that child. `validate` needs no
compiler because it checks the retained compiled artifacts against the exact
manifest. Omit `--reuse-artifacts` when reusing the chosen workdir itself.
Import checks the saved hashes **before** copying or recomputing outputs. Every
validation reruns the untouched witness/key checkers, ordinary randomized
prover/verifier, four fixed proofs, independent algebra and all 80 named controls.
The scripts under `scripts/` are internal staged-workdir programs; use this entry
point rather than invoking them in the source package.

## Maintained files and generated results

`circuits/` holds the complete authored relation. `scripts/poseidon.mjs` and
`make-inputs.mjs` build independent reference hash paths. `math-reference.mjs`
parses binary key/witness sections and checks all QAP rows, FFT values, MSMs and
fixed proofs. `controls.mjs` retains each named control. The Python stages handle
the build, the exact randomizer-only source patch, validation and metadata.

Witness arrays, `.ptau`, `.zkey`, `.r1cs`, `.wasm`, native compilers,
`node_modules`, copied snarkjs sources and full logs are generated only in the
workdir; no results are committed. [DEPENDENCIES.md](DEPENDENCIES.md) records the
isolated GPL and LGPL dependencies this generator fetches.

Each successful run writes `RESULTS.json`, current `VERSIONS.json`,
`source-manifest.json`, `artifact-manifest.json` and logs in its workdir. The
generated `artifacts/depth{2,16}/intermediates.json` includes full vector hashes;
`vectors/*.frle` contains canonical 32-byte little-endian scalars for locating a
disagreement. Random proofs and wall times are measured outputs, not
deterministic equality vectors. A failed rerun replaces `RESULTS.json` with a
failure record so an earlier success cannot be mistaken for the current outcome.

## Run the zkc integration

After a successful fixture generation, pass the separately built tools and
the maintained explicit PIR source. The zkc tool must have the `test-utils`
feature for the two explicit fixed-randomness comparisons. See the repository's
native build instructions for compiler and Lean prerequisites; this runner does
not modify or build their sources.

```sh
cargo build --release --locked -p zkc-tools --features test-utils \
  --bin groth16-artifact
python3 tests/groth16/run_zkc.py \
  --workdir /tmp/groth16-run \
  --zkc target/release/groth16-artifact \
  --compiler build/compiler/zkc-compile \
  --lean formal/.lake/build/bin/interactive-protocol \
  --source examples/protocols/groth16.pir --iterations 3
```

`run_zkc.py` rechecks the fixture artifacts and original upstream source hashes,
then compiles with the actual R1CS, saves admitted code, compares both fixed
proofs at both depths, cross-verifies fresh proofs and executes 16 additional
rejection controls. Verifier calls use saved code, expected relation identity,
VK, public input and proof, without R1CS, zkey or witness. It records preparation,
import, binding, repeated execution and process timings separately. Output lives
under the same workdir's `zkc/`; external binaries and PIR source are hashed
before and after. [INTEGRATION.md](INTEGRATION.md) states the observed scope.
