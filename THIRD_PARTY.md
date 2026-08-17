# Third-Party Software and Research Artifacts

zkc is licensed under Apache-2.0, except for the third-party material
identified here, which remains under its upstream terms. This inventory covers
the source snapshot. It is not a generated license bundle for binary
distribution.

## Material included or adapted in this repository

### Plonky3

- **Upstream:** [Plonky3](https://github.com/Plonky3/Plonky3/tree/3da346791c813433b201299afc3d10bf42f8a078)
- **Revision:** `3da346791c813433b201299afc3d10bf42f8a078`
- **Upstream license:** MIT OR Apache-2.0
- **Copyright:** Copyright (c) 2022 The Plonky3 Authors

The following local material is translated, adapted, or generated from that
revision:

- [`lib/Interpreter/Plonky3Profile.cpp`](lib/Interpreter/Plonky3Profile.cpp)
  and [`reference/oracle/babybear.py`](reference/oracle/babybear.py):
  Poseidon2 constants and permutation/duplex behavior, plus a known-answer
  vector transcribed from the pinned BabyBear implementation and tests;
- [`evaluation/upstream/plonky3-replay/src/bin/trace.rs`](evaluation/upstream/plonky3-replay/src/bin/trace.rs):
  pinned permutation and duplex observations used by the integration checks;
- [`evaluation/upstream/plonky3-replay/src/lib.rs`](evaluation/upstream/plonky3-replay/src/lib.rs):
  a small Fibonacci AIR adapted from the pinned `p3-uni-stark` test AIR; and
- [`evaluation/upstream/plonky3-replay/fixtures/duplex_babybear.json`](evaluation/upstream/plonky3-replay/fixtures/duplex_babybear.json)
  and [`evaluation/upstream/plonky3-replay/fixtures/fib_babybear.json`](evaluation/upstream/plonky3-replay/fixtures/fib_babybear.json):
  outputs generated through the pinned Plonky3 implementation.

This redistributed material is used under the MIT option. Its required notice
is reproduced below:

> The MIT License (MIT)
>
> Copyright (c) 2022 The Plonky3 Authors
>
> Permission is hereby granted, free of charge, to any person obtaining a copy
> of this software and associated documentation files (the "Software"), to deal
> in the Software without restriction, including without limitation the rights
> to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
> copies of the Software, and to permit persons to whom the Software is
> furnished to do so, subject to the following conditions:
>
> The above copyright notice and this permission notice shall be included in
> all copies or substantial portions of the Software.
>
> THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
> IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
> FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
> AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
> LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
> OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
> THE SOFTWARE.

### ArkLib declaration records

- **Upstream:** [ArkLib](https://github.com/Verified-zkEVM/ArkLib/tree/fad5cbf808774838924dc8273715724c6a6caa1f)
- **Revision:** `fad5cbf808774838924dc8273715724c6a6caa1f`
- **License:** Apache-2.0
- **Authors at the pin:** the ArkLib contributors listed in its `AUTHORS` file,
  including Quang Dao, Devon Tuma, Gregor Mitscha-Baude, Bolton Bailey,
  Frantisek Silvasi, Ilia Vlasov, Julian Sutherland, Chung Thai Nguyen,
  Poulami Das, and Mirco Richter.

[`registry/soundness-signature.json`](registry/soundness-signature.json)
contains normalized printed Lean declaration types and axiom-profile
observations from that revision. Related tests and documentation interpret
those records. No ArkLib source tree, compiled object, or proof term is
vendored or executed by the compiler.

## Fetched or linked dependencies

These dependencies are not vendored in this source repository:

| Dependency | Use | Version authority | License at the reviewed source |
|---|---|---|---|
| LLVM, MLIR, and lit | Compiler infrastructure and test runner | MLIR 23 or newer, checked in [`CMakeLists.txt`](CMakeLists.txt) | Apache-2.0 WITH LLVM-exception |
| Plonky3 crates | Optional replay/prover evaluation harness and the emitter runtime (`emit/zkc-rt`) | evaluation and emit `Cargo.toml` and `Cargo.lock` | MIT OR Apache-2.0 |
| arkworks crates (`ark-bls12-381`, `ark-ec`, `ark-ff`, `ark-serialize`) | The emitter runtime's BLS12-381 kernel for the KZG check adapters | [`emit/Cargo.lock`](emit/Cargo.lock) | MIT OR Apache-2.0 |
| `postcard`, `serde`, `serde_json`, `sha2`, `hex`, `zeroize`, and their transitive crates | Optional Rust harness and emitter support | [`evaluation/upstream/plonky3-replay/Cargo.lock`](evaluation/upstream/plonky3-replay/Cargo.lock), [`emit/Cargo.lock`](emit/Cargo.lock) | Per-crate terms; not redistributed in this source tree |
| Rust | Builds the optional Rust harness | stable toolchain available on the host | Rust toolchain component licenses |
| ArkLib, Lean, Lake, Mathlib, and elan | Separate formalization-drift reading | [`registry/upstreams.json`](registry/upstreams.json) and the pinned ArkLib dependency files | Per-project terms; not compiler dependencies |
| uv and Hatchling | Python environment and packaging tools | workflow plus Python project files | Tool-specific terms; executables are not vendored |
| GitHub Actions used by workflows | Checkout, cache, and uv setup | exact major action tags in `.github/workflows/` | Action-specific terms; not part of zkc artifacts |

The Python reference project declares no third-party runtime Python packages.
Its build backend is fetched only when packaging requires it.

## Provenance-only source coordinates

The [evaluation overview](evaluation/README.md#regression-provenance) records
the source coordinates behind the Linea and SP1/Plonky3 semantic regression
fixtures. It does not archive or redistribute those repositories.

The Linea entries are citations and coordinates only. No license file or
package license field was found at the reviewed revisions; that absence must
not be treated as permission to copy upstream source into a release.

Other papers, specifications, and repositories cited in documentation or rule
annotations are references, not incorporated dependencies. Entries without a
source revision or license, including the `simple-rbr-fri` and Isabelle AFP
Sumcheck references in the current signature, must remain citations only.

## Binary distribution

Before publishing a binary, container, package, or bundled toolchain, generate
and review a complete license-and-notice bundle for every included LLVM
component, Rust crate, runtime library, and packaged asset. This source
inventory does not by itself clear a binary distribution.

<!-- The revisions above are restated from registry/upstreams.json, and are held to it: upstream-pin: arklib upstream-pin: plonky3 -->
