# Dependency provenance

This harness downloads or exports its test dependencies
only into a caller-selected workdir. No Circom/circomlib source distribution,
native compiler, Node modules, or whole modified snarkjs tree is vendored in the
maintained package. The controlled source copy stays in that workdir and retains
upstream `COPYING`. The maintained patch is a two-line test adaptation of the
pinned GPL snarkjs prover. The original verifier/CLI are never patched.

The entries below describe provenance. None of them is a claim that another
part of this repository has adopted their licence or their security assumptions.

| Component | Exact source/version | Upstream license | Use here |
|---|---|---|---|
| Circom | [iden3/circom](https://github.com/iden3/circom/tree/5de739581d23ebe0bdb9c4255a106f6dc7d8a5cf), commit `5de739581d23ebe0bdb9c4255a106f6dc7d8a5cf`, 2.2.2 | GPL-3.0 (`COPYING`) | External circuit compiler; explicit caller-supplied binary or local build, current hash recorded per run. |
| circomlib | [iden3/circomlib](https://github.com/iden3/circomlib/tree/35e54ea21da3e8762557234298dbb553c175ea8d), commit `35e54ea21da3e8762557234298dbb553c175ea8d`, package 2.0.5 / `v2.0.5-9-g35e54ea` | LGPL-3.0 (`LICENSE`) | Unchanged optimized Poseidon circuit and unoptimized constants, fetched/exported only in workdir. |
| snarkjs | [iden3/snarkjs v0.7.5](https://github.com/iden3/snarkjs/tree/v0.7.5), npm 0.7.5 with locked tarball integrity | GPL-3.0 (`COPYING`) | Test setup, proof and untouched verifier/CLI; controlled copy differs only in two explicit r/s randomizer lines. |
| ffjavascript | npm 0.3.1, exact tarball/integrity in lock | GPL-3.0 | Shared BN254 EC/FFT primitives; not an independent pairing implementation. |
| ffjavascript (nested under r1csfile) | npm 0.3.0, exact tarball/integrity in lock | GPL-3.0 | Separately locked transitive version used by r1csfile. |
| wasmcurves | npm 0.2.2, exact tarball/integrity in lock | GPL-3.0 | Upstream arithmetic/QAP implementation used through ffjavascript/snarkjs. |
| wasmbuilder | npm 0.0.16, exact tarball/integrity in lock | GPL-3.0 | Upstream WebAssembly builder. |
| @iden3/bigarray | npm 0.0.2, exact tarball/integrity in lock | GPL-3.0 | Upstream integration dependency. |
| @iden3/binfileutils | npm 0.0.12, exact tarball/integrity in lock | GPL-3.0 | Upstream binary-container support. |
| fastfile | npm 0.0.20, exact tarball/integrity in lock | GPL-3.0 | Upstream file support. |
| r1csfile | npm 0.0.48, exact tarball/integrity in lock | GPL-3.0 | Upstream R1CS reader/checker. |
| circom_runtime | npm 0.1.28, exact tarball/integrity in lock | Apache-2.0 | Witness runtime dependency; Circom also emits witness helper files. |

[package-lock.json](package-lock.json) is authoritative for all transitive npm
versions, registry URLs, integrity values and declared licenses, including
nested package versions. `npm ci --ignore-scripts` installs this graph without
package lifecycle scripts. It is isolated from the Rust application build.

[SOURCE_PINS.json](SOURCE_PINS.json) pins the source commits, setup beacons and
versions. [source-integrity.json](evidence/source-integrity.json) pins original
prover, controlled prover, untouched verifier and CLI hashes.
[prover-rng-only.diff](evidence/prover-rng-only.diff) is the complete patch.
The native Circom binary's original SHA-256 is preserved only as original-machine
evidence; newly built binaries are version checked and their own hashes recorded.
