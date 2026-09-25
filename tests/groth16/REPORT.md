# Groth16 fixture evidence

This record establishes **Circom/snarkjs fixture reproduction and independent
prover-algebra agreement only**. The later results from the delivered Rust tool
and relation-aware PIR path are recorded separately in
[INTEGRATION.md](INTEGRATION.md). This fixture record makes no end-to-end zkc
claim, secure ceremony claim, general backend conformance claim or independent
pairing implementation claim.

The setup uses public deterministic beacons. Its tau, alpha, beta and delta
trapdoors are deliberately reconstructed and published for testing. Fixed
`(r,s)=(1,2)` and `(0,0)` proofs are equality vectors, not private proofs.

## Preserved experiment

Both complete circuits constrain the Poseidon leaf, every boolean direction,
every Merkle path hash and the public root. The sparse-tree leaf indices are
1 and 42301. circomlib Poseidon(2), rather than Poseidon2, is used throughout.
The compiler flags are `--O2 --prime bn128 --r1cs --wasm --sym`.

| Depth | Constraints | Witness entries | QAP domain | Actual named controls |
|---|---:|---:|---:|---:|
| 2 | 726 | 731 | 1024 | 19 |
| 16 | 4128 | 4147 | 8192 | 61 |

The original fixture's complete checksum manifest was verified before importing
any evidence. [The retained manifest](evidence/artifact-manifest.json) pins 39
deterministic artifact identities, including the original setup, keys, compiled
circuits, witnesses and fixed outputs. It retains hashes, not the large files.
[Original machine metadata](evidence/original-versions.json) records the observed
compiler binary hash; it is not a portable binary identity requirement.

The final proving-key SHA-256 values are:

- Depth 2: `2463806d45d62f6a37e6e6bf8ea08cfa339be4d480d0264ffcf839f4e8c31260`.
- Depth 16: `b1ceae3168d3bac44dba5f9a1b9397b0f9952d667d6a87f08aba8c64daee6081`.

## Exact comparisons

The independent implementation checks every original R1CS constraint, every
additional constant/public QAP row and zero padding. It compares all A/B/C
coefficient and coset values against ffjavascript: 55,296 scalar comparisons
over the two domains. Thirteen full vectors per depth have pinned lengths,
encodings and SHA-256 digests, totaling 26 digests and 115,470 scalar entries.
The compact records retain roots, Montgomery factors, binary section layouts,
sampled coefficients, all five MSM results per depth, eight H-query samples,
public trapdoors and final proof scalars.

All five MSMs at both depths agree with independently derived generator
multiples. All four fixed proofs agree exactly with the controlled upstream
prover. Natural-order FFT roots, odd-coset numerator scalars, `c*R^2` coefficient
encoding and the maximal-domain identity padding are checked explicitly.
See the [depth-2](evidence/depth2/intermediates.json) and
[depth-16](evidence/depth16/intermediates.json) records.

The controlled prover changes **only two randomizer lines**; original and
modified source hashes and the exact diff are checked before use and again
after validation. The verifier and compiled upstream CLI remain unchanged.
EC primitives and the final pairing verifier share ffjavascript with snarkjs;
the beacon decoder also uses upstream code. The independent component is the
BigInt Poseidon/QAP/FFT/binary decoding and scalar proof reconstruction, not a
second independent curve or pairing implementation.

## Actual controls

[Depth-2 outcomes](evidence/depth2/controls.json) and
[depth-16 outcomes](evidence/depth16/controls.json) preserve all **80 named
controls**, comprising 72 rejection checks and eight positive/repeat checks.
They cover changed root, secret and blinding; every sibling and direction;
nonboolean directions with a consistently recomputed root; zero and field-edge
valid inputs; tampered binary witness rejection; a proof emitted from that bad
witness and rejected by the verifier; changed/noncanonical public input;
negated A; swapped G2 coefficients; and exact repeats of both fixed proofs.

The ordinary randomized prover and verifier are also exercised. An invalid
witness can reach the upstream prover, so witness satisfaction and final
verification are separate checks. A passing controlled test is evidence about
these fixed inputs and implementations; the known trapdoors preclude a sound
production setup claim.

## Maintained-package validation

The [maintained reproduction receipt](evidence/reproduction.json) records three
successful modes: imported-artifact `validate`, a complete `all` rebuild, and
`reuse-setup` with fresh circuit compilation, witnesses and circuit-specific
keys. The latter two ran from relocated, read-only copies of this package.
The full rebuild also regenerated the public power-13 setup. Each run installed
the locked npm graph with `npm ci`; no copied Node installation was needed.

All 39 deterministic artifact hashes, 26 full-vector hashes, four fixed proofs
and 80 controls matched. The ordinary randomized proofs verified too. Source
snapshots remained unchanged. Fourteen focused Python tests check altered
artifact/proof/lock/source rejection, clean pinned checkouts, safe workdir
selection, repeated staging from a read-only source copy, and replacement of a
stale success record when a rerun fails. Python lint/format and JavaScript syntax
checks passed. These 14 harness tests
are separate from the 80 original fixture controls.

The exercised dependency route used the exact local Git checkout and a populated
npm cache in offline mode. Fresh network fetch and a fresh native Circom build
are supported paths but were not exercised in these runs. The supplied Circom
binary's source checkout, version and current hash were checked. Timings in the
receipt describe this machine and include the named command's startup; they are
not zkc performance claims. Native binary reproducibility across hosts is not
claimed. A subsequent `validate` rerun also passed in the existing workdir after
the read-only staging regression was repaired.
