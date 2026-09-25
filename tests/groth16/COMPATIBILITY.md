# Exact compatibility contract

These notes describe the **preserved fixture** and inspected snarkjs **0.7.5** code. `SOURCE_PINS.json`, `evidence/original-versions.json`, `evidence/SHA256SUMS` and `evidence/artifact-manifest.json` identify the inputs. Paths under `artifacts/`, `reference/` and `node_modules/` below refer to generated work-directory files, not vendored package files. This is a public, deterministic local test setup, with deliberately reconstructible trapdoors; it makes no security claim.

## Circuit and Poseidon

`circuits/merkle.circom` implements the entire relation. The sole public signal is `root`. Private inputs are `secret`, `blinding`, `siblings[depth]`, and `directions[depth]`. The leaf is `Poseidon(secret,blinding)`. A bottom-up direction of 0 hashes `(node,sibling)`; 1 hashes `(sibling,node)`. Every direction satisfies `d*(d-1)=0`, and the final node equals the public root. There are no unconstrained assignments (`<--`).

Poseidon is **circomlib's original Poseidon, not Poseidon2**: width 3, two field inputs, capacity/initial-state word 0, exponent 5, eight full and 57 partial rounds, first state word as output. Leaf and internal hashes use exactly the same function, without an added domain separator. The optimized Circom constants and matrices are pinned to circomlib commit `35e54ea21da3e8762557234298dbb553c175ea8d` (`v2.0.5-9-g35e54ea`); package version alone is not the pin. [Pinned upstream source](https://github.com/iden3/circomlib/tree/35e54ea21da3e8762557234298dbb553c175ea8d).

`scripts/poseidon.mjs` independently implements the unoptimized permutation using that checkout's `poseidon_constants_old.circom`. Its matrix multiplication is `out[i]=sum_j M[i,j]*state[j]`. The optimized circuit instead uses its transformed constants and transposed matrix access; do not mix these representations. `reference/poseidon-t3.json` contains all 195 unoptimized round constants and nine row-major MDS entries. Generated witnesses/checks establish agreement for all fixture hash paths and positive controls.

The field is BN254's **scalar field**:

```
p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
q = 21888242871839275222246405745257275088696311157297823662689037894645226208583
```

Here `q` is the curve-coordinate base field, not the circuit field. All fixture inputs are canonical integers in `[0,p)`. Circom arithmetic provides field semantics, not byte-string hashing or application-specific integer range constraints. The fixtures describe a sparse tree whose other leaves equal `Poseidon(0,0)`: leaf indices 1 and 42301 (`0xa53d`), with least-significant index bits first. Depth 16 means 65,536 leaves. `hash-vectors.json` exports every path node and empty-root reference.

## Witness, R1CS and QAP rows

Circom 2.2.2 compiles with `--O2 --prime bn128 --r1cs --wasm --sym`. The depth-2 artifact has 726 constraints and 731 witness entries; depth 16 has 4,128 constraints and 4,147 witness entries. Witness index 0 is the constant 1, index 1 is the public root; the remaining indices include private inputs and intermediates. Consult the generated `.sym` file rather than deriving indices from source labels: optimized-away labels have witness index -1.

R1CS rows mean `A_i(w)*B_i(w)=C_i(w)`. In [`zkey_new.js`](https://github.com/iden3/snarkjs/blob/v0.7.5/src/zkey_new.js), setup appends **nPublic+1 A rows**, including the constant:

```
A[m+s] = w[s], B[m+s] = 0, C[m+s] = 0, s=0..nPublic
N = 2**ceil(log2(m+nPublic+1))
```

Thus N=1024 and 8192. All remaining evaluation rows are zero. Adding only the public-root row and omitting the constant row is incompatible.

Zkey section 4 stores only sparse **A and B** entries, not C. The prover computes C evaluations as `A[i]*B[i]`. For a valid witness these equal the original R1CS C values. This shortcut does **not** validate a witness; `controls/tampered-proof.json` demonstrates a proof emitted from a bad witness and rejected by the untouched verifier. `scripts/math-reference.mjs` checks every original R1CS row before computing the independent reference.

## Roots, FFT and H-query basis

For these fixtures `k=log2(N)<28`. ffjavascript chooses the smallest quadratic nonresidue, 5. Define:

```
omega = 5**((p-1)/N) mod p
eta   = 5**((p-1)/(2*N)) mod p
eta**2 = omega; eta**N = -1
FFT(a)[i] = sum_j a[j] * omega**(i*j)
IFFT(A)[j] = N**(-1) * sum_i A[i] * omega**(-i*j)
```

Output is in natural index order. Internal bit reversal is an FFT implementation detail, not an external permutation. Exact omega/eta values are exported in each `intermediates.json`. The upstream maximum-field-domain `Fr.shift` branch is not exercised here.

The prover interpolates row evaluations A/B/C, multiplies coefficient j by `eta**j`, and applies FFT. This evaluates on `eta*omega**i`, in that order. The scalar vector passed to the H MSM is:

```
Podd[i] = A(eta*omega**i)*B(eta*omega**i) - C(eta*omega**i)
```

It is the **numerator on the odd coset**, not monomial coefficients of H and not quotient evaluations. With `Z(X)=X**N-1`, the independent quotient evaluations are `Hodd=Podd/(-2)`, and monomial H coefficients are `IFFT(Hodd)[j]*eta**(-j)`. Their final entry is zero. The upstream prover does **not** perform that division, inverse FFT or unshift before its H MSM. See [`groth16_prove.js`](https://github.com/iden3/snarkjs/blob/v0.7.5/src/groth16_prove.js) and [`build_qap.js`](https://github.com/iden3/wasmcurves/blob/v0.2.2/src/build_qap.js).

Section 9 has **N G1 points**, not N-1 monomial H-query points. Initial setup selects the odd entries of the prepared **2N-point group IFFT** of powers of tau; the phase-2 beacon scales them by `delta**(-1)`. Precisely, using group-identity padding where necessary:

```
T[j] = [tau**j]G1, j=0..2N-1
K[i] = (1/delta) * IFFT_2N(T)[2*i+1]
resH = sum_i Podd[i]*K[i] = [(A(tau)*B(tau)-C(tau))/delta]G1
```

**Maximal setup-domain subtlety:** power-13 phase 1 stores tau powers through degree 16382. When N=8192, `T[16383]` above is the **group identity**, not `[tau**16383]G1`. `powersoftau_preparephase2.js` explicitly pads it. The degree of `A*B-C` is at most `2N-2`, so this does not change the final MSM. For N=1024 the needed powers all exist. Calling the maximal-domain points literal full Lagrange evaluations at tau without mentioning this padding would give incorrect individual query points. The independent reference checks samples 0,1,2,N-1 using the corresponding geometric-series formula and verifies the entire H MSM against its scalar value.

## Zkey and Montgomery serialization

The binary container begins with four-byte magic, U32LE version and U32LE section count. Each section is U32LE id, U64LE byte length, then that many bytes; locate sections by id, not physical order. Saved zkeys have format version 1 (the reader accepts up to version 2), R1CS version 1 and witnesses version 2. Exact section offsets/lengths are exported in `intermediates.json`.

| Section | Contents |
|---|---|
| 1 | Protocol id 1, Groth16 |
| 2 | n8q, q, n8r, p, nVars, nPublic, N; alpha1, beta1, beta2, gamma2, delta1, delta2 |
| 3 | nPublic+1 IC points, G1 |
| 4 | U32LE record count; records `(U32LE matrix, U32LE row, U32LE wire, 32-byte coefficient)` |
| 5 / 6 / 7 | nVars A G1 / B G1 / B G2 points |
| 8 | nVars-nPublic-1 private L points, G1; called C by the prover |
| 9 | N odd-query H points, G1 |
| 10 | Circuit hash and phase-2 contribution metadata |

Header integer widths are U32LE except the 32-byte moduli. Follow actual `writeHeader`/`readHeaderGroth16` implementation: the introductory comment in `zkey_utils.js` lists an obsolete point order.

Let `Rp=2**256 mod p`, `Rq=2**256 mod q`. The representations deliberately differ:

- Witness section 2 and R1CS coefficients: canonical field integers, 32-byte little-endian, no Montgomery factor.
- **Zkey section 4 coefficients: `c*Rp**2 mod p`, 32-byte little-endian.** This is neither canonical c nor ordinary Montgomery `c*Rp`. Decode with `Rp**(-2)`.
- ffjavascript Fr arithmetic/FFT memory: `x*Rp mod p`. Upstream `Fr.mul(c*Rp**2,w)` yields `c*w*Rp`, because the witness operand is canonical and Montgomery multiplication divides once by Rp.
- Point-query buffers: affine coordinate limbs in Montgomery form modulo **q**, little-endian. G1 is `(x*Rq,y*Rq)` (64 bytes). G2 is `(x0*Rq,x1*Rq,y0*Rq,y1*Rq)` (128 bytes).
- MSM scalar buffers are canonical, 32-byte little-endian. `joinABC` explicitly calls `frm_batchFromMontgomery` before passing `Podd` to the MSM.

Affine binary infinity is all-zero coordinate limbs; JSON's normalized infinity is `[0,1,0]` (and the Fq2 analogue). Ordinary proof points in these fixtures are finite.

## Proof equations, G2 and verification

Write `SA/SB1/SB2` for witness MSMs of sections 5/6/7, `SL` for section 8 with witness slice beginning at index **nPublic+1**, and `SH` for section 9 with Podd. The exact final equations are:

```
pi_a = SA + alpha1 + r*delta1
pi_b = SB2 + beta2 + s*delta2
b1   = SB1 + beta1 + s*delta1
pi_c = SL + SH + s*pi_a + r*b1 - r*s*delta1
```

The C equation uses the **already randomized** A and B1. The verifier checks `e(A,B)=e(alpha,beta)*e(IC[0]+root*IC[1],gamma)*e(C,delta)` using the corresponding four-pair product with negative A. It reads `node_modules/snarkjs/src/groth16_verify.js` unchanged; CLI checks also use the original `build/cli.cjs`.

In Fq2, an element is `c0+c1*u` with `u**2=-1`. Canonical snarkjs proof JSON is:

```
pi_a: [x,y,"1"]
pi_b: [[x0,x1],[y0,y1],["1","0"]]
pi_c: [x,y,"1"]
protocol: "groth16", curve: "bn128"
```

All numeric entries are decimal strings. Do not swap the G2 coefficients for snarkjs JSON. The **EVM calldata exporter swaps them** to `[[x1,x0],[y1,y0]]`, omits projective coordinates and writes 32-byte big-endian hex words. Matching calldata files are saved. JSON byte endianness is irrelevant; interpret numeric strings as integers. A swapped-G2 control fails the original verifier.

## Reference independence and exact agreement

`scripts/prepare_reference.py` copies upstream source, changes only `Fr.random()` for r and s to `Fr.e(options.fixtureR/S)`, checks that no other source file differs, and saves `reference/prover-rng-only.diff`. The wrapper requires explicit canonical randomizers. `reference/source-integrity.json` records original/controlled prover and original verifier/CLI SHA-256 values. The verifier is never modified.

`scripts/math-reference.mjs` separately parses binary sections, decodes Montgomery factors, evaluates all sparse rows with BigInt, and implements its own FFT. It compares every A/B/C FFT and coset value with ffjavascript; checks all five MSM results against generator multiples derived from the public test trapdoors; checks sampled H-query points including padding; and reconstructs the final proof points from scalar equations. Both fixed proofs exactly equal the controlled upstream prover's output at both depths. This is independent QAP/prover-algebra validation; **the EC primitives and final pairing verifier still share ffjavascript**, and beacon decoding uses upstream code. It is not a second independent pairing implementation.

Agreement requires the same pinned circuit, optimization, witness order, key bytes, public signals and explicit r/s. Compare canonical residues without modularly reducing a malformed candidate: scalar entries in `[0,p)`, coordinate entries in `[0,q)`, G2 coefficient order as above. Normalize valid projective points to the specified affine representation before comparing. **Tolerance is zero** for every field, scalar, point and public signal. There is no permitted sign ambiguity for a fixed proof. JSON whitespace/key order may differ; the parsed canonical values may not. Random `proof.json` is verified but is not an equality vector.

Each fixture's `intermediates.json` contains small first/last samples, added rows, decoded coefficient records, roots, canonical query/MSM points, final proof scalars and digests. `vectors/*.frle` exports full arrays with no header, canonical 32-byte little-endian Fr values; vector lengths and hashes are indexed in the JSON. Use these stages to locate the first disagreement before comparing the final proof.

## Maintained compact evidence

The package retains the intermediate scalar/point checks and SHA-256/length of each full vector, without copying the large vectors. Reproduction writes the full arrays only in the work directory and checks their hashes against `evidence/depth{2,16}/intermediates.json`. Every preserved deterministic artifact in `evidence/artifact-manifest.json` is checked too. Control outcomes are compared by name and result; machine-dependent error text and elapsed times are not equality vectors. Original and controlled prover hashes, verifier hash, CLI hash and the exact two-line diff are enforced by `scripts/prepare_reference.py`; `npm ci` enforces the locked dependency graph.
