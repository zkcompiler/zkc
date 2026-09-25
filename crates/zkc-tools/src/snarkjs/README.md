# Bounded snarkjs import

`zkc_tools::snarkjs` independently decodes the snarkjs 0.7.5 Groth16 BN254 binary
formats: zkey version 1 and wtns version 2. It uses arkworks 0.6.0 checked field
and point arithmetic. The sources inspected for interoperability are
`snarkjs/src/{zkey_utils,groth16_prove,wtns_utils,curves}.js`,
`@iden3/binfileutils/src/binfileutils.js`, and ffjavascript 0.3.1 field conventions.
The code is an independent parser of those binary formats; no JavaScript prover
runs during import or kernel execution.

`read_zkey`/`decode_zkey` return `PreparedKey`. `read_wtns`/`decode_wtns` return
`Witness`. Both take explicit `Limits` and a backend `Policy`. Header moduli and
widths, section uniqueness/coverage/lengths, point curve/subgroup validity,
canonical residues, coefficient indices, variable counts, and radix-two domain
sizes are checked. Resource limits precede attacker-directed allocations. Missing,
unknown or duplicate sections, unsupported versions and trailing data are refused.
Optional section 10 is bounded opaque provenance. Parsing does not establish
ceremony validity, relation satisfaction, or correspondence between the imported
key and any separately supplied relation.

Point coordinates use Montgomery R = 2^256 modulo the BN254 base field. Section 4
coefficients use R² modulo Fr. Witnesses are canonical Fr integers. G2 coordinate
order is x.c0, x.c1, y.c0, y.c1. All-zero affine records represent infinity.
Conversion does not reduce out-of-range residues.

`PreparedKey::values()` returns ordinary typed backend values named `alpha1`,
`beta1`, `beta2`, `gamma2`, `delta1`, `delta2`, `ic`, `a_query`, `b1_query`,
`b2_query`, `l_query`, `h_query`, `qap_a`, `qap_b`, `domain_size`, `n_public`,
`n_vars`, `domain_root`, and `coset_shift`. A/B coefficient records become canonical
sparse COO matrices with dimensions domain_size by n_vars; duplicate entries are
summed and zero sums removed. `assignment(&Witness)` checks count and returns the
assignment vector; the witness decoder checks its leading constant one.

H query points are retained in snarkjs order. For admitted n < 2^28, the exposed
shift is the generator-5 root of order 2n. The H MSM's primitive scalar inputs are
the odd-coset numerator evaluations A*B-C, **without division by the vanishing
polynomial**. The imported H basis incorporates the corresponding factor and
transform. The authored PIR algorithm owns interpolation, evaluation, multiplication,
subtraction, MSM and proof assembly. No complete Groth16 backend operation exists.

The fixed default import ceilings are 64 MiB per file, 32768 variables/domain
points, 1048576 coefficients and 128 MiB conservative decoded/scratch storage.
Hard ceilings further cap caller overrides. Backend policy remains independent;
a host using 8192-point fixtures must explicitly raise `Policy::max_groups` above
its default 4096. There is no identity inferred from public parameter names.
Role admission and public/private custody remain the host's responsibility.

The CLI is:

```
cargo run -p zkc-tools --bin snarkjs-import -- KEY.zkey WITNESS.wtns OUTPUT.json
```

Its inspection output is `["zkc.snarkjs.prepared/1", [[name, physical-type, zkcv-hex], ...]]`,
including the assignment. This is not an execution input format: the maintained
Groth16 host consumes typed `PreparedKey` and `Witness` directly. The inspection
CLI explicitly selects a 32768 group policy.
Use the Rust API to populate role-local `InputBindings` without serializing
private assignments.

Synthetic refusal controls run in the ordinary `snarkjs_import` test target.
The genuine-file comparison is explicit and opt-in:

```
ZKC_GROTH16_FIXTURE=/tmp/zkc-groth16-fixture cargo test -p zkc-tools --release --test snarkjs_import -- --ignored
```

It checks both depth-2 and depth-16 fixtures against snarkjs and independent
canonical BigInt reference vectors: assignments, roots, shifts, header points,
IC, complete QAP evaluation vectors, all A/B1/B2/L/H query MSMs, controlled proof
coordinates and the pairing equation. This is fixture-scoped interoperability
evidence. The ordinary test suite does not silently require external files.
