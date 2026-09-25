# Authored oracle protocols

These are complete accepted `.pir` sources, including generic local algorithms,
public interaction loops and separate construction descriptors.

- `air-permutation.pir`: two original finite AIRs, challenged product auxiliaries,
  quotient/OOD checks, opening batching, fresh randomized degree correction and
  binary FRI; N=8, blowup=4, queries=3.
- `affine-tables.pir`: challenged affine-table consistency at sampled coordinates,
  with authenticated rows and no polynomial/FRI operations.

Both use Plonky3 arithmetic and shape-bound Keccak Merkle kernels. They are
nonhiding experimental arguments without a claimed security-bit estimate.
There is no complete-STARK kernel behind these sources. The public loop counts
are specialized literals, rather than unchecked runtime profile parameters. The
fresh `degree_mix` draw follows the opening batch and precedes the first FRI
root.

To inspect either source directly:

```sh
build/compiler/zkc-compile protocol-source examples/protocols/air-oracle/air-permutation.pir
build/compiler/zkc-compile oracle-check examples/protocols/air-oracle/air-permutation.pir main --publication-before-queries --queries-before-responses
```
