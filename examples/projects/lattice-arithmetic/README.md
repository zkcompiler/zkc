# Quotient-ring arithmetic

[main.zkc](main.zkc) uses the checked quotient-ring view and
[lattice library](../../../libraries/relations/lattice/README.md) in
`(Z/17Z)[X]/(X^4+1)`. These small parameters illustrate arithmetic only.

The canonical response `[16,0,1,0]` has centered coefficients `[-1,0,1,0]`.
Multiplication by the public key yields `[13,11,15,15]`; subtracting it from
the challenge yields `[1,1,1,1]`. The paired squared norm is exactly 6.
The example returns that product and `accepted=true`. A bound of 5 returns
`accepted=false` after successful execution.

## Executable quick start

Run from this directory with built `zkc` and `zkc-compile` on `PATH`:

```sh zkc-example
zkc check
zkc run Arithmetic
```

Inputs: [arguments.json](inputs/example.Arithmetic/arguments.json).

Profile: canonical quotient-ring coefficients, modulus 17 and degree 4.

Expected negative control: lowering `bound` to 5 makes the result false;
a coefficient 17 or a missing coefficient fails view construction.

Results are written to `build/zkc/example.Arithmetic.results.json`. The
[contract](../../../docs/spec/domains/quotient-rings.md) defines representation
and failure behavior. This program performs no signature decoding, challenge
hashing, signing or proof generation.
