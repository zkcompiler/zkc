# Lattice short-preimage arithmetic

`lattice::short_preimage<Q,N>(public_key, challenge, response, bound)` computes
`first = challenge - public_key * response` in `(Z/QZ)[X]/(X^N+1)` and returns
whether the sum of the two centered squared norms of `first` and `response`
is at most `bound`. All three inputs are checked
`zkc::quotient::Polynomial<Q,N>` values.

```text
let h = quotient::polynomial<12289,512>(public_key_coefficients);
let c = quotient::polynomial<12289,512>(challenge_coefficients);
let s = quotient::polynomial<12289,512>(response_residues);
let accepted = lattice::short_preimage(h, c, s, 34034726);
```

The [quotient-ring contract](../../../docs/spec/domains/quotient-rings.md)
defines canonical coefficients, ring identity, centered representatives and
integer norm semantics. To preserve a negative centered coefficient `-k`,
supply the canonical residue `Q-k`, with `1 <= k <= floor(Q/2)`. An integer
outside the centered interval cannot retain its original magnitude through
this residue view. The API does not accept signed-word encodings or silently
reduce arbitrary integers. Modulus and degree belong to the static
type. The bound is an explicit input selected by the enclosing construction.

This is the arithmetic predicate used by a short-preimage verifier. It is not
a Falcon signature verifier: the caller must separately own the public-key and
signature formats, signed-response range and encoding checks, message/salt
hashing to a challenge, parameter selection and authentication. Reduction to
residues would lose the magnitude of an arbitrary original integer. The
[Falcon specification, section 3.10](https://falcon-sign.info/falcon.pdf)
describes the full verification procedure; only its ring equation and integer
norm motivate this helper. No signing, Gaussian sampling, signature security,
ZK proof system or Fiat–Shamir composition is installed by this package.

[Native integration tests](../../../common/tests/kernels/test_quotient_rings.py)
exercise the 512-coefficient arithmetic path, exact norm thresholds, a modified
challenge, malformed lengths and noncanonical residues through the common
compiler and Host. Integer convolution supplies the independent arithmetic
reference. These are generated arithmetic controls, not signature test vectors.
The [design rationale](../../../docs/rationale/quotient-rings.md) records why
the package currently uses checked native operations instead of external NTT IR.
