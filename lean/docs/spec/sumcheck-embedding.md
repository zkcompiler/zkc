# Sumcheck with an embedded base table

`Zkc.Polynomial.Multilinear.Embedding` transports the existing ordered Boolean
table semantics along an explicit ring homomorphism `e : B →+* E`. It proves
that Boolean summation and evaluation at embedded base points commute with
`e`, and that first-coordinate and ordered-prefix restriction commute at
embedded base points. For arbitrary extension points, the operation is instead
to embed every table entry and then restrict in `E`. The list decoding and
residual evaluation laws identify this operation with the existing
`fixPrefix` and `extension`; they never pretend that an extension challenge is
a base-field element.

`ZkcSecurity.Families.Sumcheck.EmbeddingPrefix.State` retains the original
`List B`, an ordered `List E` challenge prefix, the current `E` scalar and an
arbitrary caller frame. At remaining dimension `n`, its shape is exactly
`original.length = 2^(n + point.length)`. Its reference entries are
`restrictPrefixValues (original.map e) point`. Appending every extension
challenge commutes with restriction for every received endpoint pair,
including false claims. The representation has no truth-based admission
condition. The terminal sum is evaluation of the embedded original table at
the actual prefix.

These laws are independent of any native source installation. The former generated
KoalaBear Sumcheck endpoint is retired. A future client must associate its actual
base/extension operations, representation and sampling law before applying these
mathematical results. See [support](../support.md).
