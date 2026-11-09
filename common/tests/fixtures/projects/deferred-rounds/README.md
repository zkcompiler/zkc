# Deferred rounds

A two-round Fiat–Shamir proof whose verifier's arithmetic is consumed only at
the end. The prover sends `a0 = w`, the verifier draws `r0`, the prover sends
`a1 = w · r0` and the verifier draws `r1`; the verifier accepts when
`a0 · r0 · r1 + x = a1 · r1 + x` for the public `x`. The honest prover is always
accepted. The protocol proves nothing about `x` and `w`: it exists to fix the
schedule of pure calculations.

The constructed validator computes `a0 · r0` where the source does, right after
the first draw. The compiler's calculation batching computes it, with every
other product, in one calculation call after the second draw, before the
comparison that consumes it. The program is therefore not the constructed
validator instruction for instruction, and the
The native scheduling fixture remains maintained. Its former generated Lean
byte correspondence is retired; see [formal support](../../../../../lean/docs/support.md).
