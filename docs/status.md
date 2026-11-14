# Status

What this repository implements. The [reference of the source language](../language/README.md)
defines more than is implemented: the language is designed in layers, and the inner layer is
frozen as the baseline of the implementation.

| Area | Supported |
|---|---|
| Source language | `.zkc` source of the frozen layer, and the scheme declarations that derive a proof by Fiat–Shamir with the canonical layout. A root that uses a form of a later layer waits, with the form it waits for |
| Admission | elaboration of a package of the core language, its types, the check of facts (an admitted program never stops `undefined`) and the check of copies |
| Construction and projection | the Fiat–Shamir and serialize steps that construct a non-interactive scheme; projection of a protocol to one program per role |
| Execution | role programs run by the total executor of the core, in Lean. Rows of G2, Gt, the pairing and the hashes other than SHA-256 have no arithmetic in it and do not run |
| Proofs | statements and proofs over the meaning of the core: the completeness of the Schnorr scheme of `examples/schnorr_example.zkc` in the model that runs, under named hypotheses about the curve; an invariant of ten rounds of `Sumcheck<Fr, 10>` in the model of any arithmetic (when the claims are the sum of the table, the verifier's ten checks pass). No statement of soundness, knowledge or zero knowledge |
| Native execution | not supported |
| WASM and EVM targets | not supported |
| Oracles and commitments, STARK, constraint systems and the other forms beyond the frozen layer | not supported; being rebuilt on this structure |

The earlier implementation, a C++ compiler with a Rust runtime, is at the tag
`old-route-2026-11-14`.
