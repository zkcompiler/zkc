# Raw Spongefish Schnorr

This project uses the [source library](../../../../../libraries/constructions/spongefish/README.md)
to produce 80-byte proofs compatible with the pinned Spongefish 0.7.4 Schnorr
example, specialized to BLS12-381 G1 and SHAKE128. The nonce comes from the
prover's managed random service. Run from this directory with `zkc` installed:

```sh
zkc check
zkc prove --allow-authored --output=proof.bin
zkc verify --allow-authored --proof=proof.bin
```

Public inputs contain the upstream protocol tag, session, generator and public
point. The witness contains scalar 7. `RawBytes` emits no zkc framing; the
authored library owns statement binding, decoding and EOF checks.
`--allow-authored` acknowledges that responsibility. It is not a soundness
judgment. Independent reference tests are in
[test_source_transcript.py](../../../protocol/test_source_transcript.py).
