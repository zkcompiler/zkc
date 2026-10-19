# Choose an external construction

The [protocol](protocol.zkc) calls the ordinary `schnorr::Schnorr` library and
retains prover nonce randomness. The [Entry](main.zkc) selects the reusable
Spongefish SHAKE128 provider and an explicit 48-byte point / 32-byte scalar
record format. No Schnorr algorithm or transcript kernel is duplicated.

```sh
cd examples/projects/schnorr/spongefish
zkc check
zkc prove --allow-authored --output=schnorr.proof
zkc verify --allow-authored --proof=schnorr.proof
```

Inputs use the sole Entry's default directory. This authored construction binds
its tag, session, base and public point. It intentionally emits no zkc header;
`--allow-authored` acknowledges that application-owned binding choice. Decoding
precedes observation, the final response is absorbed, and the stream checks EOF.
The fields and codecs are specifically BLS12-381 G1/Fr with Spongefish 0.7.4's
SHAKE128 conventions. The example witness is public test data.

The [explicit transcript client](../../../../common/tests/fixtures/projects/spongefish-schnorr/README.md) remains an
independent byte-level reference. Tests compare both paths to upstream vectors
and exercise malformed encodings. Agreement is not a security proof or a claim
of compatibility with every Spongefish configuration.

## Executable quick start

Run these literal commands from this project directory with `zkc` and
`zkc-compile` on `PATH` (Python 3 for generated inputs). The test suite runs
this block in a separate consumer tree using only declared package dependencies.

```sh zkc-example
zkc check
zkc prove Proof --allow-authored
zkc verify Proof --allow-authored
```

Inputs: inputs/example.Proof/{public,witness}.json.

Profile: BLS12-381 G1/Fr; SHAKE128, 48-byte points, 32-byte scalars and an 80-byte proof.

Expected negative control: A truncated encoding or a changed session refuses verification.

Generated packages, proofs and result documents are written under `build/`
inside this project. Existing input maps remain source inputs.
