# zkc

zkc is a compiler for zero-knowledge proof protocols. A protocol is written in the zkc source
language with its roles, the values each role holds, the messages they exchange, the challenges
they draw and the checks that decide acceptance. zkc checks the program, projects it to one
program per role and constructs a non-interactive proof scheme from it.

zkc is written in Lean. The definitions that the compiler runs are the definitions that its
theorems are about: the core language has its meaning in Lean, the theorems of admission state
what an admitted program never does, and a formal package proves properties of compiled programs
over that meaning.

## Repository

| Path | Content |
|---|---|
| [`language/`](language/README.md) | the reference of the source language and its conformance tests |
| [`libraries/`](libraries/) | the library of the source language, in source |
| [`examples/`](examples/) | worked programs |
| [`lean/compiler/`](lean/compiler/README.md) | the compiler, one Lake package: the core (`Zkc.Core`), the frontend (`Zkc.Frontend`), their tests and tools |
| [`lean/formal/`](lean/formal/README.md) | a second Lake package: statements and proofs over the meaning of the core |
| [`docs/`](docs/README.md) | the status, the development guide and the specification of the core language |
| [`scripts/`](scripts/) | the document checker |

## What it does now

- The frontend reads `.zkc` source of the frozen layer of the language, and the scheme
  declarations that derive a proof by Fiat–Shamir, and emits programs of the core language.
- The core elaborates and admits these programs. Admission checks their types, checks facts so
  that an admitted program never stops `undefined`, and checks the copies of a value that
  several roles hold.
- The core projects a protocol to one program per role, constructs a non-interactive scheme by
  the Fiat–Shamir and serialize steps, and runs role programs with a total executor.
- The formal package states and proves properties over the meaning of the core. It has two
  worked results: the completeness of the Schnorr scheme of
  [`examples/schnorr_example.zkc`](examples/schnorr_example.zkc), and an invariant of ten rounds
  of Sumcheck (when the claims are the sum of the table, the verifier's ten checks pass). Neither
  is a statement of soundness.

zkc does not currently run role programs natively, target WASM or the EVM, or compile the forms
of the language beyond the frozen layer, such as oracles and commitments, STARK and constraint
systems. These are being rebuilt on this structure. The [status](docs/status.md) lists what is
supported. The earlier implementation, which had some of these, is at the tag
`old-route-2026-11-14`.

## A protocol in zkc

The Schnorr protocol of [`examples/schnorr.zkc`](examples/schnorr.zkc) proves knowledge of a
scalar whose multiple of `base` is `point`. Both roles hold `base` and `point`; only the prover
`P` holds `scalar`. The prover samples a secret nonce and sends a commitment, the verifier `V`
draws a public challenge, the prover sends a response, and the verifier's guard decides
acceptance:

```zkc
pub protocol Schnorr<G: PrimeOrderGroup> roles(P, V)(
    base: G @(P, V),
    point: G @(P, V),
    scalar: G::Scalar @P
):
    nonce @P <- sample G::Scalar
    commitment <- send base * nonce to V
    challenge <- draw G::Scalar from V to P
    response <- send nonce + challenge * scalar to V
    guard @V base * response == commitment + point * challenge
```

[`examples/schnorr_example.zkc`](examples/schnorr_example.zkc) declares a non-interactive scheme
over the group G1 of BLS12-381. zkc derives its prover and verifier by the Fiat–Shamir step with
the suite `Merlin3Bls12381` and the canonical layout of the proof:

```zkc
scheme Proof = Schnorr<G1>:
    construction derived(Merlin3Bls12381)
```

## Build and test

The Lean toolchain is named in `lean/compiler/lean-toolchain` and installed by
[elan](https://github.com/leanprover/elan). With `elan`, [just](https://github.com/casey/just)
and `python3`, from the root of the repository:

```sh
just build   # build the compiler package, then the formal package
just test    # build and test both packages, then audit them
just check   # check the public tree and the documents
```

The [development guide](docs/development.md) describes the layout, every command and how to run
part of the tests.

## Read more

- [The source language](language/README.md): its reference, its libraries and its conformance
  tests.
- [The documentation index](docs/README.md): the status, the development guide and the
  specification of the core language.
- [The contribution guide](.github/CONTRIBUTING.md).

## License

Licensed under the [Apache License, Version 2.0](LICENSE.md).
