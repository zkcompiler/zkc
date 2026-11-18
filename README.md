# zkc

zkc is a compiler for zero-knowledge proof protocols, written in Lean. The source language
describes roles, the values each role holds, the messages they exchange, and the checks
that decide acceptance. The Core gives these programs a meaning that Lean proofs can use.

## What builds today

The default build admits programs of named functions. Admission checks each definition against
earlier headers and proves its summary and loop bounds on valid inputs satisfying its requirements.
A checked transformation preserves the function's behavior under those requirements. For a
protocol supplied as a typed Core term, projection relates each role's process to its part in
the protocol. Protocol definitions in named programs still await admission.

For the working `.zkc` frontend, `zkc-check`, scheme construction and the Schnorr and Sumcheck
formal examples, use [the previous Lean compiler at `10ed903fc`](https://github.com/zkcompiler/zkc/tree/10ed903fc22d3f20b22ff2d1bbf607a740ef0718).
Those consumers await migration to the rebuilt Core. The [status](docs/status.md) records
which paths the current build exercises.

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
over the group G1 of BLS12-381. The declaration selects Fiat–Shamir with the suite
`Merlin3Bls12381` and the canonical proof layout.

```zkc
scheme Proof = Schnorr<G1>:
    construction derived(Merlin3Bls12381)
```

## Build and test

Both packages pin Lean 4.36.0. The [toolchain guide](docs/lean-toolchain.md) describes the audit.

The Lean toolchain is named in `lean/compiler/lean-toolchain` and installed by
[elan](https://github.com/leanprover/elan). With `elan`, [just](https://github.com/casey/just)
and `python3`, from the root of the repository:

```sh
just build   # build the active compiler targets
just test    # build, test and audit the active targets
just check   # check the public tree, the documents and the generated Unicode tables
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
