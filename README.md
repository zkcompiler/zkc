# zkc

zkc is a compiler for zero-knowledge **proof protocols**. It makes participant
computation, interaction and protocol composition explicit so they can be
analyzed, transformed and executed using cryptographic libraries.

A relation describes what is being proved. A protocol describes how participants
compute, exchange messages, obtain challenges and check the proof. zkc authors
that protocol in `.zkc` and compiles it through mathematical MLIR to independently
executable participant programs.

The project is under active development. [Implementation status](docs/status.md)
records supported capabilities and their limits.

## A protocol in zkc

The [Schnorr library](examples/libraries/schnorr/lib.zkc) expresses its exchange
with explicit roles and random services:

```text
let nonce = nonces.draw();
let commitment = send P -> V(base * nonce);
let challenge = challenges.draw();
let received = send V -> P(challenge);
let response = send P -> V(nonce + received * scalar);
let accepted@V = base * response == commitment + point * challenge;
return (accepted = accepted);
```

Its [Entry](examples/projects/schnorr/main.zkc) selects public inputs, the
acceptance result and a Fiat–Shamir construction. The compiler derives participant
transcripts; the Rust Host executes independent prove/verify calls. The
[Sumcheck project](examples/projects/sumcheck/README.md) demonstrates bounded
repetition, vector kernels and an actual terminal evaluation.

## How it works

```text
.zkc Language → mathematical MLIR
                 protocol → participant → exec → physical
                                                       ↓
                                                 zkc.program/2
                                                       ↓
                                     shared Rust Runner + installed kernels
                                        Entry / proof / joint Hosts
```

Language checks explicit modules, types, capabilities, resources and selected
Entries. The compiler preserves mathematical structure through participant
projection, demand lowering and physical kernel selection. Hosts authenticate
packages, bind application inputs and setup authority, and manage execution and
publication. Direct MLIR clients enter the same pipeline.

The independent [Lean library](formal/README.md) supplies semantic models and
proofs. Those results concern their stated formal subjects; native pipeline
correspondence remains open. [Architecture](docs/architecture.md) explains the
owners, and [assurance](docs/assurance.md) distinguishes formal results, compiler
checks and bounded tests.

## Try it

The supported development environment is x86_64 Linux with Nix. Follow the
[setup guide](docs/development/README.md#set-up-the-development-checkout), then
run from the repository root:

```sh
nix develop
just setup
just demo
```

The demo builds the C++/Rust tools, compiles Schnorr with known-witness inputs,
produces a proof and verifies it in a separate process. It reports `Proof accepted`
and the output directory containing `proof.bin` and execution reports. The
witness is deliberately public; runtime randomness is fresh. See the
[walkthrough](docs/getting-started.md) for individual steps and authority binding.

## Explore

| Task | Start here |
|---|---|
| Write a protocol or library | [Language](docs/language/README.md), [example projects](examples/projects/README.md) |
| Develop the compiler or a backend | [Architecture](docs/architecture.md), [development](docs/development/README.md) |
| Study semantics and verification | [Model guides](docs/guides/README.md), [specification](docs/spec/README.md) |
| Assess support and future work | [Status](docs/status.md), [roadmap](docs/roadmap.md) |

The [documentation index](docs/README.md) maps the reference. Contributions follow
[the contribution guide](.github/CONTRIBUTING.md).

## License

Licensed under the [Apache License, Version 2.0](LICENSE.md).
