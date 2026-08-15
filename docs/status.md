# Current Status

> **zkc v0 · research snapshot · last verified 2026-08-14**

zkc can describe and identify proof protocols, derive executable endpoints,
run selected prover and verifier paths, derive selected soundness and
completeness judgments, and apply a checked protocol optimization. The table
below reports tested examples in this repository, not compatibility with every
implementation of a protocol family.

## Protocol coverage

`●` exercised compiler path · `◐` limited to a bounded shape, stage, or profile
· `—` no callable path

- **Describe** — represent the protocol structure.
- **Check and identify** — validate the structure and assign a content identity.
- **Verifier path** — generate and run the verifier side. A cell is filled only when
  a test executes the generated verifier; generating an endpoint and
  discarding it is not this column.
- **Prover path** — generate and run the prover side.
- **Soundness** — derive a conditional adversarial-security judgment.
- **Completeness** — derive an honest-prover acceptance judgment.
- **Checked optimization** — apply and verify a protocol transformation.

| Protocol or component | Describe | Check and identify | Verifier path | Prover path | Soundness | Completeness | Checked optimization |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| Schnorr | ● | ● | ● | ● | ● | ● | — |
| DLEQ / OR-Sigma | ● | ● | ● | — | — | — | — |
| Sumcheck | ● | ● | ● | — | ● | — | — |
| GKR | ◐ | ◐ | — | — | ◐ | — | — |
| KZG openings / same-point batching | ● | ● | ● | — | ◐ | — | ● |
| FRI | ◐ | ◐ | ◐ | ◐ | ◐ | — | — |
| R1CS → Sumcheck | ◐ | ◐ | — | — | ◐ | — | — |

Profile scope: Schnorr refers to the included native profile; GKR to the
width-two, depth-three fixture; FRI to the parameterized generator and pinned
Plonky3 fixture; and R1CS → Sumcheck treats the relation artifact as opaque.
Soundness cells denote conditional judgments under declared assumptions. They
are distinct from execution evidence and formal proof.

Where the evidence is. Every cell above is backed by tests you can run and
read; this table says which, so a claim can be checked rather than taken.

| Cell | The test that fills it |
|---|---|
| Schnorr, all columns | [`test/Encoding/schnorr.mlir`](../test/Encoding/schnorr.mlir), [`test/Encoding/routed-schnorr.mlir`](../test/Encoding/routed-schnorr.mlir), [`test/Oir/schnorr-exec.test`](../test/Oir/schnorr-exec.test), [`test/Oir/prover-round-trip.test`](../test/Oir/prover-round-trip.test), [`test/Soundness/soundness-rule-bodies.mlir`](../test/Soundness/soundness-rule-bodies.mlir), [`test/Soundness/completeness-beside-a-run.test`](../test/Soundness/completeness-beside-a-run.test), [`test/Emit/emit-schnorr.test`](../test/Emit/emit-schnorr.test), [`test/Emit/emit-schnorr-prover.test`](../test/Emit/emit-schnorr-prover.test) |
| DLEQ / OR-Sigma | [`test/Encoding/chaum-pedersen.mlir`](../test/Encoding/chaum-pedersen.mlir), [`test/Encoding/or-sigma.mlir`](../test/Encoding/or-sigma.mlir), [`test/Oir/chaum-pedersen-exec.test`](../test/Oir/chaum-pedersen-exec.test), [`test/Oir/or-sigma-exec.test`](../test/Oir/or-sigma-exec.test), [`test/Emit/emit-sigma-family.test`](../test/Emit/emit-sigma-family.test) |
| Sumcheck | [`test/Encoding/sumcheck-fs.mlir`](../test/Encoding/sumcheck-fs.mlir), [`test/Oir/sumcheck-exec.test`](../test/Oir/sumcheck-exec.test), [`test/Soundness/derive-witness.test`](../test/Soundness/derive-witness.test), [`test/Emit/emit-sigma-family.test`](../test/Emit/emit-sigma-family.test) |
| GKR | [`test/Evidence/gkr-width2-depth3-parity.test`](../test/Evidence/gkr-width2-depth3-parity.test), [`test/Evidence/gkr-width2-stress.test`](../test/Evidence/gkr-width2-stress.test) |
| KZG openings / batching | [`test/Encoding/kzg-before.mlir`](../test/Encoding/kzg-before.mlir), [`test/Transforms/pir-batch-open.mlir`](../test/Transforms/pir-batch-open.mlir), [`test/Compiler/kzg-batch-core.mlir`](../test/Compiler/kzg-batch-core.mlir), [`test/Soundness/soundness-kzg-preservation.mlir`](../test/Soundness/soundness-kzg-preservation.mlir), [`test/Emit/emit-kzg-batching.test`](../test/Emit/emit-kzg-batching.test) |
| FRI | [`test/Family/fri-family.test`](../test/Family/fri-family.test), [`test/Oir/plonky3-fri-exec.test`](../test/Oir/plonky3-fri-exec.test), [`test/Evidence/plonky3-replay.test`](../test/Evidence/plonky3-replay.test), [`test/Soundness/grinding-over-fri.test`](../test/Soundness/grinding-over-fri.test), [`test/Emit/emit-plonky3-fri.test`](../test/Emit/emit-plonky3-fri.test), [`test/Emit/emit-plonky3-real-fill.test`](../test/Emit/emit-plonky3-real-fill.test) |
| R1CS → Sumcheck | [`test/Soundness/r1cs-entry.test`](../test/Soundness/r1cs-entry.test) |

A dash means no test executes that half. It is not a statement that the path
is impossible — GKR and R1CS project — only that nothing here runs the
result, so the column is not filled. The KZG verifier cells are filled by
emitted standalone crates: no in-process profile executes the pairing
checks, and the emitted crates' scope is their committed vectors under the
named test binding.

## Architecture progress

Each row has one status. **Implemented** means complete for the current stated
scope, not that the full target architecture is finished. The architecture and
specification intentionally include north-star contracts beyond this matrix.

| Architecture area | Implemented | Partial | Not built | Exercised scope |
|---|:---:|:---:|:---:|---|
| Protocol authoring and import |  | ● |  | Low-level PIR authoring and parameterized FRI family generation. |
| Relation interface |  | ● |  | Opaque relation identities and the `r1cs` anchor profile. |
| PIR sealing |  | ● |  | One seal engine owns structural, claim-flow, transcript, route, cited-vocabulary, and identity checks. |
| PIR canonical identity | ● |  |  | PIR content-derived identity. |
| Persisted PIR artifact lifecycle | ● |  |  | the canonical encoding decode, stored-identity validation, registry-backed admission against exact cited authority, and immutable in-process reuse. |
| Protocol policy |  | ● |  | Exact permitted-sink enforcement. |
| Static protocol linking |  | ● |  | Open-PIR splicing under one environment, with face-local namespaces and current construction routes preserved. |
| Soundness analysis |  | ● |  | Selected conditional, notion-indexed derivations from admitted PIR. |
| Completeness analysis |  | ● |  | Separate judgment track exercised by the included Schnorr path. |
| Checked optimization and selection |  | ● |  | In-process checked-search library exercised by same-point KZG batching over admitted PIR. |
| Verifier and prover generation |  | ● |  | Verifier OIR and derived prover-skeleton OIR; standalone Rust crate emission for either endpoint from the persisted artifact under an explicit supplier binding (`emit/`), with the emitted pair exercised against each other. |
| Endpoint execution |  | ● |  | Selected built-in verifier and prover profiles; a hole contract's static and semantic parameter bindings are re-admitted from the endpoint alone and handed to the supplier, which is given identities rather than the material they name. |
| Witness interface |  | ● |  | Typed opaque scalar handles for selected prover operations. |
| Formalization evidence |  | ● |  | Rule annotations and pinned declaration/axiom-profile drift checks. |
| Execution and conformance evidence |  | ● |  | C++/Python parity boundaries and a pinned Plonky3 replay. |
| Evidence admission policy |  |  | ● | — |
| Wider emission targets and deployment |  |  | ● | — |
| Recursion and zkVM composition |  |  | ● | — |
| Zero-knowledge analysis |  |  | ● | — |

## Read next

[Project Overview](overview.md) explains the idea, [Architecture](architecture.md)
describes the target system, [Roadmap](roadmap.md) describes target layers and
development order, and the [Specification](spec/overview.md) defines the exact
semantics.
