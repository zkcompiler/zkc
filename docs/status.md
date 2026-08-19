# Current Status

> **zkc v0 · research snapshot · last verified 2026-08-19**

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
- **Seal policy** — which sinks the exercised artifact's policy permits.
  A *closed proof* routes every claim to a discharge, so the artifact
  states its conclusion outright. *Analysis only* additionally permits
  residual, export, and assumption routes, so some claim the protocol
  raises is carried rather than closed — the soundness cell then prices
  the claims that were, and the artifact is not a proof of the whole
  statement. The distinction is invisible in the marks above and
  changes what a filled cell means, so it is a column.

| Protocol or component | Describe | Check and identify | Verifier path | Prover path | Soundness | Completeness | Checked optimization | Seal policy |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|---|
| Schnorr | ● | ● | ● | ● | ● | ● | — | closed proof |
| DLEQ / OR-Sigma | ● | ● | ● | — | — | — | — | analysis only |
| Sumcheck | ● | ● | ● | — | ● | — | — | analysis only |
| GKR | ◐ | ◐ | — | — | ◐ | — | — | analysis only |
| KZG openings / same-point batching | ● | ● | ● | — | ◐ | — | ● | closed proof |
| FRI | ◐ | ◐ | ◐ | ◐ | ◐ | — | — | analysis only |
| R1CS → Sumcheck | ◐ | ◐ | — | — | ◐ | — | — | analysis only |

Profile scope: Schnorr refers to the included native profile; GKR to the
width-two, depth-three fixture; FRI to the parameterized generator and pinned
Plonky3 fixture — commit phase, grinding, and the query phase: sampled
indices, opened rows and authentication paths on the wire unabsorbed, the
input-layer Merkle multi-opening and the fold-consistency checks executed
natively and in emitted crates, query answering derived on the prover from
the retained trees, the emitted wire graded by the pinned upstream verifier
through the decoding judge, a deterministic scale gate at fold depth 13, and
recorded generation-versus-upstream benchmark evidence
(evaluation/fri-bench); the sealed judgment states the query binding through
counted and positional attachments, and soundness prices both a conjectured
mode (the corrected random-words row) and a proven above-Johnson mode (the
threshold-halving row, its unvetted standing carried by the obligations
ledger). The family's rate and stopping shape are instance parameters —
log_blowup and log_final_poly_len under the shape equation query_log2 = k +
log_blowup + log_final_poly_len — executed end to end at rate 1/4 and at a
two-coefficient final polynomial (both graded by the pinned upstream
verifier) and priced at rate 1/4 through every proximity row, with the
value-faithful instance's pricing refusal pinning the ALI/DEEP composition
boundary. The analysis-only template's judgment now compiles: over the toy
configuration the whole chain runs to a Fiat-Shamir bound, and the artifact
judgment refuses to call that bound the artifact's when a round the
derivation never covered — the grinding round, when the compilation skips it
— is missing from the sum. R1CS → Sumcheck treats the relation artifact as
opaque.
Soundness cells denote conditional judgments under declared assumptions. They
are distinct from execution evidence and formal proof.

Where the evidence is. Every cell above is backed by tests you can run and
read; this table says which, so a claim can be checked rather than taken.

| Cell | The test that fills it |
|---|---|
| Schnorr, all columns | [`test/Encoding/schnorr.mlir`](../test/Encoding/schnorr.mlir), [`test/Encoding/routed-schnorr.mlir`](../test/Encoding/routed-schnorr.mlir), [`test/Encoding/grind-schnorr.mlir`](../test/Encoding/grind-schnorr.mlir), [`test/Oir/schnorr-exec.test`](../test/Oir/schnorr-exec.test), [`test/Oir/prover-round-trip.test`](../test/Oir/prover-round-trip.test), [`test/Oir/grind-round-trip.test`](../test/Oir/grind-round-trip.test), [`test/Soundness/soundness-rule-bodies.mlir`](../test/Soundness/soundness-rule-bodies.mlir), [`test/Soundness/completeness-beside-a-run.test`](../test/Soundness/completeness-beside-a-run.test), [`test/Emit/emit-schnorr.test`](../test/Emit/emit-schnorr.test), [`test/Emit/emit-schnorr-prover.test`](../test/Emit/emit-schnorr-prover.test), [`test/Emit/emit-grind-prover.test`](../test/Emit/emit-grind-prover.test) |
| DLEQ / OR-Sigma | [`test/Encoding/chaum-pedersen.mlir`](../test/Encoding/chaum-pedersen.mlir), [`test/Encoding/or-sigma.mlir`](../test/Encoding/or-sigma.mlir), [`test/Oir/chaum-pedersen-exec.test`](../test/Oir/chaum-pedersen-exec.test), [`test/Oir/or-sigma-exec.test`](../test/Oir/or-sigma-exec.test), [`test/Emit/emit-sigma-family.test`](../test/Emit/emit-sigma-family.test) |
| Sumcheck | [`test/Encoding/sumcheck-fs.mlir`](../test/Encoding/sumcheck-fs.mlir), [`test/Soundness/fs-counted-squeeze.test`](../test/Soundness/fs-counted-squeeze.test), [`test/Oir/sumcheck-exec.test`](../test/Oir/sumcheck-exec.test), [`test/Soundness/derive-witness.test`](../test/Soundness/derive-witness.test), [`test/Emit/emit-sigma-family.test`](../test/Emit/emit-sigma-family.test) |
| GKR | [`test/Evidence/gkr-width2-depth3-parity.test`](../test/Evidence/gkr-width2-depth3-parity.test), [`test/Evidence/gkr-width2-stress.test`](../test/Evidence/gkr-width2-stress.test) |
| KZG openings / batching | [`test/Encoding/kzg-before.mlir`](../test/Encoding/kzg-before.mlir), [`test/Transforms/pir-batch-open.mlir`](../test/Transforms/pir-batch-open.mlir), [`test/Compiler/kzg-batch-core.mlir`](../test/Compiler/kzg-batch-core.mlir), [`test/Soundness/soundness-kzg-preservation.mlir`](../test/Soundness/soundness-kzg-preservation.mlir), [`test/Emit/emit-kzg-batching.test`](../test/Emit/emit-kzg-batching.test) |
| FRI | [`test/Family/fri-family.test`](../test/Family/fri-family.test), [`test/Soundness/fs-duplex-chain.test`](../test/Soundness/fs-duplex-chain.test), [`test/Family/relation-absorbing-variant.test`](../test/Family/relation-absorbing-variant.test), [`test/Oir/plonky3-fri-exec.test`](../test/Oir/plonky3-fri-exec.test), [`test/Evidence/plonky3-replay.test`](../test/Evidence/plonky3-replay.test), [`test/Soundness/grinding-over-fri.test`](../test/Soundness/grinding-over-fri.test), [`test/Soundness/fri-pricing-modes.test`](../test/Soundness/fri-pricing-modes.test), [`test/Emit/emit-plonky3-fri.test`](../test/Emit/emit-plonky3-fri.test), [`test/Emit/emit-plonky3-real-fill.test`](../test/Emit/emit-plonky3-real-fill.test), [`test/Emit/emit-fri-prover.test`](../test/Emit/emit-fri-prover.test), [`test/Emit/emit-fri-scale.test`](../test/Emit/emit-fri-scale.test), [`test/Emit/emit-fri-shapes.test`](../test/Emit/emit-fri-shapes.test), [`test/Soundness/fri-quarter-pricing.test`](../test/Soundness/fri-quarter-pricing.test), [`test/Registry/family-vocabulary-parity.test`](../test/Registry/family-vocabulary-parity.test), [`test/Registry/check-attachment-vector.test`](../test/Registry/check-attachment-vector.test), [`test/SemanticClosure/check-attachment-binding.test`](../test/SemanticClosure/check-attachment-binding.test) |
| R1CS → Sumcheck | [`test/Soundness/r1cs-entry.test`](../test/Soundness/r1cs-entry.test), [`test/Relation/relation-contract.test`](../test/Relation/relation-contract.test) |

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
| Protocol authoring and import |  | ● |  | Low-level PIR authoring, parameterized FRI family generation, and authored instance content: a description may state seal-stage bindings emitted at the head of the spine, whose value, when one cites a claim anchor, is that anchor's transcript projection. The exercised variant binds its relation's identity into its own transcript — a departure the pinned upstream verifier cannot grade — and derives a byte-identical conclusion to the instance it departs from. |
| Relation interface |  | ● |  | Opaque relation identities, the `r1cs` anchor profile, and the relation contract: a post-seal document stating a relation's reading format, anchor partition, instance encoding, witness ports, and statement correspondence, judged against a sealed artifact with the computed, cross-checked, and asserted parts reported apart. The `r1cs-bin-v1` header reader cross-checks a contract's declared arity, field, private count, and constraint count against supplied bytes; because no anchor-preimage rule exists, that agreement is between two things the same party states, and the judgment reports it as consistency rather than as a fact about the relation the anchors name. A relation anchor whose transcript projection a seal-stage binding carries is reported as transcript-carried rather than structural. |
| PIR sealing |  | ● |  | One seal engine owns structural, claim-flow, transcript, route, cited-vocabulary, and identity checks. |
| PIR canonical identity | ● |  |  | PIR content-derived identity. |
| Persisted PIR artifact lifecycle | ● |  |  | the canonical encoding decode, stored-identity validation, registry-backed admission against exact cited authority, and immutable in-process reuse. |
| Protocol policy |  | ● |  | Exact permitted-sink enforcement. |
| Static protocol linking |  | ● |  | Open-PIR splicing under one environment, with face-local namespaces and current construction routes preserved. |
| Soundness analysis |  | ● |  | Selected conditional, notion-indexed derivations from admitted PIR, including the Fiat-Shamir compilation of a family artifact end to end: the interactive rows, the grinding row that scales one of them, state restoration, and the duplex hop, whose bound carries each squeeze's exact sampling bias and the collision game the transcript's relation anchors scale. |
| Completeness analysis |  | ● |  | Separate judgment track exercised by the included Schnorr path. |
| Checked optimization and selection |  | ● |  | In-process checked-search library exercised by same-point KZG batching over admitted PIR. |
| Verifier and prover generation |  | ● |  | Verifier OIR and derived prover-skeleton OIR; standalone Rust crate emission for either endpoint from the persisted artifact under an explicit supplier binding (`emit/`), with the emitted pair exercised against each other. |
| Endpoint execution |  | ● |  | Selected built-in verifier and prover profiles; a hole contract's static and semantic parameter bindings are re-admitted from the endpoint alone and handed to the supplier, which is given identities rather than the material they name. The `pow_search` transcript peek executes as a supplier-run search over a trial the executor builds on a cloned sponge, never the live state. |
| Witness interface |  | ● |  | Typed opaque scalar handles for selected prover operations. |
| Formalization evidence |  | ● |  | Rule annotations and pinned declaration/axiom-profile drift checks. |
| Execution and conformance evidence |  | ● |  | C++/Python parity boundaries and a pinned Plonky3 replay. |
| Evidence admission policy |  |  | ● | — |
| Wider emission targets and deployment |  |  | ● | — |
| Recursion and zkVM composition |  | ● |  | The bounded artifact-verification carrier form only: eight of the eleven facts `endpoints.md` §3.1 lists are sealed and canonically encoded, with cross-implementation byte parity on the row and the artifact identity, and both endpoints refuse it at projection. The covered parent claim id is carried by the parent route instead, because a claim is linear and its one consumer is the sink that routes it; explicit child assumptions and source-event provenance and failure behaviour are not bound. No child artifact is verified and nothing composes; the carrier fixes the shape a later projection, execution, and conformance surface must preserve. |
| Zero-knowledge analysis |  |  | ● | — |

## Read next

[Project Overview](overview.md) explains the idea, [Architecture](architecture.md)
describes the target system, [Roadmap](roadmap.md) describes target layers and
development order, and the [Specification](spec/overview.md) defines the exact
semantics.
