# Pinned Plonky3 replay slice

This crate is the current pinned Plonky3 backend-evidence harness. It targets
exactly Plonky3 revision
`3da346791c813433b201299afc3d10bf42f8a078`, which `Cargo.toml` names and
`Cargo.lock` resolves. It is not linked into the zkc compiler or checker and is
not a general Plonky3 backend.

## What the harness checks

- `trace` emits upstream BabyBear/Poseidon2 duplex observations, including the
  known-answer permutation vector and buffering, extension-sampling, and
  low-bit behavior used by zkc's native profile and Python twin.
- `capture` proves one non-hiding, Fibonacci-shaped AIR instance with the
  ordinary challenger, confirms that an observing challenger produces the
  same proof bytes, captures two identical verifier transcripts, and emits the
  checked-in fixture.
- `replay <fixture> [mutation]` reconstructs the exact pinned configuration and
  runs the upstream verifier from the fixture. The unmodified fixture is
  accepted and reproduces the captured transcript. Byte mutations are reported
  as postcard-decoding refusals; public-value and opened-value mutations reach
  and are refused by the upstream verifier; `swap-events` is explicitly a
  challenger-log experiment rather than a verifier run.
- `prove <canonical-prover-document.json> [corrupt-final-poly]` recomputes the
  OIR prover artifact identity before reading its semantics, matches its
  declared schedule to the recorded upstream challenger events, fills its
  routed holes through the pinned prover, and runs the pinned verifier. The lit
  suite separately feeds the assembled wire to zkc's native Plonky3 execution
  profile and checks acceptance and corruption refusal.

The checked-in fixtures are `fixtures/duplex_babybear.json` and
`fixtures/fib_babybear.json`. The latter's format,
`zkc.replay.fixture`, is a prototype rather than a supported public schema.
Proof bytes are postcard-encoded and are identified only together with the
encoding, pinned crate revision, and proof type parameters. The AIR is bound by
content address on the zkc side because this upstream verifier does not absorb
the AIR itself into the transcript.

## Pinned configuration

The exercised instance uses:

- the BabyBear base field and degree-four binomial extension field;
- the pinned default BabyBear Poseidon2 permutation, width 16 and rate 8;
- `DuplexChallenger`, Merkle-tree MMCS, radix-2 DIT DFT, and
  `TwoAdicFriPcs`;
- a non-hiding Fibonacci-shaped AIR of width 2, three public values, and trace
  height 8; and
- FRI parameters `log_blowup=1`, `log_final_poly_len=0`, `max_log_arity=1`,
  `num_queries=4`, zero commit proof-of-work bits, and eight query
  proof-of-work bits. These describe this fixture; the prove and grade
  binaries derive `log_blowup`, `log_final_poly_len`, the query count, and
  the grinding bits from each document's own schedule, so any shape the
  family seals runs against the pin.

The fixture records the source and dependency pins, construction identity, AIR
content address and shape, public values and degree bits, encoded proof, and
ordered primitive challenger log.

## Binding and transcript boundary

Replay reconstructs the pinned verifier configuration and call-side inputs,
including public values, degree bits, commitments, opened-value groups, FRI
opening proof, step arities, and proof-of-work witnesses. The upstream
transcript does not absorb the AIR program itself, so the fixture's AIR content
address is a structural zkc-side binding rather than a transcript-carried one.

The captured log contains primitive challenger events, not the logical OIR
schedule. Event order remains significant: an extension-field sample expands
to several primitive samples, output follows the challenger's native order,
and a new observation invalidates buffered output.

The prover experiment uses the value-faithful family variant. It recreates the
fresh upstream duplex state and absorb/sample order, binds fold arities in a
separate segment, and represents the opening value, final-polynomial
coefficient, and one-word grinding nonce as explicit proof slots. This is the
correspondence for this fixture, not a generic FRI lowering.

## Scope of the evidence

The harness supports claims only about this fixture, this configuration, and
this upstream revision: deterministic capture, upstream acceptance, exact
captured challenge-stream reproduction, the declared artifact-to-runner
correspondence, and the tested refusal cases. It does not establish universal
Plonky3 conformance, complete FRI source-to-PIR correspondence, correctness of
an AIR or relation compiler, protocol soundness, zero knowledge, production
schema stability, or security against untested mutations. A decode refusal is
not presented as a verifier-security result.

Run the individual binaries from this directory:

```sh
cargo run --locked --bin trace > /tmp/duplex_babybear.json
cargo run --locked --bin capture -- /tmp/fib_babybear.json
cargo run --locked --bin replay -- fixtures/fib_babybear.json
cargo run --locked --bin prove -- /path/to/canonical-prover-document.json
```

The cargo-driven checks are `test/Evidence/plonky3-replay.test` and
`test/Oir/prover-real-fill.test`. The value-faithful carrier and native duplex
paths are exercised by `test/Oir/plonky3-fri-value-faithful.mlir` and
`test/Oir/plonky3-duplex-replay.test`.
