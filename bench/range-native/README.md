# Visible range reduction and recursive IPA

This benchmark crate measures independently authored native range-reduction and
recursive-IPA producers and validators over the pinned real Ristretto
implementation, against the released Bulletproofs 5.0.0 baseline. It is an
executable research prototype, not a replacement compiler and not a production
cryptographic library. Raw measurement records remain local; retained claims
follow the [measurement policy](../README.md#reading-and-recording-a-measurement).

## Exact research question

Can visible range-reduction and recursive-IPA algorithms over the pinned real
Ristretto implementation produce and consume released Bulletproofs proof bytes,
with the actual range parent and full IPA terminal equation preserved by direct
folding and linear-weight pullback?

Expected gates fixed in the implementation/tests:

1. Both interoperability directions pass across `n ∈ {8,16,32,64}`,
   `m ∈ {1,2,4,8,16}`.
2. Native materialized and pulled-back producers produce identical complete proof
   bytes for the same RNG tape.
3. Folding, flat/materialized, and flat/pulled-back validators agree on **exact
   residual points**, including well-formed invalid proofs.
4. Dropping either the range or IPA terminal obligation would accept a supplied
   negative control.
5. Actual context, public commitments, dimensions, round order, canonical
   encodings and nonzero-challenge guards are exercised.
6. Same-equation measurements and the upstream variable-time/randomized baseline
   remain distinct; slowdowns are retained.

These finite gates passed. General security, compiler correspondence and equality
of fallible native executions remain separate obligations.

## Implementation map

| File | Responsibility |
|---|---|
| [src/prover.rs](src/prover.rs) | Real bits; fresh masks; visible `t1,t2`; range responses; recursive `L,R` and four folds; materialized and pulled-back first-round variants |
| [src/verifier.rs](src/verifier.rs) | Received proof bytes; range residual; actual range-to-IPA parent; direct and flattened terminal checks; deterministic acceptance |
| [src/codec.rs](src/codec.rs) | Exact upstream layout; canonical scalar and point parsing; exact round count/length |
| [src/generators.rs](src/generators.rs) | Independently derived per-party SHAKE256 generators and default Pedersen bases |
| [src/transcript.rs](src/transcript.rs) | Merlin framing, challenge reduction, explicit zero refusal and public transcript audit |
| [src/linear.rs](src/linear.rs) | Checked dot/MSM and diagonal-view pullback; no truncating zip contract |
| [src/baseline.rs](src/baseline.rs) | **Only** module calling upstream whole-proof algorithms; interoperability/performance baseline |
| [src/tests.rs](src/tests.rs) | 13 substantive tests, including the 20-profile matrix and hostile controls |
| [src/experiment.rs](src/experiment.rs) | Seeded research fixtures, equality checks, raw timing samples and public transcript vectors |
| [src/main.rs](src/main.rs) | Measurements and independent `verify statement.json proof.bin` process entry |
| [EQUATIONS.md](EQUATIONS.md) | Exact equations, byte/transcript decisions and source pointers |

The native prover and validator share arithmetic, codec, generator and transcript
primitives, but the validator never calls the prover or receives its
witness/response vectors. Its folding implementation and its flattened weights are
separate code. Upstream cross-verification and literal raw-Merlin replay provide
additional checks against correlated mistakes in shared primitives. This is
independent authorship within one crate, not an independent external review.

## Selected research profile

- Profile name: `bp5-wire-strict-nonzero-v1`.
- Real `curve25519-dalek = 4.1.3`, `merlin = 3.0.0`, `bulletproofs = 5.0.0`; all
  direct dependencies use exact versions. [Cargo.lock](Cargo.lock) freezes
  transitive versions/checksums.
- `n ∈ {8,16,32,64}`; positive power-of-two `m`; `N = nm`; checked multiplication;
  `N ≤ 16384` as an explicit prototype resource bound. No padding, mixed bit
  widths, or arbitrary-count aggregation.
- Ordered public commitments and public `bits,count` are supplied by the
  validator's caller. Proof bytes contain neither a replacement commitment list
  nor an application context.
- The application prefix is `Transcript::new(b"zkc-goal3-range-native-v1")` followed by
  `append_message(b"application-context", context)`. Nonempty context is limited
  to 65536 bytes. Actual transaction canonicalization and ledger semantics remain
  the caller's responsibility; the fixture context is research data.
- Exact released range/IPA transcript labels and order; 64-byte challenge squeeze
  followed by Dalek wide little-endian scalar reduction.
- Reject zero `y,z,x,w,u` immediately, including before every inverse. **No
  retry/resampling.** This is stricter than upstream's nonuniform handling of
  degenerate challenges, so interoperability is scoped to the tested
  nondegenerate transcripts.
- Canonical response/terminal scalars may be zero. Blinding scalars may be zero.
  Identity value commitments are valid. Identity `A,S,T_1,T_2,L,R` are refused.
  `P` is allowed to be identity; `Q=wB` is nonidentity under the selected `w`
  guard.
- Raw proof length is exactly `32*(9 + 2*log2(n*m))`, from 480 bytes at `(8,1)` to
  928 bytes at tested `(64,16)`; the resource cap allows up to 1184 bytes.
- `prove` accepts a mutable caller `RngCore + CryptoRng`. Masks are sampled anew in
  the documented global-vector order. The test harness alone seeds ChaCha20. It
  deliberately does not match upstream's per-party randomness tape.

`validate` returns success only when **both** residuals are identity. `evaluate`
is an audit API returning residuals even for well-formed invalid proofs; receiving
a report is not acceptance. Call `report.acceptance()` to make the decision.

## Run

`just bench` runs this crate from the repository root and writes its JSON to the
chosen output directory. The measurement binary takes an optional trial count,
defaulting to nine timing trials after warmup:

```sh
cargo run --release --manifest-path bench/range-native/Cargo.toml -- 9
```

Each run also exports one statement and both proof files per profile into an
ignored `records/` directory beside this file, for use with `verify` below.
Neither the JSON measurements nor those exports are committed.

Individual commands, from this directory:

```sh
cargo fmt -- --check
cargo clippy --release --offline --locked --all-targets -- -D warnings
cargo test --release --offline --locked -- --test-threads=1 --nocapture
cargo build --release --offline --locked
./target/release/zkc-range-native-research verify STATEMENT_JSON PROOF_BIN
```

The `verify` command reads a bounded JSON public statement and a separate bounded
binary proof, constructs generators from the admitted profile, and runs all three
exact validators. Wrong context and a tampered canonical IPA terminal scalar fail
the process.

## What the baseline calls

`src/baseline.rs` is the only module that invokes an upstream whole-proof
routine, `RangeProof::prove_multiple_with_rng` and its verifier. Nothing in the
native path calls it. Generator reconstruction and Pedersen derivation are
implemented here from the released hashing rules; the tests use upstream's
public `G` accessor, and its private `H` array is checked indirectly through
proving in one direction and verifying in the other.

Native group contractions use Dalek's `MultiscalarMul`, whose interface is
documented as constant-time. That is an interface choice, not evidence about the
whole program: upstream's inner-product argument and combined verifier use
variable-time multiscalar multiplication, and the measurements name those
contexts separately.

Dependencies are pinned in this crate's own `Cargo.toml` and `Cargo.lock`, which
is why a benchmark may depend on a library the product does not.

## Limits

No formal security, soundness, zero-knowledge, or whole-code constant-time claim.
Native MSM calls use Dalek's constant-time `MultiscalarMul` interface; witness
admission, allocation, surrounding control, secret lifetime and the complete
compiled program have not been audited for leakage. This prototype does not
zeroize secret vectors or enforce nonforkable proof-session authority. A caller
can misuse or clone an RNG; the API does not prevent that.

No maintained compiler pass, checker, Lean theorem, reference interpreter,
transaction application, BLS instantiation, multiparty topology, or
resource-failure equivalence is delivered here. Source-level temporary storage
counts are not total allocation/copy measurements or peak RSS. Algebraic equality
is scoped to successful arithmetic under sufficient resources.
