# Direct application baselines

This benchmark crate measures matched direct Rust implementations of the two
application families against the zkc route. `just bench` does not run it; drive
it with the scripts in this directory. Build products, private fixtures, proofs
and measurement logs are local run artifacts. The comparison pages retain
historical summaries; they are not measurements of every later revision.

A separate `tx-matched` route implements the complete PIR transaction algorithm
with explicit IPA folds and separate range/IPA/balance/owner equations. See
[MATCHED.md](MATCHED.md) for its source mapping, transcript, deviations and checks.
The `tx` command is the optimized upstream-practice comparison; its timing
difference from native does not measure interpreter overhead.

These are runnable, whole application Rust producers and independent public-only
verifiers. They do not establish production security, interoperability, or a
formal cryptographic reduction. See [COMPARISON.md](COMPARISON.md)
for actual measurements.
Neither implementation calls a PIR interpreter, a whole-protocol native callback,
or a zkVM library.

## Transaction algorithm and trust boundary

`src/transaction.rs` admits the exact `parameters.json`, verifier-owned
`fixture/ledger.json`, `fixture/statement.json` and private
`fixture/witness.json`. It checks the same supported widths/counts, canonical
integers/points/scalars, nonidentity owner keys, ordered unique input IDs,
ledger/network/snapshot agreement, prior range declarations and integer bounds.
Configuration reads are bounded to four MiB **before** JSON allocation. The
verifier reads no witness. The ledger authority still supplies authenticity,
freshness, unspentness and prior valid input ranges; a declared range is not a
new proof. Ledger openings, extracted output openings and excess knowledge must
refer to a common witness experiment for the conservation interpretation.

The producer calls pinned Bulletproofs 5.0.0 `RangeProof::prove_multiple_with_rng`
for all output values. It then proves knowledge of
`sum(input_blindings)-sum(output_blindings)` relative to `H` for the actual public
point `sum(input_commitments)-sum(output_commitments)-fee*G`. Each selected owner
gets a separate Schnorr proof relative to `G`. Every nonce uses `OsRng`, as do the
upstream proof masks and verifier batching randomness. The fixed fixture's
ledger/output commitments are deliberately identical across timing samples;
internal range commitments and Schnorr nonces are fresh. Repeated proofs are
checked to differ. Identity excess is legal, identity owner/nonce points refuse.

The common transcript binds a versioned direct source/profile identifier,
parameters, full ordered statement (including fee/context/version/network),
selected ledger entries (including IDs, owners, prior ranges and commitments),
Pedersen bases and the fixed upstream generator-suite identifier. The upstream
range transcript is a domain-separated clone. The resulting complete range
proof is appended to the common transcript before balance and owner challenges.
Each Schnorr challenge follows its component index, base, subject and nonce;
responses are appended before the next component. Verification recomputes all
challenges from public inputs and proof messages. No observed challenges are
accepted as inputs.

The producer parses private values without checking conservation, owner-key
agreement or commitment openings. Consistently changed false outputs, wrong
excess/owner secrets and out-of-range outputs are actually produced and then
rejected by the verifier. Upstream is allowed to reject malformed witness
shapes. The control runner tests `2^64` as witness-input refusal at 64-bit width:
the upstream `u64` API cannot represent an out-of-range value at that width.
Narrower widths exercise actual invalid-range proof production and rejection.
Single-input fixtures omit the inapplicable owner/order swap controls; every
remaining public mutation must change its input. Control failures are recorded
before raising, and a crash is never counted as an expected refusal.
This is normal direct-library author practice, not the PIR range
algorithm's ABI: upstream fuses the range/IPA algorithms and optimizes group
operations, while the PIR route exposes its component computations. The direct
profile also retains upstream Fiat–Shamir exceptional-challenge behavior; it
does not add the PIR profile's separate zero-challenge refusals.

## Execution algorithm and trust boundary

`export_execution.py` calls the existing compiler's public `relation-read` once
per CPU, memory and link R1CS file. It retains every original sparse matrix
coefficient and the exact original assignment layout, public statement,
configuration and original PIR source hash. This is untimed public input staging;
it never executes a prover, obtains challenges or exports a relation certificate.
The verifier caller owns and authenticates this exported relation configuration.
The export is not accepted from the candidate proof. As with verifier-owned
compiled matrices elsewhere in the repository, its association with the declared
machine is an application admission premise. The source fixtures' public and
relation configuration/statement files must agree.

`src/execution.rs` implements this topology:

1. Zero-pad the original assignment, then commit **once** with `zkc-arkworks`.
2. Open that original at Boolean coordinates for ONE and every public statement
   coordinate; the verifier checks every value and PCS proof.
3. For each of CPU, memory and link, derive `tau` and prove cubic sumcheck for
   `eq(tau,x)*(Az(x)*Bz(x)-Cz(x))`, starting from zero. Send actual `Az(r), Bz(r),
   Cz(r)` reports, and check the outer terminal expression.
4. Derive three fresh batching scalars after those reports. Prove quadratic
   sumcheck for the product of the public mixed matrix contraction `K(r,y)` and
   the **original** multilinear assignment polynomial `z(y)`.
5. Gather the three actual inner points/residuals. Open the same original at
   those three points, verify all three PCS proofs, and require each actual
   `K(r,s)*z(s) == residual`. The verifier computes `K` directly from its sparse
   matrices and equality weights. There is no division, including at zero `K`.

The complete typed public root includes all nine matrices, dimensions, public
statement, machine config/program, original source hash, direct algorithm
version and full actual verifier key/profile. Merlin absorbs commitment,
opening values/proofs, every round's coefficients and reports. Challenge draws
are replayed by the verifier, never loaded from a file. MSB-first folding matches
the adapter's original polynomial convention. The verifier enforces exactly
four coefficients per cubic and three per quadratic, each recurrence, all
terminal expressions, canonical scalar/PCS encodings and exact EOF.

The verifier's code path contains no assignment, trace, prover-key import,
pre-recorded challenges or whole-relation precheck. Private invalid assignments
are committed and reduced before the public verifier rejects them. This remains
the existing **nonhiding development multilinear KZG** profile. Both paths share
its trusted OS-generated fixture setup; setup import is separately measured.

## What the baselines call

The transaction baseline calls upstream Bulletproofs whole-proof routines. The
separate `src/transaction/matched.rs` route does not: it implements the local
algorithms of [`confidential-transaction.pir`](../../examples/protocols/confidential-transaction.pir)
directly, so that the comparison is against the same algorithm rather than
against a different one. Its `G` comes from the pinned `BulletproofGensShare::G`
API; upstream's `H` is private, so it is derived as
[`bench/range-native/src/generators.rs`](../range-native/src/generators.rs)
does, with SHAKE256 and Dalek's `from_uniform_bytes`. No curve, field, hash or
transcript primitive is reimplemented here.

The direct R1CS reduction is authored here from the maintained source
algorithms; no upstream zkVM or generic interpreter hides behind the baseline.
Dependencies are pinned in this crate's own `Cargo.toml` and `Cargo.lock`.

## Wire and input costs

The proof starts with `ZKCTXD01` or `ZKCEXD01`. Each subsequent message is a
little-endian u32 byte length plus its payload. Message labels and ordering are
fixed by the protocol, not supplied by the proof. Transaction payloads are the
complete upstream range proof followed by one nonce/response pair for balance
and each owner. Execution payloads are the original commitment, public
value/proof pairs, three sets of outer rounds/reports/inner rounds, then the three
final value/proof pairs. Scalars are canonical 32-byte little-endian encodings;
PCS objects use the adapter's canonical checked encoding. Reader bounds and
exact EOF reject truncation/extra data. Proof sizes include all framing and
all combined cryptographic proofs, excluding verifier-owned public inputs on
both paths. There is no identical ABI or proof-byte compatibility claim.

Warm runs cache parsed public inputs, serialized transcript-root context,
Bulletproof generators or authenticated PCS keys, and parsed private scalars.
They include all per-proof transcript work, private working-vector/table copies,
commitments, sumchecks, openings, group checks, serialization and parsing.
Setup/admission, assignment JSON parsing/padding, public-root preparation and
prover-key import are recorded separately. Fresh process measurements include
those costs, file I/O and launch overhead. Neither warm nor process rows are
pure algebra timings.

## Reproduce

Run from the repository root with the fixture runs available. The paths below
identify the original local campaign directories, which are not distributed
with a clean checkout. These commands replay an existing campaign; they do not
generate all its inputs. Supply an equivalent retained run directory, the
baseline binary as `--binary` and, for execution measurements, the frozen tools
as `--tools`; neither has a default location. A lockfile permits offline
building only after its source dependencies have been fetched.

The [measurement policy](../README.md#reading-and-recording-a-measurement) states
what to retain for a new run. The summaries and their original identities remain
historical evidence until a new campaign is actually executed.

```sh
CARGO_TARGET_DIR=/tmp/zkc-4b-baselines/target cargo build --offline --locked --release \
  --manifest-path bench/application-baselines/Cargo.toml

binary=/tmp/zkc-4b-baselines/target/release/zkc-application-baselines
python3 -B bench/application-baselines/measure.py --binary "$binary" \
  --application tx --run /tmp/zkc-4b-transaction/final-n8-m2 \
  --output /tmp/zkc-4b-baselines/reproduce-tx-n8-m2 --compare-native
python3 -B bench/application-baselines/measure.py --binary "$binary" \
  --application tx --run /tmp/zkc-4b-transaction/n32-m8-k4 \
  --output /tmp/zkc-4b-baselines/reproduce-tx-n32-m8-k4 --compare-native
python3 -B bench/application-baselines/measure.py --binary "$binary" \
  --application execution --run /tmp/zkc-4b-execution/tiny \
  --tools /tmp/zkc-4b-execution/tools \
  --output /tmp/zkc-4b-baselines/reproduce-execution-tiny --compare-native
python3 -B bench/application-baselines/measure.py --binary "$binary" \
  --application execution --run /tmp/zkc-4b-execution/memory64 \
  --tools /tmp/zkc-4b-execution/tools \
  --output /tmp/zkc-4b-baselines/reproduce-execution-memory64 --compare-native
```

Each output directory must be new. `--samples` defaults to three and requires
at least three. Other measured fixtures are transaction `n16-m4`, `n64-m2` and
execution `memory8`, `loop16`. Native execution uses the frozen tools named by
`--tools`; transaction uses each run's frozen tools unless `--tools` names
others. Receipts retain commands, raw samples, RSS, stdout, stderr,
and binary/lock hashes. Each native sample pins its actual source, descriptor,
construction, physical artifact and input envelope before execution and checks
those hashes afterward. The runtime's public binding deliberately survives
compatible physical rewrites, so it cannot identify the timed implementation.
Tool pins include the transaction admission helper; Python harness hashes and
the execution admission helper's loaded repository sources are also retained.
`report.py RESULTS_JSON...` regenerates compact comparison tables.

Native timing includes the frozen artifact admission. The pipeline column adds
application admission but excludes the later retained claim check; receipts mark
`native_claim_admission_included: false`. Historical measurements are preserved
with their original manifests, rather than retrospectively assigned new pins.

Standalone binary CLI (all paths are positional):

```text
tx prove PARAMETERS LEDGER STATEMENT WITNESS PROOF
tx verify PARAMETERS LEDGER STATEMENT PROOF
tx bench PARAMETERS LEDGER STATEMENT WITNESS OUTPUT_DIR SAMPLES
execution prove PUBLIC_JSON SETUP_JSON ASSIGNMENT_JSON PROOF
execution verify PUBLIC_JSON SETUP_JSON PROOF
execution bench PUBLIC_JSON SETUP_JSON ASSIGNMENT_JSON OUTPUT_DIR SAMPLES
execution setup-bench ARITY SAMPLES
```

`PUBLIC_JSON` and normalized `SETUP_JSON` are emitted by `export_execution.py
--run RUN --output OUTPUT`. Proving loads the pinned public proving material
specified in setup JSON. Verification needs only `verifier_key` and its
independently trusted `verifier_key_id`; it does not open the proving-key path.
`setup-bench` times fresh matching-arity OS-generated keys without replacing the
original fixture key used by proof comparisons.

## Correctness controls and checks

```sh
cargo fmt --check --manifest-path bench/application-baselines/Cargo.toml
CARGO_TARGET_DIR=/tmp/zkc-4b-baselines/target cargo clippy --offline --locked \
  --all-targets --manifest-path bench/application-baselines/Cargo.toml -- -D warnings
CARGO_TARGET_DIR=/tmp/zkc-4b-baselines/target cargo test --offline --locked --release \
  --manifest-path bench/application-baselines/Cargo.toml
ruff check --no-cache bench/application-baselines

binary=/tmp/zkc-4b-baselines/target/release/zkc-application-baselines
python3 -B bench/application-baselines/controls.py --binary "$binary" \
  --application tx --run /tmp/zkc-4b-transaction/final-n8-m2 \
  --output /tmp/zkc-4b-baselines/reproduce-controls-tx
python3 -B bench/application-baselines/controls.py --binary "$binary" \
  --application execution --run /tmp/zkc-4b-execution/tiny \
  --export /tmp/zkc-4b-baselines/reproduce-execution-tiny/export \
  --output /tmp/zkc-4b-baselines/reproduce-controls-execution
```

The Rust tests include honest zero excess, fresh transaction proof randomness,
consistent false outputs, private invalid witnesses, transcript/context binding,
mutation of every execution message, and attacks at **each** final connection
with valid PCS proofs and valid prior recurrences. The latter tests also execute
with exactly zero matrix coefficients, rejecting a nonzero residual without
inversion. CLI controls use isolated public-only verifier bundles, mutate every
message and selected lengths, test EOF, and produce invalid full proofs without
a whole-relation producer gate. Tests are evaluation evidence, not security
proofs or a new production cryptographic library.

The native CLI `run_seconds` includes proof reads or durable proof publication
(`sync_all`) and runner teardown. Direct warm timers exclude file I/O. Compare
whole process/pipeline costs or the prepared-host evaluation for aligned API
boundaries; subtracting these two run fields is not a VM-overhead estimate.
