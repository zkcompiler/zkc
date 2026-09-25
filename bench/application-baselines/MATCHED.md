# Matched transaction algorithm, direct Rust

`tx-matched` is a complete independent producer and public-only verifier for the
bounded confidential-transaction application. `tx` remains the upstream
Bulletproofs comparison. Neither the matched route nor its transcript calls a
PIR interpreter, `RangeProof`, whole-native callback or precomputed proof.

This matches the source-level range/IPA/balance/owner algorithms and their check
order. It is suitable for a whole-application comparison with the native dense
route. It does **not** make subtraction of timings a pure VM-overhead measurement.
The differences below remain part of the experiment. This adds no production
security, zero-knowledge, leakage or cryptographic reduction theorem.

## Source and operation correspondence

The authority for this comparison is the actual generated transaction source,
`examples/protocols/confidential-transaction.pir`, specialized by the existing
transaction builder for larger parameters. Let `n=bits`, `m=outputs`, `k=inputs`,
`N=n*m`, and `r=log2(N)`. All widths, counts, integer bounds, ledger/statement
admission, canonical scalar/point codecs and owner checks use the existing
direct application's admission code. Authenticated prior ledger ranges,
freshness/unspentness and common-witness conservation premises are unchanged.

| Source algorithm / cut | Direct operation |
|---|---|
| ValueCommitments; CheckCommitments | Separate value/base and blinding/base multiplications; append copies; two all-one MSMs plus every ordered point equality on P and V |
| DrawVectorMasks; RangeCommitments | Fresh alpha, rho, N sL, N sR in that order; four CT MSMs and two blind-base multiplications |
| y, z; RangePolynomials | Party-major `d = z^[2..m+2) tensor 2^[0..n)`; materialized vector powers, gather copies, products, sums and three dots |
| DrawPolynomialMasks; PolynomialCommitments | Fresh tau1 then tau2; four scalar multiplications and two point additions |
| x; RangeResponses | Materialized scaled vectors and sums; `tx=<l,r>`, tau and mu, in that message order |
| w; CheckRangeEquation | Separate required range equation, finite power sums (including y=1), one commitment MSM and five scalar multiplications |
| RangeParent on P and V | Compute q, parent and y-inverse factors locally; materialize H-prime then MSM; separate G MSM and four scalar multiplications |
| PrepareIPA on P | Materialize H-prime again; two MSMs and `<l,r>*q`; require equality with P's computed parent |
| r IPA rounds on P | Explicit copied halves, four cross-term MSMs, two q multiplications; transmit L/R; challenge; materialized a,b,G,H folds, including final one-element bases |
| r IPA rounds on V | Require nonidentity L/R; challenge; add u²L and u⁻²R; expand separate G/H weights with MSB-first Kronecker products |
| CheckIPATerminal on V | Two separate MSMs; rematerialize H-prime; check accumulated parent against `a*G_final + b*H_final + a*b*q` |
| ExcessBlinding; BalanceSubject | P sums input and output blindings in the proof call; V computes two all-one MSMs, fee multiplication, two negative-one multiplications, then additions |
| Balance and every owner | Fresh independent nonce, nonidentity guard, challenge, response, then one separate Schnorr equality; owner nonidentity check at each owner component |

All MSMs in the new route use Dalek `MultiscalarMul`; all point multiplications
use the same pinned Dalek 4.1.3 scalar-action APIs as the native CT kernels.
There is no verifier randomness, random batching, variable-time ablation,
cross-equation fusion, omitted owner or omitted IPA producer fold. Proving does
not execute V's range, terminal IPA, balance or owner equations as preprocessing.
Wrong output openings stop at P's actual source commitment guard; wrong excess
and owner witnesses, consistent false conservation, and representable oversized
outputs create complete proofs that the public verifier rejects.

## Transcript and proof wire

The mathematical domain is `ristretto255.group` / `ristretto255.scalar`; scalar
messages use canonical 32-byte little endian encodings, points canonical
Ristretto compression. Challenges are Merlin 3.0.0 64-byte outputs reduced by
Dalek `from_bytes_mod_order_wide`, with an explicit zero refusal and no retry.

The independent transcript starts at `zkc-direct-transaction/pir-matched/1` and
absorbs `public-root` once. Its root is the typed compact JSON tuple of:

1. Hex of the fixed matched profile string from `matched.rs`.
2. Hex of the application's `zkc/confidential-transaction/1` domain bytes.
3. Hex of the existing direct admission's complete canonical public root:
   existing direct profile, parameters, full statement, selected ordered ledger
   entries, both Pedersen bases, fixed generator-suite identifier.
4. Ordered hex encodings of every actual G and every actual H generator.

Consequently context, version, network, snapshot, input IDs/order, admitted
commitments, prior ranges, owner keys, output order, fee, dimensions, bases and
generators precede the first challenge. Sharing admission retains the upstream
direct profile as a nested identifier; the matched profile and transcript
domain distinguish the routes. An unselected ledger entry is admission-checked
but is not a new selected statement field.

The fixed schedule is:

```text
ordered_commitments, range_a, range_s -> range_y -> range_z
range_t1, range_t2 -> range_x
range_tx, range_tau, range_mu -> range_w
(ipa_left, ipa_right -> ipa_challenge) repeated r times
ipa_terminal_a, ipa_terminal_b
(component index, schnorr_nonce -> schnorr_challenge, schnorr_response)
    for balance then owners 0..k-1
```

Each arrow is `challenge_bytes(label, 64)` with the indicated label. Every proof
message is absorbed with its indicated label, in order. Component indices use
Merlin `append_u64("schnorr-component", index)`. Merlin's challenge operation
advances the transcript; derived challenges are not proof messages or supplied
by a caller. Repeated IPA labels are distinguished by ordered transcript state.
All prior proof messages and all prior challenge transitions precede each next
challenge. The public root is inherited throughout; components do not fork.

Wire magic is `ZKCTXM01`. Each P message has a u32 little endian byte length.
The first payload is exactly `32*m` ordered commitment bytes; every remaining
point/scalar payload is exactly 32 bytes. There are `10+2*r+2*(1+k)` frames.
Proof size is `8 + 4 + 32*m + 36*(9+2*r+2*(1+k))`: 904 bytes at 8/2/2 and
1528 bytes at 32/8/4. Length, canonical encoding, point guards and exact EOF are
checked. Native typed framing, source origins, construction/artifact identities
and public-root bytes are different; no native wire or challenge equality is
claimed. Cross-route proofs fail the version check.

## Remaining experimental differences

- Native artifact framing binds source/construction identities and qualified
  operation origins. This direct route binds an installed versioned algorithm
  string and the same application facts, with its own labels and wire. Native
  proof sizes and transcript costs therefore differ. This is a separately
  instantiated Fiat–Shamir experiment with the same challenge cuts and binding
  obligations, not a proof of construction equivalence.
- Native randomness uses a fresh OS-seeded `StdRng` resource. This direct route
  draws each scalar with `Scalar::random(OsRng)`. Both reduce a 64-byte draw
  using the same scalar sampler; draw count and order match. Equality of the
  joint RNG distributions is not established. Entropy cost, random tape and
  proofs differ. Draws are
  `2*N+5+k` private scalars and `r+5+k` public challenges. Direct challenge
  generation also executes its zero/inverse guard on the producing endpoint;
  a projected artifact's placement of verifier-only local work can differ.
- Direct G uses Bulletproofs' public API. Its H API is private, so H is generated
  with the existing helper's procedure using the already locked SHA3 0.10.9.
  Setup constructs upstream G/H and materializes H again. These costs are outside
  proof calls and included in public/generator setup fields. Exact G/H bytes are
  compared with the native admission helper in the functional comparison.
- Native input envelopes already contain field-valued amounts and bit vectors.
  This direct API accepts the same application `u64` amounts and computes the
  bit vector inside proving. Manually forged field-valued producer envelopes
  (for example negative scalar amounts) are outside this direct witness API;
  their canonical scalar messages remain rejected/checked normally. At width
  64, `2^64` is input refusal rather than a representable range counterexample.
- Admission shares the upstream excess computation and parsing. The matched
  route additionally recomputes BalanceSubject and ExcessBlinding in their
  source positions. Rust types replace PIR's redundant runtime shape checks
  once admission and fixed local construction establish those shapes. P and V
  still execute both commitment-length MSMs and all per-output equality guards.
- Vector intermediates, copied splits, append copies, scale_each materialization
  and recursive G/H folds are retained as shown above. Rust monomorphization,
  lifetimes, inlining, layout and allocation retention differ from runtime
  values, cloning, resource charging, capabilities, instruction dispatch and
  observation recording. There is no exhaustion/observation refinement claim.
- `measure.py --transaction-algorithm matched` selects `tx-matched`. With native
  comparison its default is `dense.compile.stdout`; `--physical` selects an
  explicit candidate, and explicit `--linear-contractions` selects the existing
  contraction ablation. Native claim admission remains optional as in the
  original harness: use `--include-claims` for the optimization work integrated measurements.
  Do not combine selected contraction/implementation changes with this baseline
  and attribute the difference solely to the runtime.

Native CLI `run_seconds` includes proof-file reads or durable publication
(`sync_all` and persist), report construction and runner teardown. Direct API
proof timers exclude file I/O; its process path uses `fs::write` without the same
publication policy. The prepared-host experiment supplies the separate in-memory
comparison. No subtraction of those CLI/direct timer fields isolates VM cost.

## Functional reproduction

The commands below replay retained campaign inputs. Their `/tmp` paths and
frozen native tools are not supplied by a clean checkout; see the
[input requirements](README.md#reproduce). Select your actual run directory and
binary explicitly. The recorded measurements are not rerun by building the crate.

Build with the existing lock, including all unchanged prior dependency versions:

```sh
CARGO_TARGET_DIR=/tmp/zkc-baseline/matched-baseline-target cargo build --offline --locked --release -j 2 \
  --manifest-path bench/application-baselines/Cargo.toml
```

Standalone commands have the original positional CLI shape:

```text
tx-matched prove PARAMETERS LEDGER STATEMENT WITNESS PROOF
tx-matched verify PARAMETERS LEDGER STATEMENT PROOF
tx-matched bench PARAMETERS LEDGER STATEMENT WITNESS OUTPUT_DIR SAMPLES
tx-matched trace PARAMETERS LEDGER STATEMENT PROOF TRACE_JSON
```

`trace` first verifies, then exports only public messages and recomputed direct
challenges for the existing helper's independent equations. It is diagnostic:
the helper trusts these observed challenge bytes; it neither certifies this
transcript construction nor runs Lean on the direct route. The actual direct
verifier always derives its own challenges and never consumes this export.

```sh
python3 -B bench/application-baselines/matched_compare.py \
  --run /tmp/zkc-baseline/baseline/tx-small --output /tmp/matched-small-new \
  --binary /tmp/zkc-baseline/matched-baseline-target/release/zkc-application-baselines --native
python3 -B bench/application-baselines/matched_compare.py \
  --run /tmp/zkc-4b-transaction/n32-m8-k4 --output /tmp/matched-large-new \
  --binary /tmp/zkc-baseline/matched-baseline-target/release/zkc-application-baselines --native
python3 -B bench/application-baselines/controls.py \
  --application tx-matched --run /tmp/zkc-baseline/baseline/tx-small --output /tmp/matched-controls-new \
  --binary /tmp/zkc-baseline/matched-baseline-target/release/zkc-application-baselines
```

The comparison pins actual fixture/tool/artifact files, produces two distinct
direct proofs, verifies in a public-only bundle, compares every G/H byte, runs
independent direct equations, and optionally produces/verifies fresh dense
native proofs on the same data. It produces complete invalid proofs for every
owner, excess, conservation and supported range control on both routes. It does
not compare proof bytes or infer performance from functional run timings.

The Rust tests also cover zero excess, 64-bit maximum amounts, each equation's
named failure, mutation of every proof message, every proof-point identity
guard, exact framing/EOF, public context, ordered equal-sum commitment swaps,
noncanonical encodings, and the finite y=1 power-sum case. Existing upstream and
execution tests remain in the suite.

## Execution comparison adequacy

The unchanged execution route is already a complete algorithm-level comparison:
one original commitment; ONE and all public coordinate openings; CPU, memory and
link cubic outer sumchecks; three quadratic inner sumchecks; three final
original openings and three separately required coefficient-times-value
equations. For the four-field statement it has eight PCS verifications. Its
zero-coefficient controls retain the equation without division, and its unit
tests attack each terminal connection after valid PCS checks.

It still uses its own transcript/framing, direct sparse matrix loops,
allocation/folding layout and preparation rather than the source runtime's
materialization and dispatch. Its matching schedule is adequate for a complete
algorithm comparison, not for a pure interpreter-overhead subtraction. No
execution implementation changes are part of this addition.
