# Benchmarks

One scheduler measures independent protocol implementations, ordinary source
programs, and composed library workloads. Results remain separate by operation,
shape, input policy and timing boundary. There is no aggregate score or implicit
family weight. STARKs have more coverage because their distinct dimensions need
separate experiments, not because their cases count as extra votes.

## Run

Use explicit, already-built executables. The harness does not build dependencies,
tune the host, raise execution limits or retry failed samples.

```sh
cargo build --release --locked -p zkc-benchmarks
python3 common/benchmarks/run.py list
python3 common/benchmarks/run.py run --preset smoke \
  --compiler build/compiler/zkc-compile --runtime target/release/zkc \
  --worker target/release/zkc-benchmarks \
  --output build/experiments/benchmarks
```

The output directory must be new. Runs are exploratory by default: they do not
acquire a host-wide lock and can overlap with development work. Use repeated
baseline/current comparisons under similar load to identify broad trends;
concurrent timings do not establish small speedups.

Pass `--exclusive` to either benchmark entry point to acquire
`/tmp/zkc-benchmark-execution.lock` across preparation, timing and validation.
Exit 75 means another cooperating session owns the slot. Do not wrap the harness
in another acquisition or delete the lock file. Workers inherit the owned
descriptor so the slot remains held if the supervisor is killed.

`coordination.json` records whether the run was `uncoordinated` or `exclusive`,
its start/end times and, for exclusive runs, lock acquisition time. An exclusive
lock coordinates cooperating suites; it does not stop ordinary builds or isolate
unrelated host activity. Schedule a quiet interval explicitly for precise results.
Ordinary builds and tests should use separate output directories and bounded
parallelism, without a host-wide benchmark lock.

Selection options intersect:

- `--case NAME`: individual case; repeat to select several.
- `--suite NAME`: family; repeat to select several.
- `--preset smoke`: a fixed, small list covering the major execution paths.
- `--preset stark`: AIR (both single-table profiles), FRI, polynomial, extension, transcript and machine cases.
- `--preset execution`: all source controls and library workloads, without an external reference build.
- `--preset all` (default): everything, including the optional Monero and c-kzg comparisons.

The default is four **sequential** fresh processes per implementation/operation,
two warmup samples and five measured samples per process, one call per sample.
`--processes`, `--warmups`, `--samples` and `--iterations` override these choices.
A correctness trial can use `--processes 1 --warmups 0 --samples 1`; it is not a
stable performance estimate. `--source` selects project/library sources; the
executing harness remains this checkout. Both are identified and captured.

Use `--compiler-option=--fuse-collect-fold` to measure an explicit compilation
choice; repeat `--compiler-option` to combine supported switches. The manifest
records the choices and captures the resulting packages. Compare separate runs
with identical sources, inputs and worker settings. A smaller intermediate or
instruction count does not by itself establish a timing improvement.

`--threads` selects the shared Native CPU context (default one). The development
worker transports this request through `RAYON_NUM_THREADS`; SDK and CLI execution
receive an explicit context. Worker reports separate pool initialization from
admission and timed calls. Native workers must report their actual owned worker
count; live and saved-result validation require it to match the request.
Separate CLI proof observations pass `--threads`
explicitly, check the CLI's reported worker count and retain it beside their
process wall times. Foreign reference providers retain their own policy;
this is not a universal process thread limit.
`--cpus 2,4-7` pins the suite and children to a set within the current affinity;
`--cpus 2` selects one CPU. Workers check the requested environment, main-thread
affinity and every surviving thread's CPU set. This is an exit-time observation,
not scheduler tracing or proof that a terminated thread never escaped.
The harness records CPU topology, common runtime ISA features across the selected
CPUs and governor/turbo/SMT settings but does
not change them. `--seed` shuffles case/operation blocks; paired implementations
run consecutively with their order reversed on alternate process repetitions.
Child processes receive a recorded, allowlisted environment: tool paths, temporary
paths, allocator/thread settings and explicit locale controls. Ambient feature
switches, Python injection paths and unrelated credentials are not inherited.
The schedule seed does not seed production prover randomness. Input generators use fixed,
recorded algorithms and seeds, with full generated inputs retained.

Rust workers embed their compiler, profile, target features, Rust flags and
crate features. `--cargo-manifest Cargo.toml` additionally captures an offline,
locked source dependency-feature resolution; repeat for standalone reference
workspaces. Source graphs and lockfiles do not attest which features a prebuilt
binary linked. Compiled Rust target features also do not describe the ISA of
separately compiled C/assembly dependencies.

### EIP-4844 comparison

Build the [pinned standalone reference](../tests/reference/c-kzg/README.md):

```sh
cargo build --release --locked --manifest-path common/tests/reference/c-kzg/Cargo.toml \
  --bin zkc-c-kzg-benchmarks --target-dir build/experiments/c-kzg-reference
python3 common/benchmarks/run.py run --suite eip4844 \
  --compiler build/compiler/zkc-compile --runtime target/release/zkc \
  --worker target/release/zkc-benchmarks \
  --c-kzg build/experiments/c-kzg-reference/release/zkc-c-kzg-benchmarks \
  --cargo-manifest Cargo.toml --cargo-manifest common/tests/reference/c-kzg/Cargo.toml \
  --threads 1 --cpus 0 --output build/experiments/eip4844
```

Use an allowed CPU. Compare multicore conditions in a separate run, for example
`--threads 4 --cpus 0-3`. c-kzg's EIP-4844 APIs are single-threaded; its setup
`precompute` setting stays zero because it targets EIP-7594 operations.
Neither affinity nor the Rayon environment creates a shared provider budget.
The reference uses its pinned `std` and `portable` features; Native keeps its
normal build policy. Captured feature graphs expose that distinction, which
also prevents interpreting the API ratio as a matched ISA comparison.

The panel measures the ordinary authored EIP-4844 library: commitments, point
openings and verification, single blob proofs, and batches of 1/4/16 blobs.
Blobs contain distinct deterministic full-width scalars. Every function output
is compared with the reference outside the execution timer; every produced blob
proof is byte-checked and cross-verified. Changed statements and truncated and
trailing proofs are negative controls. The panel stays within normal Host
capacities. A 64-blob concatenated statement exceeds the current logical tree
limit, so it is outside the maintained timing panel. A refused case remains
failed evidence and is never silently resized.

The source timer includes SDK input adaptation, source-level statement/setup
validation, provider conversions, execution, publication and teardown. The
reference timer covers the upstream call and returned bytes. Both exclude
result checks and proof-file writes. Source JSON decoding parses input documents
and resolves deferred file references; the timed SDK call reads those payloads,
checks pins and imports values. Preowned ingress materializes payloads during
its one-time input construction. Reference input decoding and setup loading are
outside its timer. Lifecycle records separate source capture/admission,
document parsing/reference resolution, ownership, requests and diagnostics. Reference setup/decode
times are diagnostics. Conversion diagnostics are counts, not isolated timings.
Thus this is a practical API comparison, not a matched kernel-only speedup.
The current compiler's mixed-provider policy is used normally. An all-Arkworks
KZG baseline needs an explicit captured pre-preference compiler; the harness
does not rewrite executable artifacts to change providers.

### External Monero comparison

Build `monero-benchmark` using the [pinned reference build](../tests/reference/monero/README.md)
in Release mode, then supply `--monero /path/to/monero-benchmark` and
`--monero-source /path/to/pinned/monero`. The client uses upstream randomness;
the deterministic replay wrapper is linked only into `monero-reference`.
`--suite monero` compares counts 1, 2, 4, 8 and 16.

## Coverage

| Family | Dimensions and purpose | Evidence limit |
|---|---|---|
| `schnorr` | BLS12-381 G1/Fr, Spongefish 0.7.4 SHAKE128 | Cross-verification with independent arkworks/Spongefish client |
| `monero` | BP+ proving/verification, 64-bit amounts, 1–16 commitments | Upstream C++ comparison; fixture amounts and small masks, not a sampled wallet workload |
| `sumcheck` | Public tables of 16–65,536 elements | Independent Rust algorithm; verifier includes linear public-table evaluation, no PCS |
| `finite` | Identical pointwise polynomial + sum as reduction, collect + sum, bulk operations, total collect–fold and total fold; KoalaBear and BLS12-381 Fr; 0/17/1,024/8,192 elements | Independent Python expectations; exposes source-form recognition and materialization differences |
| `numerical` | Two columns and a scalar capture; map, collect and vector operations; vector, sum and product results; KoalaBear, BLS Fr and dense degree-eight extension; 0–8,192 elements | Matched arithmetic and inputs across forms; includes equality and Host costs, with independent Python expectations |
| `expression` | Fixed panel of short/deep Horner, wide independent, shared-subexpression, capture-heavy and input-heavy functions; KB, Fr, dense KB Ext4/Ext8, binary64 and binary Ext3 | Independent authored Python formulas; map/sum/product; two additional validation-only shapes; source shape needs lowered-IR inspection |
| `field_vector` | Separately named add, subtract, Hadamard multiply, scale, sum, product and dot controls; larger KoalaBear/BLS Fr vector results at 1,024 (add) and 8,192 (Hadamard) | Independent scalar expectations and complete vector equality; SDK/run includes validation and Host costs |
| `transform` | Separate DFT and interpolation calls, unit shift, full dense coefficients; KB/Ext4/Ext8 at 32, KB/Ext8 at 1,024 | Independent Python evaluation; polynomial adaptation and equality remain inside the SDK call |
| `coset` | Separate point enumeration and even/odd folding; KB/Ext4/Ext8 at 32 and 8,192, dense extension shifts | Independent integer field arithmetic; arbitrary fold inputs, full result checks and Host costs |
| `coset_batch` | Matched per-column and library extension; KB/Ext4/Ext8, widths 1/4/16/64, separate height and row-layout controls | Independent integer transforms; every coordinate checked; row-layout cases include both transposes and SDK/run includes Host and equality costs |
| `coefficient_batch` | BN254 coefficient prefixes versus explicitly padded per-column FFTs; threshold neighbors at 64 outputs, short/dense pairs at 4,096 and 32,768 outputs, widths 1/3 | Independent modular Python transform and complete column-major output equality; identical coefficients across forms; default Host capacities and source construction costs |
| `coset_point` | Direct opening claims, repeated native interpolation/evaluation, and coefficient reuse for multiple points | Full point-major output check; on/off-domain controls; SDK timing includes setup, validation and output construction |
| `quotient_split` | Matched library batch and explicit per-block coefficient evaluation; base, quartic and octic KoalaBear; varying input height, block width and count | Independent coefficient/block-evaluation oracle; includes interpolation, padding, output checks and Host costs; no divisibility proof |
| `literal` | Constants versus operand captures in ordered Local loops across all installed fields; zero, first and repeated reach | Independent repeated-addition oracle; inspect exported reached literal counts; SDK/run includes Host and checking |
| `vector_literal` | Typed `vector.constant` versus decoded vector operands; KoalaBear/BLS Fr, 1,024 elements with 17 reaches and 8,192 elements with one reach | Independent complete-output repeated-addition oracle; repeated reach requires the literal inside the exported loop; includes vector arithmetic, equality and Host costs |
| `relation_rows` | Actual table residuals for quadratic and coupled constraints; varying height/width, valid and perturbed traces | Independent complete residual oracle, including inactive slots; Bundle admission, result checks and Host costs included |
| `curve_operation` | Separately named BLS12-381 G1 vector scaling, per-point scaling and MSM; 1/33/128 points | Includes point generation and every result check; weaker group-law consistency, sharing native group kernels |
| `kzg` | Generic KZG evaluation/quotient on checked roots-of-unity evaluations; on/off-domain, BLS Fr sizes 1/8/64/256/1,024, a bit-reversed control and KoalaBear size 32 | Independent coefficients, Horner and synthetic division; every quotient entry checked, including the derivative at an on-domain point; no pairing or commitment |
| `eip4844` | Actual 4,096-scalar blob commitments, openings, point/single/blob-batch verification; 1/4/16 blobs | Authored library against c-kzg 2.1.8; exact bytes and independent cross-verification; different SDK/API validation boundaries and normal resource limits |
| `curve_family` | BLS12-381 and BN254 G1/G2, Ristretto and prime Edwards; fixed-base source multiplication, shared-scalar/per-point scaling and MSM; 257-point scaling controls cross the Arkworks chunk boundary | Python scalar expectations plus shared-provider group-law self-consistency; includes point construction and checks, without an independent curve-coordinate oracle |
| `sparse_matrix` | Controlled dimensions/nnz and uniform, clustered or empty-row distributions; forward, transpose and bilinear contractions; prime, extension and binary fields | Independent complete-output Python contractions with dense extension coordinates; bilinear includes singleton/long-row controls; no full R1CS proof or enlarged capacities |
| `opening_quotient` | Current `deep_columns` versus explicit per-opening quotient/accumulate; KB/Ext4/Ext8, selected columns, repeated/distinct off-domain points | Identical inputs; independent coefficient/Horner/quotient expectations, all accumulated coordinates and final weight checked; checked setup and output construction inside SDK/run |
| `hash_bytes` | SHA-256 over 0/64/8,192 payload bytes | Independent Python `hashlib` digest; all bytes checked |
| `poseidon` | Width-16 KoalaBear Poseidon2, 1/17/256 states | Published Plonky3 known answer repeated per state; full batch check, one distinct state |
| `merkle` | Poseidon2 base-row trees; separate height/row-width sweeps, single and pruned multi-openings | Independent expected rows and changed-row rejection; root/path authentication shares the provider |
| `host_vector` | Matched KoalaBear input length/sum controls at 16,384/65,536 elements | Linear Python expectations; selected Host/Function ingress, default capacities |
| `scan` | Scalar ordered scan and bulk prefix sum; 17/1,024/4,096 elements | Full output check; source-form comparison, no presumed storage-release benefit |
| `control` | Rectangular nested loops, branches, indexing and carried state | Independent of machine libraries; not an unseen statistical holdout |
| `matrix` | Rectangular matrix-vector multiplication, dense and sparse occupancy | Python expectations; R1CS-like arithmetic, not a full proof system |
| `polynomial` | Dense coset evaluation/interpolation, base and degree-eight extension, 32–8,192 elements | Every evaluation and recovered coefficient checked; includes equality work |
| `extension` | Dense degree-eight extension multiplication, 1/17/1,024 elements | All coordinates vary; no general claim about other extension towers |
| `curve` | BLS12-381 point generation, vector scaling, MSM | Composed workload; scalar identity oracle shares native group kernels |
| `pairing` | 2/8/32 BN254 pairings and scalar multiplication | Bilinearity consistency, not Groth16/KZG or independent kernel validation |
| `transcript` | Independent round-count and payload-size variation | Ordered challenge recurrence and payload check; Merlin construction |
| `fri` | Domain size, dense polynomial degree bound and query count vary separately | Same-stack proof validation; degree bound is not domain size |
| `air` | Trace height, width and evaluation blowup vary separately, including original independent recurrences and new coupled quadratic/cubic columns | First/last/transition constraints; one table; default execution capacities |
| `stark` | The `air` shapes through the [parameterized library](../../libraries/arguments/stark/README.md#parameterized-single-table-argument), retaining KoalaBear quartic FRI and octic Merlin draws; additional bounded BabyBear quartic and Goldilocks quadratic configurations | Independent integer recurrence and same-stack proof verification; exact field/hash/transcript profiles, constant final polynomial; no external proof compatibility or field-only performance attribution |
| `bulletproofs` | BP+ source workload, counts 1/3/8/16; changing statements and preparation policies | Retained conformance inputs; independent comparisons remain in `monero` |
| `machine` | LogUp/grand-product, optional memory absent/present; bounded CPU/program and memory heights | Existing `ThreeTableArgument` and external accumulator interpreter; same-stack proof checks, not production zkVM scale |

The [source catalog](bench/coverage.py) records exact dimensions, operation mix,
category and limitations. Each run also records its oracle, input identities and
generated source/asset digests.
The two total finite forms use one explicit `math fn`, so collect and fold share
a numerical unit. Ordinary function calls can introduce separate ordered units;
collect–fold composition does not cross those boundaries.
Python oracles execute outside the SDK timer. They use dense deterministic field
values, including nonzero higher extension coordinates; the curve and pairing
controls explicitly use weaker algebraic consistency checks.

The additional `stark-baby-bear-quartic-poseidon2-16-*` and
`stark-goldilocks-quadratic-poseidon2-8-*` cases use the existing
`baby_bear_quartic::Poseidon2` and `goldilocks_quadratic::Poseidon2` library
configurations. Their exact extension fields are `baby-bear.ext4-binomial11`
and `goldilocks.ext2-binomial7`; their Merlin suites are
`merlin3.baby-bear.ext4-binomial11.rejection31le/0` and
`merlin3.goldilocks.ext2-binomial7.rejection64le/0`. Poseidon2 widths are 16
and 8, and coset shifts are 31 and 7, respectively. Shape metadata retains
these selections and each characteristic before compilation. Each field has
11 fixed cases: independent quadratic columns and coupled quadratic/cubic
columns, heights 8/32/128, widths 1/2/4/8/16, blowups 4/8 and eight queries.
The largest trace has 512 base elements and the largest evaluation domain has
512 rows. Each shape matches an existing KoalaBear recurrence control, with
all arithmetic reduced modulo its selected characteristic. The existing KoalaBear
cases and smoke list stay fixed. Changed statements and canonical claim mutations
use the selected modulus and coordinate width. These are composed SDK/Host proof
workloads under normal capacities; field, hash and transcript all change between
profiles, so a ratio cannot isolate arithmetic throughput. They provide no external
STARK byte compatibility or independent security result. BLS provider, Monero and
EIP-4844 comparisons keep their separate contracts.

### Fixed numerical panel

The numerical panels vary expression shape, field operations, transforms, cosets,
curves and coupled AIR/STARK constraints. Case counts imply no suite weights.

The `coset_batch` panel uses identical inputs across its two source
forms. It separates batch width, transform height and layout conversion. The
per-column form retains explicit interpolation/evaluation and concatenation;
the library form follows the current column-extension implementation. These are
source-to-execution comparisons, not isolated provider transform timings.

The separate `coefficient_batch` family starts from BN254 coefficients, without
interpolating evaluation words. Its fixed panel pairs `batch` with
`padded-columns` on exactly the same input polynomial, shift 7 and complete
output. At output size 64, coefficient heights 15/16/17 straddle the pinned
Arkworks 0.6.0 degree-aware FFT condition `4 * coefficient_count <= output_size`;
height 64 supplies a dense control. At output size 4,096, heights 17 and 4,096
each use widths one and three. At output size 32,768, heights 1,024 and 32,768
use width one. This keeps the flattened expected output within the ordinary
Host's 32,768-element logical array limit. Larger multicolumn domains require
separate input design; the harness does not raise capacities or silently resize.

The padded control slices each coefficient column, appends explicit zeros to
the output height and calls public `coset::evaluate_batch` with width one and
that full coefficient height. This reaches the ordinary full-length FFT while
retaining the same polynomial and evaluation order. Going through
`polynomial::from_coefficients` would trim the zero tail and erase the control.
The source loop, padding, slices and concatenation are part of its cost.
The Python oracle independently evaluates all output points with modular
radix-two arithmetic; focused tests cross-check it against Horner at every point.
Both source forms check full vector length and equality before returning their
boolean acceptance result. These are SDK/Host measurements with output
construction and checking, not isolated FFT or publication timings.

Select a matched pair, using already-built tools and a new output directory:

```sh
python3 common/benchmarks/run.py run \
  --case coefficient-batch-bn254-h17-w3-n4096-batch \
  --case coefficient-batch-bn254-h17-w3-n4096-padded-columns \
  --compiler build/compiler/zkc-compile --runtime target/release/zkc \
  --worker target/release/zkc-benchmarks \
  --output build/experiments/coefficient-batch
```

The larger `field-vector-{kb,fr}-add-1024` and
`field-vector-{kb,fr}-hadamard-8192` cases retain dense, distinct inputs and
check every output element through `vector::equal`. They expose larger native
result construction within the existing SDK/run boundary. Equality and Host
costs remain included; returning a boolean does not replace the full vector
check with a reduction or checksum.

The `vector_literal` family extends the `literal` generator with typed vector
values. `vector-literal-{kb,fr}-n1024-17-{constant,operand}` pairs 17 executions
of one literal site with captured operands; `vector-literal-{kb,fr}-n8192-1-{constant,operand}`
pairs first reach at a larger vector size. Each form receives identical decoded
inputs and independently computed expectations for every result element.
Inspect the exported `zkc.program/0` before interpreting repeated preparation:
the `vector.constant` operation must remain inside the `for` body. Invariant
hoisting would invalidate that interpretation even if the source contains a
literal in the loop. Observe reached-site counts separately with an instrumented
worker and `--execution-counts`; count runs do not supply timing comparisons.
If a compiler moves the literal, keep repeated preparation in a Native probe.
SDK calls reset invocation-local preparation, and the source cases include
vector addition and equality, so neither form measures parsing alone.

[`expressions.py`](bench/expressions.py) defines short/deep Horner, independent
branches, shared intermediates, capture-heavy and input-heavy Math bodies with
separate scalar oracles. Representative sizes include empty/singleton inputs,
31/32/33 and 127/128/129 tails, and larger columns, across six fields. Extension
coordinates are dense; binary fields use canonical hexadecimal inputs and the
captured [Python reference](../tests/support/binary_reference.py).
`difference-products` and `alternating-powers` have fixed
`dimensions.role = validation-only`; keep them out of tuning. The role is
metadata: `--suite expression` includes both roles. Inspect the captured lowered
IR before attributing performance to the authored expression's shape.

[`operations.py`](bench/operations.py) isolates named operations in source.
Transform directions use independent Python evaluation, rather than validating
a native roundtrip. Coset controls separately enumerate points and fold arbitrary
evaluations over base, quartic and octic fields, using dense extension shifts.
Their integer oracle follows the public subgroup convention and checks every
coordinate; folding does not assert a degree bound. Curve controls use weaker
scalar/group-law checks. Point generation, polynomial adaptation, validation and
Host costs remain inside the SDK timer; these are **not kernel-only timings**.
Separate hash/Merkle controls are described below.

The `air-coupled-*` and `stark-coupled-*` pairs share Bundles and traces with
simultaneous updates `next[j] = current[j]^(degree-1) * current[(j+1) % width] +
current[(j-1) % width] + j+1`. First/last constraints cover every column.
Quadratic cases vary height and width; the cubic case uses blowup eight.
Ordinary Python arithmetic generates the trace independently of the Bundle.
Negative controls check interior and boundary violations.

Default capacities stay unchanged. Generator tests check arithmetic and input
sizes; compilation, lowered-IR inspection and native resource admission are
separate validation steps. Production-scale traces, Host-limit stress and
larger multi-table scaling remain additional experiments.

### Public algebra library panels

[`library_algebra.py`](bench/library_algebra.py) generates the public algebra
panels, including `quotient_split` and `relation_rows`;
[`operations.py`](bench/operations.py) supplies `literal` loops. Select families
with `--suite`; the catalog owns exact dimensions, without aggregate weights.

KZG calls the actual [generic library](../../libraries/commitments/kzg/README.md),
separately measuring `evaluate` and `quotient`. Every call constructs an admitted
`EvaluationDomain` using `two_adic` or `two_adic_bit_reversed` and an
`Evaluations` view with equal extent.
Both constructors execute inside the SDK call. The off-domain point is 13;
the on-domain point is the middle stored root. BLS Fr sizes are 1, 8, 64, 256 and
1,024; a size-256 bit-reversed panel checks stored-root order, and a KoalaBear
size-32 control exercises the generic field boundary. Dense
coefficients independently generate inputs and Horner claims. Synthetic division
generates quotient coefficients, then evaluates them at every stored root,
including the derivative entry on domain. Quotient cases check both the returned
value and every quotient entry. This is evaluation/quotient algebra, without
commitments, trusted setup, pairings or a KZG security claim.

Curve cases cover BLS12-381 and BN254 G1/G2, Ristretto and prime Edwards, using
each group's associated scalar field. The common small-vector panel covers all
four forms; separate size controls include 257-point shared-scalar/per-point
scaling across the Arkworks chunk boundary. Fixed-base means an authored
`curve::collect` of generator multiplications; it selects no dedicated fixed-base
native kernel.
Shared-scalar uses `curve::scale`, per-point uses `curve::scale_each`, and MSM
uses `curve::msm`. Points are generated inside the call, with zero/unit factors
in the larger cases. Python computes the expected scalar of every result;
source checks each point through a group-law identity involving the generator.
These are explicitly **shared-provider self-consistency** oracles, without
independent curve coordinates, timing benefits or security claims. Ristretto and
Edwards remain distinct nominal groups despite sharing a scalar field.

Sparse cases vary dimensions, nonzero count and uniform/clustered/empty-row
distributions through the public matrix APIs. BLS Fr includes matched forward,
transpose and bilinear contractions, empty matrices, and singleton/long-row
bilinear controls. Cross-field clustered panels exercise all three contractions
over BN254 Fr, KoalaBear and its extensions, and both binary fields. Coordinates
are unique and sorted; stored coefficients are nonzero. Independent Python
contractions check complete outputs, including zeros and dense extension
coordinates.

Opening cases use checked coset, column-batch, opening-descriptor, bound-opening
and accumulator APIs over KB, Ext4 and Ext8 with matched `library`/`reference`
forms. Heights range from 8 to 4096, widths from 1 to 8 and opening counts from
0 to 8, with separate singleton and empty controls. Points are all repeated,
all distinct, or mixed runs that also revisit earlier points; the catalog fixes
the individual shapes. Selected columns and rotations use explicit deterministic
orderings. All points lie outside the evaluation coset. Nonzero dense
initial values, first weight and ratio exercise accumulation and final-weight
progression. The reference explicitly loops over `coset::opening_quotient` and
`vector::accumulate`; the library calls `opening::deep_columns`. Both construct
the checked views inside the SDK call and compare every result coordinate plus
the final weight. The library uses one private weighted-quotient result; the
reference retains per-opening intermediates. The panel includes no
protocol-specific kernel or quotient-coefficient splitting.

All Python oracles run outside the SDK timer. They load no external data or
oracle files. The scheduler captures the executing generator and arithmetic
module, generated inputs, and transitive library modules/manifests from the
selected `--source` root. Incorrect controls change one expected field coordinate
and preserve typed inputs and lengths. The panels stay below the default Host
input/collection ceilings without capacity overrides. Generator checks establish
bounded input sizes and arithmetic; real compilation and native resource
admission remain separate checks required before publishing measurements.

### Hash, commitment and input controls

The catalog records category, dimensions and operation mix for hash, permutation,
Merkle, bounded machine and Host input controls; generated Programs supply the
captured oracle.

[`commitments.py`](bench/commitments.py) uses the public byte hash, permutation
and row-oracle APIs. SHA-256 checks every digest byte against `hashlib`.
Poseidon2 repeats Plonky3 0.8.0's published KoalaBear answer across each batch;
this is a retained known-answer control, not independent random-state coverage.
Every Run also supplies an incorrect expected result to the acceptance gate.

Merkle single-opening shapes `(height, row_width)` are `(16,1)`, `(256,1)`,
`(16,8)`, `(16,9)` and `(13,9)`. These separate tree size from leaf payload,
cross the eight-coordinate sponge rate, and include padding. A sixth case uses
the `(256,1)` tree with four positions, including an out-of-order position and
a duplicate. Each call commits, opens, checks every returned row against Python
row-major expectations, authenticates it, and requires authentication of a
canonical changed row to return false. Root/path checks use the same provider;
there is no independent Merkle-root oracle or binding/security claim. Timings
include commitment, opening, positive/negative authentication, equality and Host
work; they do not isolate a tree-building or opening kernel.

The machine additions reuse the fixture's source, captured Bundle, imperative
interpreter and input preparation. Both LogUp and Product vary CPU/program
height 8/16 with memory absent. Two LogUp cases hold CPU/program height 8 and
the same four memory events fixed while varying present memory height 16/32.
A matched arithmetic-only LogUp case enables an idle memory table while keeping
the program, CPU witness and final value equal to the height-8 absent case. The
active-memory cases also change the instruction mix and do not isolate presence.
The existing profile stays at maximum log height 5, log domain size 6, five
rounds, eight queries, eight attempts, two channels and shift 3. Changed-final
statement and canonical-claim mutation checks use the existing proof controls.
The Bundle supports CPU/program heights 4/8/16 and memory heights 8/16/32;
larger heights or arbitrary table arity need a separate supported relation and
profile. These controls keep fixed inputs and do not establish proof security.

The large input controls use identical dense vectors for length and sum. Their
Python expectations take linear work. Length exposes input adaptation and
admission with minimal source work; sum adds one native reduction. The largest
case reaches the default 65,536-element collection ceiling. JSON requests fit
the existing 16 MiB document and 200,000-node bounds; no capacity is enlarged.
Decode/request construction and SDK/Host execution retain their separate report
boundaries. Select `--ingress` for matched input-ownership comparisons under these
same capacities.

With the prebuilt tools from the Run section, select cases or suites explicitly:

```sh
python3 common/benchmarks/run.py run \
  --case hash-sha256-8192 --case poseidon2-kb-states-256 \
  --case merkle-poseidon2-h16-w9-single --case machine-logup-h8-m32-present \
  --case host-vector-kb-sum-65536 \
  --compiler build/compiler/zkc-compile --runtime target/release/zkc \
  --worker target/release/zkc-benchmarks --output build/experiments/selected-controls
```

Use `--suite merkle` or `--suite host_vector` for their small dimensional panels.
Normal runs execute validation gates before publishing timing summaries;
source compilation and generator tests alone do not establish runtime admission.

Broader coverage does not establish universal performance. Full Groth16/KZG,
recursive proving, production zkVM traces, other fields/hash families,
concurrent services and other CPUs remain separate experiments. Apply application
weights during interpretation, document them, and retain the unweighted rows.
Do not compare two workloads merely because both are called FRI or pairing.

## Changing statements and preparation

Source proof workloads can cycle distinct inputs through one admitted Entry.
Run workloads keep fixed inputs; `--input-count` does not change them:

```sh
python3 common/benchmarks/run.py run --case bulletproofs-3 \
  --input-count 3 --preparation both --warmups 3 --samples 9 --iterations 1 \
  --compiler build/compiler/zkc-compile --runtime target/release/zkc \
  --worker target/release/zkc-benchmarks --output build/experiments/reuse
```

Warmups and samples must each contain complete input cycles. Every invocation is
identified; reports retain first visits and repeated times **per statement** as
well as the declared schedule's aggregate. This is sequential reuse, not batch
verification. Every generated proof is checked against its own statement.

`--preparation enabled|disabled|both` selects matched source-proof jobs. Preparation
costs stay inside SDK calls; entries, retained bytes and hits are observed after
each call. `--preparation-entries N` and `--preparation-bytes N` independently
select the store's entry and byte bounds. Omitting either uses its native default
(currently 128 entries and 8 MiB). Zero disables retention. These controls permit
both saturation and larger working-set experiments without changing execution
capacities or native defaults. Requested limits are recorded in the contract; compare
capacity experiments separately from otherwise matched implementation timings.
Workers report the native default and the bounds passed to the Entry. Effective
limits are zero for disabled workers, including the unprepared half of `both`.
Statistics must respect those bounds; disabled preparation must retain no state.
Reports include final entries, retained bytes and hits. A bounded store need not
improve a workload, and hits alone do not establish a timing benefit. The machine fixtures support fixed inputs
only; BP+ uses at most four fixture patterns times the commitment count through
ordered permutations. Distinct public statements are checked before timing.
External comparison families retain their fixed-statement contracts and default
preparation policy.

## Input ingress

`--ingress json|wire|native|prepared` selects Host/Function input ownership (default
`json`), independently of `--preparation`. All modes use the captured named input
documents and the admitted interface's default physical codecs. Source run jobs
capture one `arguments.json` parameter map, such as `{"inputs":{"P":{...}}}`;
the worker request uses `backend.arguments` for its path. Static run children
receive explicit setup-free authority and benchmark sessions outside ordinary
source data. The timed `admitted_function_call` boundary is the complete shared
`FunctionEntry.prepare(...).execute()` call. Capture, admission, decoding, request
construction, return-value inspection and final diagnostics retain their separate
measurement boundaries. Proof jobs retain public/witness groups and native proof
preparation measurements.

| Mode | Input construction |
|---|---|
| `json` | Bounded named decoding before every call |
| `wire` | Decode once per statement before warmups; retain canonical frames in shared `Arc<Vec<u8>>` owners |
| `native` | Decode once, then use the native decoder and validator to retain typed immutable Values |
| `prepared` | Decode once, then use `PreparedData::from_wire` to retain decoded data and its canonical encoding |

Preowned modes retain one input tree per statement, run the admitted Entry's `check_inputs`
during construction, and share data owners when constructing each request.
Every SDK call still performs ordinary binding, quota, loading and authority
checks. No execution plan or protocol result is retained by ingress selection.
Conversion preserves products, associated values and active variants. Native
and Prepared conversion require duplicable, wire-encodable, setup-independent
leaves; resource/key descriptions retain their existing constructors. The worker
Decoder has no file resolver; unsupported conversions refuse. Document/inline
limits apply across the input groups of each statement; execution capacities are
unchanged.

The current `zkc.benchmark/0` manifest requires `ingress`.
`zkc.benchmark-worker/0` requires Host/Function backend `ingress`, report
`lifecycle.ingress`, `lifecycle.input_setup`, and each call's `input_index`,
`decode_ns` and `request_ns`. JSON has an empty `input_setup` and numeric
`decode_ns`; preowned modes have null `decode_ns` and one ordered setup row per
statement. Each row contains `input_index`, `construction_ns` (decoding,
conversion and input preflight) and `retained_payload_bytes`. Payload sums
ordinary converted leaves: Wire frame lengths, Native retained-value bytes, or
Prepared decoded-plus-canonical bytes. It excludes constructor material, input
documents, proof buffers, request-tree metadata and allocator overhead. It is
neither RSS nor allocation traffic and does not deduplicate shared occurrences.

External reference workers keep their existing ingress defaults; only their
Host counterpart receives the selector. Contracts and reports record this
asymmetry as `reference defaults`.

## Measurement boundaries

| Metric | Boundary |
|---|---|
| Package capture | Authentication/capture after reading package bytes |
| Admission | Native Entry admission after capture; the existing `admission_ns` total is capture + admission |
| Input construction | Preowned `input_setup[].construction_ns`, once per statement before warmups |
| Decode/call | Bounded named JSON decoding from preloaded bytes; `decode_ns` is null for preowned modes |
| Request/call | `request_ns`: named request construction, including sharing the preowned input tree where selected |
| SDK call | Input adaptation/admission, execution, service lifecycle and named output reconstruction; source controls also execute their result checks |
| First call / first visit | First invocation in a worker / first invocation for each statement, including warmup calls |
| Final diagnostics | One materialization after the last SDK call, measured separately |
| RSS snapshots | OS-reported worker lifetime high-water marks before/after final diagnostics and before serializing the final report |
| Process wall time | Entire worker, including setup, all calls and evidence writes |
| Compilation | External comparison: repeated CLI compilation; source controls: one compiler-process observation, excluding generation |
| CLI observation | Separate proof process including I/O and admission; exploratory, external comparison cases only |

Do not add medians of different boundaries to estimate end-to-end latency. Peak
RSS is not incremental allocation or live VM storage; retained inputs, allocator
state and observations contribute. These snapshots precede final report JSON
serialization; they are not an external measurement of the entire process peak. OS accounting can
be approximate. Runtime work counters describe the final call, not an allocation
profile. Intrusive profilers are separate experiments and must not supply release
latency rankings or causal percentages by subtraction.

Reference clients decode before their loops. Production protocol temporaries are
destroyed inside the call timer; returned reports/proof buffers are consumed
outside it. Only the final Host report is retained. Proof files are written
outside the SDK timer and verified after all timed workers finish. Input decoding,
proof I/O and observation still affect process time and memory. No caches are
flushed; preparation and correctness checks can warm system caches. The timer
floor is recorded and never subtracted.

## Execution counts

For runtime attribution, build a separate worker with execution observations.
Function jobs report native execution counts merged across reached numerical
calculations and child runs/proofs. Host control and non-native work are outside
those counts. Native proof jobs report their native invocation counts. These
instrumented builds are separate from release timing runs.

Build the observation worker with:

```sh
cargo build --release --locked -p zkc-benchmarks --features execution-counts \
  --target-dir target/counts
python3 common/benchmarks/run.py run --preset execution --execution-counts \
  --compiler build/compiler/zkc-compile --runtime target/release/zkc \
  --worker target/counts/release/zkc-benchmarks \
  --warmups 0 --samples 2 --processes 2 --output build/experiments/counts
```

The harness requires the requested feature state and source workloads, permits at
most 128 calls per worker, and omits timing summaries and comparisons for these
runs. Raw clock readings remain diagnostic evidence. Default runtime builds have
zero-sized counters; enabling the Cargo feature adds storage and observation
work. Counts reveal reached control flow, so they are host diagnostics, not a
public-information projection.

`lifecycle.calls[].execution_counts` contains fixed event counters and native
invocations grouped by operation contract. The histogram combines instantiated
types and implementations of a contract; workload dimensions and captured
artifacts retain those distinctions. Do not infer a universal cost per call. Snapshot construction happens when
Host collects completion reports; JSON materialization happens after the SDK
call. Each participant and attempt contributes once. Reports retain per-input
first visits and deduplicate equal repeated vectors with their multiplicities.
`counts_repeatable` compares complete ordered count sequences across processes
(`null` with only one process);
variation must be explained before fitting a deterministic cost model.

| Counter group | Unit and boundary |
|---|---|
| `charged_instructions`, `replayed_instructions` | Successful instruction charges executed directly or replayed from public preparation; their sum equals resource instruction usage |
| `local_*` | Reached local instructions after a successful charge; `local_release` is an uncharged storage instruction |
| Native operation histogram, `native_operand_values` | Actual backend invocations and top-level operand values copied into invocation scratch |
| `created_frames`, `backend_enter_calls`, `backend_leave_calls` | Actual frame construction and attempted backend boundary calls; successful execution balances enters/leaves |
| `value_validation_calls`, `backend_validation_calls` | Runtime validation and backend validation requests; exclude checks performed internally by a backend |
| `retention_plan_calls`, `retention_planned_values` | Ledger planning requests and their top-level input values |
| `retention_commit_values`, `retention_release_values`, `retention_unpin_values` | Top-level ledger references, including return pins and replay; not heap allocations |
| `computation_reuse_hits` | Successful public computation replay |

Counts include validation and planning performed by explicit Host preflight calls such as delivery checks; they describe the actual Host invocation, not a minimal abstract schedule.

Counts alone do not identify time costs. Use clean release measurements on the
same artifacts and inputs, and report correlated counters when they cannot
separate candidate causes. No per-operation clocks or allocator interception are
installed. Failed Runner initialization has no snapshot; this mode measures
successful benchmark calls rather than failure profiles.

## Correctness and evidence

External comparisons cross-verify both directions and check deterministic proof
identity or randomized proof uniqueness. Source proofs use same-stack verification
and separate format, changed-statement and semantic controls. Semantic controls
use an invalid witness under the same public statement (FRI/transcript), a
canonical claim mutation (AIR/machine), or a canonical response mutation (BP+). The FRI control evaluates a polynomial one degree beyond the allowed bound.
Each refusal is tested in a fresh Entry and after one valid call
in the same Entry. Changing-input schedules also test a swapped proof. Every timed verifier
must accept; every produced proof, including warmups, is retained and validated.
Run programs must return a typed `accepted = true`; every source Run control also
tests a generator-supplied incorrect expectation at that acceptance gate. These are bounded execution checks,
not proof-system soundness results.

Controls check the observed refusal layer: framing for malformed proofs, binding
or verification for changed statements, and verification for semantic mutations.
Raw proof codecs perform format checks in the authored verifier, so those
controls require a verification refusal instead. The compiled Entry selects the
format. The worker records the error code and stop kind. Known format refusals include
the driver's subsequent cancellation. Truncation also permits the separately
recorded bounded-byte-read refusal, which alone does not identify the buffer read.
Failed calls retain effective preparation limits and statistics before and after
the refusal; the same capacity checks apply to successful and refused calls. Some
workloads have no eligible preparation, and early format failures need not reach
a prepared operation; a preceding successful call alone does not prove a hit.
Crashes, timeouts, unrelated cancellation and resource-limit failures do not pass.
Any failed gate, incomplete matrix or changed captured input invalidates the whole
run's timing summaries and comparisons. Failed evidence is retained.
Saved reports validate every retained worker, including in failed or interrupted
runs. Backend requests and proof artifact records use the current exact schema;
artifact paths, sizes, digests and input schedules remain part of the evidence.

Outputs include `plan.json`, `manifest.json`, `coordination.json`, reports in
Markdown/JSON/CSV, captured sources/inputs, packages, every produced proof and
command journals. An append-only `progress.jsonl` records worker completion; full
reports are written at phase boundaries, outside the timed worker sequence.
Summaries use medians of process medians. Paired ratios are
descriptive, not significance tests; no timing threshold decides correctness.

```sh
python3 common/benchmarks/run.py report RUN/manifest.json --output NEW_REPORT
python3 common/benchmarks/run.py compare BASELINE/manifest.json CURRENT/manifest.json
```

Cross-run comparison requires matching contracts, sampling and host metadata.
Binary hashes identify selected executables; adjacent source revisions do not
prove build provenance. Worker optimization facts do not certify every dependency.
Performance environment variables are allowlisted; dynamic library closures and
unrelated host activity are not captured. Publish measurements with retained evidence.

## Extension and validation

[`workloads.py`](bench/workloads.py) and [`suites.py`](bench/suites.py) own external
comparisons. [`coverage.py`](bench/coverage.py) and [`execution.py`](bench/execution.py)
own source cases. Both use [`runner.py`](bench/runner.py), [`io.py`](bench/io.py),
[`results.py`](bench/results.py), and the generic
[`zkc-benchmarks`](../../crates/zkc-benchmarks) Host worker. Add an ordinary source
workload and oracle, not a production protocol-specific executor.

[`protocol_math.py`](protocol-math.md) retains its distinct compiler-policy/CLI
comparison contract and shares the journal and optional execution lock. Research drivers
remain supporting evidence. This design follows worker/warmup separation in
[pyperf](https://pyperf.readthedocs.io/en/stable/run_benchmark.html) and explicit
boundaries/interleaving in [Google Benchmark](https://google.github.io/benchmark/user_guide.html).

```sh
cargo test --locked -p zkc-benchmarks
uv run --no-sync --locked pytest common/tests/harness/test_benchmark*.py \
  common/tests/harness/test_protocol_measurements.py \
  common/tests/harness/test_processes.py
uv run --no-sync --locked ruff check common/benchmarks
python3 common/tests/check_docs.py --all
```

Unit checks cover oracles, catalog dimensions, locks, lifecycle evidence, process
failure, incorrect acceptance, input identity and complete-run summaries. Real
benchmark matrices are opt-in and require the selected built tools.

## Compare build profiles

Use the existing scheduler with named root profiles:

```sh
python3 common/benchmarks/run.py run --preset=execution \
  --case=finite-kb-collect-17 --processes=2 --samples=3 --warmups=1 \
  --compiler=build/compiler/zkc-compile --runtime=target/release/zkc \
  --worker=target/release/zkc-benchmarks --profile-project=zkc.toml \
  --profile=default --profile=vector --output=build/profile-comparison
```

The manifest must define `profile.vector`; `default` selects root `[build]`.
At most 16 distinct candidates are accepted. Profile candidates cannot combine
with `--compiler-option`. Each candidate gets its own ordinary run manifest,
correctness/refusal controls and samples; `candidates.json` links requests and
results under separate `requests/NAME` and `candidates/NAME` directories. All
candidate settings resolve before measurement starts. Effective values and
origins are retained as `configuration`. There is no weighted aggregate or
automatic selection. Existing ingress, process, input,
preparation and coordination options apply unchanged.

Generated source controls retain a separate compiler observation and published
package policy. Compilation is outside runtime samples; its observation-enabled
wall time is labelled and must not be compared with uninstrumented compilation
as if the measurement boundaries were equal. Runtime counts remain a separate
observation mode, with the existing restrictions on timing comparisons.

## Provider and conversion controls

The `bls_provider` suite compares Arkworks and blst G1/G2 scaling, MSM and
pairing-product checks on deterministic full-width inputs. Use `list` to choose
cases or select `--suite=bls_provider`. The existing process scheduler alternates
providers and retains every request and result.

`resident_kernel_call` starts with each provider's resident values.
`converted_kernel_call` directly times import, arithmetic and export from the
shared Arkworks representation. `installed_operation_call` executes the selected
binding through the VM and Native, including resource admission and output
publication; program admission and Runner construction occur before the timer.
For blst, this boundary has Arkworks entry and output ports and explicit
`native/representation.convert` calls around `blst/resident` arithmetic.
`provider_import` measures point and scalar import, while `provider_export`
measures point export. These conversion-only cases contain no arithmetic. Never
add their isolated medians to estimate a complete call; measure that boundary
directly. Every result is compared with Arkworks outside the timer, including
warmups; input generation, JSON I/O, checking and returned-result destruction are
excluded. blst's worker pool is disabled, and MSM is variable-time. These are
operation controls, not protocol throughput or security measurements.

Cases with `resident-chain` and `converted-chain` measure the same four-operation
computation at the direct kernel boundary (conversion once around the chain in
the latter). `resident_installed_chain` repeats the selected operation four times on Native
resident values. `wire_decode_resident_execute_wire_encode` additionally times
selected wire decoding, Runner construction, output encoding and Runner teardown.
Both include Runner teardown; both admit programs and generate/check mathematical
oracle values outside timing. Backend construction is excluded from the wire boundary.
These are selected entry codec controls; no protocol message transport, transcript
or whole-protocol execution is measured.
Select these cases with names containing `resident-installed-chain` or
`wire-resident-chain`. Scalar field/vector, G1/G2 and pairing cases cover small
and large inputs. Scaling and scalar products feed each result into the next
operation; MSM chains accumulate repeated MSM outputs with resident curve addition;
pairing chains return every Boolean for checking. No intermediate representation
conversion is inserted in resident chains.

Scalar-vector multiplication includes 8,192 and 32,768 elements for both curve
families, covering the shared vector kernel's parallel chunks as well as small
calls. The direct Arkworks controls use the same typed destination kernel as
Native; their result checks use scalar loops outside timing. Curve scaling and
MSM results are checked using element-wise Arkworks multiplication and addition,
without reusing the measured bulk plan or MSM. These checks share Arkworks scalar
and group primitives and are not independent curve-coordinate implementations.
Operands and base-point coefficients use distinct deterministic hash domains,
so reversing a single-step vector result is observable. Direct point-valued
controls retain inline points for both providers; observer-only singleton vectors
are constructed outside timing. Setup constructs foreign input storage only for
the resident or export controls that consume it. The converted installed panel
stops at 8,192 vector elements so explicit conversions fit Native's default work
allowance; direct and resident-chain panels also include 32,768 elements.

Worker diagnostics retain the admitted straight-line program, exact physical
ports, chain length, arithmetic calls, explicit conversion directions/counts,
elements and canonical payload bytes (excluding framing), and native wire byte
counts. Conversion counts describe reached program occurrences, not allocator
instrumentation. Native selected codecs construct resident values through
`decode_native_value`; direct wire paths need no Arkworks value construction
inside timing. MSM requires explicit trusted variable-time authorization.
Provider workspace admission bounds (where available) are declared limits rather
than observed allocation peaks. Managed input retained-payload charges and terminal Runner usage are reported
separately from process lifetime peak RSS. Public APIs currently expose no
retained/scratch high-water counters, so those fields are null; cumulative fresh
payload is not a peak, and provider-hidden allocation is not allocator-traced.

For exploratory resident measurements use `--processes=3`, bounded build workers
(`cargo build --release --locked --jobs=2 -p zkc-benchmarks`) and the existing
scheduler without `--exclusive`. Preserve each process's samples and variability;
these operation/control measurements do not establish protocol throughput.

## Browser module and proof-client observations

The `browser` adapter uses prepared ordinary `ProofClient` cases, the same
`Capture`/`Journal` evidence owners and optional measurement lock as native
benchmarks. Supply prebuilt portable `pkg/` and, for matched SIMD runs,
`pkg-simd/` alongside the production client and Worker modules. It downloads no
tools or browsers. Playwright is pinned to **1.64.1**, matching the manual browser
roundtrip check. Each process repetition starts a fresh Chromium process.

```sh
python3 common/benchmarks/run.py browser-fixtures \
  --compiler build/compiler/zkc-compile --output build/experiments/browser-fixtures
python3 common/benchmarks/run.py browser \
  --web /absolute/path/to/web --cases build/experiments/browser-fixtures/cases.json \
  --node /usr/bin/node --playwright /absolute/path/to/playwright/index.mjs \
  --variant portable --variant simd --revision SOURCE_REVISION \
  --processes 2 --samples 5 --warmups 1 --output build/experiments/browser
```

`browser-fixtures --source-only` generates source and inputs without compiling.
`--case NAME` selects controls. The panel reuses the existing checked vector,
transform and FRI generators, the retained independent Keccak reference, and
Plonky3's Poseidon2 known answer. Goldilocks base/extension empty and tail lengths,
small NTT/FRI, distinct Poseidon2 states, scalar Keccak, Keccak row commitments at
the two-lane 32 KiB staging neighbors, blst G2/pairing, and byte publication are
separate cases. The wrapper for local computations uses an authored proof Entry
whose verifier repeats the public computation; these are workload controls with
no cryptographic security claim. Distinct Poseidon2 compares every batch result
with scalar calls and checks the first state against the retained known answer.
The row commitment controls cross-verify scalar/batched root/path proofs across
variants; they do not have an independent root oracle. Source equality checks
and conversions remain inside the SDK call.

`quartic-keccak` combines the exact KoalaBear quartic row scheme and hash-chain
challenge suite in one row-opening proof. All four coordinates are nonzero.
The manual browser roundtrip checks exact native/browser proof bytes and
context, framing, input and budget refusals; this does not establish a complete
STARK client or a cryptographic security claim.

External prepared fixtures use one exact case document, with paths relative to
that document (and statement/material paths relative to the case directory):

```json
{"format":"zkc.browser-cases/0","cases":[
  {"name":"schnorr","directory":"fixtures/schnorr","providers":["arkworks","blst"],
   "options":{},"statements":[{"public":"public.json","witness":"witness.json"}]}
]}
```

Each directory supplies `entry.zkpkg` and an independently recorded SHA-256
`pin.txt`; the adapter checks the candidate against that pin. `providers` is
required and identical for both module variants. Installation restriction does
not exclude compiled dependencies. Optional `authority` names an independent
`zkc.entry-setups/0` document, `setups` is `[{"slot":"key","path":"vk.bin"}]`,
and `bindings` is `[{"name":"pk.bin","path":"pk.bin"}]` for ordinary opaque
`setInput` bindings. The SDK retains semantic decoding, pin checking and setup
authority. Multiple statements run a complete round-robin cycle in every warmup
and sample. `expected_outputs` optionally names a full verifier output document.

`browser-fixtures --setup-material DIR` additionally reuses the compiler's
existing two-slot PCS source fixture with actual development key material. DIR
supplies `public-0.json`/`witness-0.json` and a distinct `-1` statement,
`authority.json`, `setups.json` and `bindings.json`; material paths in the latter
two arrays are relative to DIR. Key generation is an explicit preparation step,
never browser benchmark setup or a trusted ceremony.

Add `--native-example /absolute/path/to/memory` for native/browser proof
cross-verification in both directions for every variant and statement. The
matching `zkc-web` memory example reads the same options, authority and opaque
bindings; its additional controls and complete report are retained. Native
process times have a different boundary and are not browser kernel ratios.

The default `--transport borrowed` preserves caller inputs. `--transport consume`
passes disposable input copies through the production consuming transfer API;
making those copies is included in client latency. Both modes require matching
outputs and proof verification. Neither mode isolates JS/Wasm copying from the
SDK call. The report records the observed page timer increment; intervals below
that increment cannot support fine speed comparisons.

Reports retain raw/gzip deployment bytes, exact physical bindings, module fetch,
`WebAssembly.compile`, instantiation inside glue startup, Worker readiness,
admission, setup-byte installation, first/repeated calls, encoded output sizes,
and a separate transferable MessageChannel calibration. HTTP is local and
uncompressed. Every measured Worker receives a precompiled module, including the
first case. Compilation can use browser engine caches; fresh Workers reset
mutable state, not code caches. `setSetup` timing is byte installation; semantic
output-key import is nested in SDK preflight, while input prover-key import is
nested in Host preparation inside the execute/cleanup interval.

Worker call time includes JS/Wasm conversion, SDK decoding/preflight, execution,
cleanup, encoding and report construction. It excludes result getters. SDK
instrumentation, when supplied, separately records package capture/admission,
document/codec/output-key preflight, Host preparation/import/execution/cleanup,
output encoding and diagnostics;
missing observations remain unavailable. Client latency also includes snapshots,
queueing, transfer, dispatch, getters and publication/delivery. Subtracting the
Worker call gives a residual containing all those costs, not an exact transfer
timer. These nested intervals must not be summed. Browser reports share `report`
republication; `compare` refuses their overlapping boundaries. Compare explicit
stage distributions in `summary.json`, retaining artifact and workload identities.
No whole-browser memory, constant-time or security claim follows from the panel.
