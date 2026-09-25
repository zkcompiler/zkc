# Whole application comparison: measured 2026-09-16

Both complete Rust producers and independent public-only verifiers executed
successfully on the exact application fixture inputs. These measurements
replace neither application's primitive-only records; they add the previously
missing **whole direct application** comparison. They do not close the rest of
the application composition or establish interoperability or production security.

Environment: AMD Ryzen 9 5950X 16-Core Processor, 32 logical CPUs,
Linux 6.8.0-139-generic x86_64/glibc 2.39, Rust/Cargo 1.98.0, Cargo default release
profile. Three samples per workload and role, serial measurement commands,
`--trace=none` for native artifacts, warm filesystem. Other agents/processes
could use the machine; no CPU isolation or statistical speedup claim is made.
All eight final records use binary SHA-256
`c632fa5fd9d2d1fe4072980900ccd8225fa5ace2c7bb944bbc17e39f681f6abc`
and Cargo.lock SHA-256
`501a650dffd5c4c98f66ebf84a6676849cc5d8940cffa0ae612fadcc3621ac17`.

## Complete proof work and bytes

Times below are medians in milliseconds. **Direct warm** includes complete
proving/verification and proof serialization/parsing with cached keys, parsed
inputs and public-root preparation. **Native run** is the existing host's
`timings.run_seconds` after artifact admission/key loading in each fresh process;
it is not a separately demonstrated persistent-host service. Both do actual
cryptographic work, not algebra-only evaluation.

| Workload | Prove ms, direct warm / native run | Verify ms, direct warm / native run | Bytes direct / native |
|---|---:|---:|---:|
| tx/final-n8-m2 | 2.047 / 29.455 | 0.532 / 4.382 | 772 / 1180 |
| tx/n16-m4 | 6.763 / 36.827 | 1.177 / 7.349 | 900 / 1428 |
| tx/n32-m8-k4 | 25.947 / 85.972 | 2.601 / 19.645 | 1172 / 1924 |
| tx/n64-m2 | 12.956 / 56.107 | 1.603 / 10.765 | 964 / 1456 |
| execution/tiny | 57.691 / 80.778 | 46.336 / 53.674 | 12725 / 12679 |
| execution/memory8 | 83.326 / 109.091 | 50.722 / 62.209 | 16049 / 15805 |
| execution/loop16 | 101.551 / 127.299 | 58.421 / 64.986 | 17513 / 17213 |
| execution/memory64 | 237.880 / 258.119 | 74.219 / 68.206 | 20441 / 20029 |

| Workload | Prove process ms, direct / native / native with app admission | Verify process ms, direct / native / native with app admission |
|---|---:|---:|
| tx/final-n8-m2 | 4.850 / 302.654 / 305.660 | 2.663 / 275.448 / 278.554 |
| tx/n16-m4 | 10.208 / 328.923 / 333.932 | 4.148 / 302.979 / 308.193 |
| tx/n32-m8-k4 | 32.388 / 480.292 / 494.339 | 8.383 / 415.948 / 429.699 |
| tx/n64-m2 | 16.747 / 334.725 / 342.272 | 5.721 / 287.181 / 295.446 |
| execution/tiny | 162.806 / 357.243 / 357.243 | 50.649 / 217.492 / 256.558 |
| execution/memory8 | 489.397 / 697.495 / 697.495 | 57.166 / 231.624 / 276.733 |
| execution/loop16 | 884.662 / 1104.449 / 1104.449 | 60.758 / 235.897 / 289.965 |
| execution/memory64 | 3453.910 / 3642.057 / 3642.057 | 83.064 / 275.658 / 371.647 |

The second table separates process costs. Direct processes include direct
application admission, file parsing, generator/key import, proof work and I/O.
Native processes include artifact admission and key loading; the third number
adds the application's admission helper. For transaction this runs the frozen
`prepare`/`admit` helper, generates an input envelope and checks ledger/parameters.
For execution verification it reconstructs public matrices using the existing
`check_public_bundle`; this prelude is recorded separately. Native execution
production consumes its original prepared envelope. Setup generation, compiling
source/claims, generating assignments, exporting relation matrices and acquiring
an authenticated ledger/configuration are outside these proof processes.
The native rows use the frozen fixture artifacts and tools, so they exclude
later claim and formal admission work.

The transaction proof is one combined proof including actual balance and all
owners, not range-only plus synthetic group work. Upstream fuses range/IPA,
uses optimized group calculations, and has a different encoding/transcript.
Consequently these timings compare ordinary direct-library author practice with
the full PIR route, not identical operation schedules or ABI overhead alone.
All output commitments/ledger facts/witnesses match the corresponding original
fixture, while proof randomness is freshly drawn for each sample.

Execution performs exactly one original commitment, five coordinate openings
(ONE plus four public values), three outer cubic sumchecks, three inner
quadratic sumchecks, and three final openings of that same original polynomial.
There are eight actual PCS checks. The old tiny setup helper's stored primitive
benchmark used six openings; **that old measurement is not used here**. Only its
original pinned keys are reused. Round counts per view are:

| Fixture | Original wires | Padded rows / columns | Outer / inner rounds | Final opening queries |
|---|---:|---:|---:|---|
| tiny | 154 | 128 / 256 | 7 / 8 | Three recomputed sumcheck points |
| memory8 | 863 | 1024 / 1024 | 10 / 10 | Three recomputed sumcheck points |
| loop16 | 1786 | 2048 / 2048 | 11 / 11 | Three recomputed sumcheck points |
| memory64 | 6631 | 8192 / 8192 | 13 / 13 | Three recomputed sumcheck points |

Both application proofs use their own complete serialization with EOF checks.
Byte counts include every commitment, message, evaluation report and PCS/range/
Schnorr proof. Public configuration bytes are excluded on both paths. No
pre-recorded challenges, synthetic residuals or PCS-only approximations appear
in the whole application rows.

## Setup, input and copy costs

These are milliseconds from the cached baseline process unless identified as a
three-sample median. Public preparation includes bounded JSON reads, admission,
public field/point decoding and transcript-root serialization. For transaction,
generator setup is a **subset** of public preparation. For execution, public
preparation includes verifier-key import; large prover-key import is separate.
Private input includes JSON/scalar parsing and execution assignment padding.

| Workload | Public preparation | Generator setup subset | Prover-key import | Private input |
|---|---:|---:|---:|---:|
| tx/final-n8-m2 | 0.680 | 0.405 | — | 0.025 |
| tx/n16-m4 | 1.226 | 1.004 | — | 0.017 |
| tx/n32-m8-k4 | 3.953 | 3.641 | — | 0.028 |
| tx/n64-m2 | 2.305 | 2.083 | — | 0.018 |
| execution/tiny | 1.194 | — | 100.172 | 0.041 |
| execution/memory8 | 2.367 | — | 387.548 | 0.098 |
| execution/loop16 | 3.939 | — | 782.887 | 0.243 |
| execution/memory64 | 12.090 | — | 3185.126 | 0.972 |

Separate current matching-arity OS setup generation medians are 8.124 ms (tiny),
18.812 ms (memory8), 30.723 ms (loop16), and 107.686 ms (memory64), three fresh keys
each. Those keys are discarded; comparisons retain each original fixture key.
The longer public prover-material import validates canonical group/subgroup
encodings and material/setup fingerprints. It is charged in both fresh-process
provers. Public matrix export (three compiler reads plus JSON/source staging)
took respectively 59.925, 81.083, 109.250 and 266.887 ms and is charged once,
outside proving. These staging numbers include Python/compiler startup.

Each warm execution proof still copies its original assignment into the adapter
table and creates three sets of mutable reduction vectors; those costs are in
proving. Every warm proof creates its own transcript state and complete byte
buffer, and every verification parses the complete byte buffer. Immutable
public setup/input caches are shared only between repetitions. Serialization,
field copies and root hashing are not silently reported as free algebra.

Maximum process RSS in the samples is 20,376 KiB for the direct memory64 prover
and 10,420 KiB for its verifier, versus 80,940/80,172 KiB for the native artifact
processes. Native RSS includes admission/checker children through `/usr/bin/time`;
these are process footprints, not allocator-only measurements. The memory64
native/direct admitted verification times are 68.206/74.219 ms, while
its process costs differ materially. This illustrates why one timing column
cannot stand in for every operating mode.

## Correctness and provenance

Executed checks:

- `cargo fmt --check`, locked all-target Clippy with `-D warnings`, locked release
  tests: nine tests pass; Python Ruff passes for this directory.
- Full CLI controls: 33 transaction checks, 89 tiny execution checks and 104
  memory8 execution checks. All passed.
- Both proof producers and public-only verifiers passed all three samples for
  all eight shapes. Every native comparison reported `produced`/`accepted`.
- Transaction controls include wrong fee/context/owner/ordering/snapshot/network,
  malformed range/signature bytes, prior range/identity/duplicate input refusal,
  honest zero excess, fresh proof commitments/nonces, private wrong secrets,
  consistent false outputs and out-of-range witnesses. Invalid private witnesses
  were produced without a relation precheck and rejected by verification.
- Execution controls mutate every proof message, lengths, EOF, context, source,
  public statement and each matrix view. Actual private CPU/memory/link changes,
  wrong ONE and consistently changed false output/pin/assignment were produced
  and rejected. Rust controls preserve sumcheck recurrences and valid original
  PCS openings but fail each of the three final multiplication guards. The same
  controls run with zero coefficients, exercising the no-division case.
- CLI public-only execution bundles contain only public relation data and
  verifier key/pin, with no assignment or proving-key path. Transaction public
  bundles contain only parameters, ledger and statement.

The original campaign stored raw results and exact commands at
`/tmp/zkc-4b-baselines/final-{tx-final-n8-m2,tx-n16-m4,tx-n32-m8-k4,tx-n64-m2,execution-tiny,execution-memory8,execution-loop16,execution-memory64}/results.json`.
They include all input/tool hashes and raw per-sample process reports. Controls
are under `/tmp/zkc-4b-baselines/final-controls-{tx,execution-tiny,execution-memory8}/results.json`.
Build/check logs are `/tmp/zkc-4b-baselines/{build,test,clippy,ruff}.log`.
These are provenance locations on the measurement machine, not files shipped
with this repository or a guarantee that the temporary directories still exist.
The [reproduction instructions](README.md#reproduce) require retained campaign
inputs; this table remains a historical summary until new results are recorded.
Earlier `measure-*` records are superseded by the `final-*` records after the
capacity-admission hardening and final rebuild. The table uses one final binary identity.

The local adapter source digest is
`5b6e245637be4eda347bdc05785a61109b15b57b7a44d5a6ff4f47eb3bd21b6b`:
SHA-256 of sorted repository-relative paths, each followed by NUL, file bytes,
NUL, for `crates/zkc-arkworks/Cargo.toml` and all 12 `src/**/*.rs` files.
Maintained algorithm source SHA-256 values read for this implementation:

| Source | SHA-256 |
|---|---|
| composable-libraries/source/build.py | `b11ebd1409a036a05785d211191be73151a086165ca41fe500c1e18c6e9fc987` |
| relation-integration/proof/build.py | `1116dc35ce4b7adebad93534237997fc0e179aa55dd4cef59a2bff4ba2654efe` |
| application-composition/execution/build.py | `e9a260facce2da833fa4e921d3cedd5b8ca56c3ca18be2098f932151a1fa57a4` |

The native runtime pin is
`78269cf9ae05f6a7978ce5594a4f85279faa3e70c5b97030c43b79b72ce31923`;
the compiler pin is
`b1aef05fc2f88522ebcb6f1f128192ccb48a7b859d00e21de0dc536c1761da5e`.
This record is fixture-scoped execution evidence with shared trusted crypto
libraries, not proof of the libraries, production setup validity, application
soundness, zero knowledge or the rest of the application composition.
