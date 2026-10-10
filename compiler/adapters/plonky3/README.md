# Plonky3 AIR adapter

This standalone Rust workspace captures AIRs written against pinned Plonky3
0.5.1 and exports them as views over the shared `zkc.ring/0` expression arena.
An importer rechecks the exported view, binds it to an authorized instance and a
witness, and derives relation-bundle carriers. Neither the root native workspace
nor the compiler builds or links this adapter, and no Plonky3 type enters the
shared compiler or runtime model.

## Pins and layout

| Package | Directory | Role |
|---|---|---|
| `zkc-plonky3-air` | `exporter/` | Capture, lowering, artifacts, importer, closed view, references, bundle translation |
| `zkc-plonky3-air-client` | `client/` | Ordinary upstream AIRs maintained as external clients, and refused controls; depends only on Plonky3 |
| `zkc-plonky3-air-driver` | `driver/` | Fixture driver `zkc-plonky3-air-fixtures` and the differential tests |

[`Cargo.toml`](Cargo.toml) pins `p3-air`, `p3-field`, `p3-koala-bear` and
`p3-matrix` to exactly 0.5.1, the crates.io release of upstream commit
`45e0ffe4d294816755522dd2cf7c38d6bcd701ce`. This is the family the native
KoalaBear provider in `crates/zkc-backends` pins, so both name the same field
types. `p3-commit` 0.5.1 is a test dependency for the upstream two-adic selector
law. The lockfile was seeded from the root lockfile; packages the two graphs
share resolve to the same versions. Later Plonky3 releases have different AIR
APIs and metadata and are not substitutes for this pin.

The fixture driver names the client AIRs it captures. That selection is local to
this adapter; the zkc compiler and runtime never recognize an AIR by name.

## Build and test

From the repository root, `just test-plonky3` runs the workspace tests with
native differential checks. It is an explicit optional suite, separate from
`just test` and automatic native CI. For individual commands, run from this
directory:

```sh
cargo test --locked --workspace
cargo test --locked -p zkc-plonky3-air-driver --features native
RUSTFLAGS="-C target-cpu=native" ZKC_PLONKY3_PACKING_WIDTH=8 \
  cargo test --locked -p zkc-plonky3-air-driver --features native
```

The `native` feature adds `zkc-runtime` and `zkc-backends` through relative
path dependencies and compares exported arenas with the native ring admission
and KoalaBear/Ext8 provider. Portable builds pack one lane; the third command
checks the packed provider at the AVX2 width. `ZKC_PLONKY3_PACKING_WIDTH`
states the expected width and is optional.

Regenerate or check the [fixtures](fixtures) through the resource-limited
wrapper, which bounds address space, CPU time and wall-clock time:

```sh
cargo build --locked -p zkc-plonky3-air-driver
python3 regenerate.py --binary target/debug/zkc-plonky3-air-fixtures check fixtures
python3 regenerate.py --binary target/debug/zkc-plonky3-air-fixtures write NEW_DIRECTORY
```

`write` refuses an existing directory. `check` requires every file to equal
its regeneration byte for byte and the imported violations to equal the
upstream debug checker's.

## Capture

The exporter evaluates the AIR with the upstream `SymbolicAirBuilder<KoalaBear>`
for the layout its `BaseAir` metadata declares: main width, preprocessed table
and public value count. Every call into the AIR runs under `catch_unwind`. The
exporter evaluates three times: once with the declared layout, again to detect
nondeterminism, and once with every unsupported surface (periodic columns,
permutation columns, challenges and expected permutation values) given a nonzero
width. That probe evaluation must reference none of those surfaces and must
assert the same constraints. An AIR that silently skips an empty surface is
refused rather than exported without it.

The supported inventory is cyclic main and preprocessed reads at offsets zero
and one, public values, the first-row, last-row and transition selectors,
KoalaBear constants, addition, subtraction, negation and multiplication. Upstream
`Sub(x, y)` becomes `add(x, neg(y))`; the node map records both origins, so the
upstream expressions can be rebuilt exactly. Constants are written as canonical
representatives (`as_canonical_u32`), never as internal Montgomery residues.
Lowering is iterative, follows upstream `Arc` sharing by address and merges
structurally equal nodes.

Metadata must agree with evaluation: every main or preprocessed column read on
the next row is listed in `main_next_row_columns` or
`preprocessed_next_row_columns`; those lists contain distinct in-range columns;
a `num_constraints` hint equals the captured count; a `max_constraint_degree`
hint bounds every captured degree multiple; a preprocessed table has positive
width and a power-of-two height. The exporter recomputes each upstream
`degree_multiple` from the arena and refuses a mismatch.

| Refusal | Cause |
|---|---|
| `plonky3-periodic-column` | Periodic column read |
| `plonky3-permutation-column`, `plonky3-permutation-challenge`, `plonky3-permutation-value` | Permutation-argument surfaces |
| `plonky3-extension-constraint` | `assert_zero_ext` |
| `plonky3-selector-not-guard` | A selector below an addition or subtraction |
| `plonky3-eval-panicked` | A panic in metadata or evaluation, including undeclared public values and windows other than two rows |
| `plonky3-nondeterministic-eval`, `plonky3-probe-dependent-eval` | Unstable evaluation |
| `plonky3-next-row-metadata`, `plonky3-constraint-count-hint`, `plonky3-degree-hint`, `plonky3-preprocessed-shape` | Metadata contradicting evaluation |
| `plonky3-arena-limit`, `plonky3-capture-limit`, `plonky3-layout` | Size bounds |

`AirBuilderWithContext` is not implemented by the symbolic builder, so an AIR
that requires runtime context cannot be captured at all.

## Selectors and rows

The table is cyclic with height `n = 2^k`: a next-row read on row `n - 1` reads
row zero. Selector slots have two laws with different residual values:

```text
row indicator      first = [i = 0], last = [i = n-1], transition = [i != n-1]
two-adic Lagrange  first = Z_H(x)/(x-1), last = Z_H(x)/(x-g^-1), transition = x-g^-1
```

The first is the convention of upstream `DebugConstraintBuilder` and
`check_constraints`; the second is the two-adic STARK's, including off the
trace domain. The exporter checks syntactically that every path from an
assertion to a selector passes only through multiplication and negation. Each
residual is then plus or minus a product of selector powers and a selector-free
factor. Because `n` is below the characteristic and `g^-1` is the only root of
`x - g^-1` on the domain, both laws vanish on the same rows. That shared zero
locus is the only claim relating them; their residuals are never equated.

## Artifacts

Each artifact has one exact schema. Unknown or missing fields refuse, and
accepted text must equal its canonical encoding: sorted top-level fields, one
per line, each value in compact JSON. Identities are SHA-256 of that text.

| File | Format | Content and authority |
|---|---|---|
| `export.json` | `zkc.plonky3-air-export/0` | Candidate relation: arena and its digest, slot bindings, layout and preprocessed values with their digest, assertions in upstream emission order with degree multiples and selectors, node origins, feature inventory and upstream pins. It carries no authority until a verifier configuration selects its identity. |
| `instance.json` | `zkc.plonky3-air-instance/0` | Verifier statement: selected export identity, height and public values |
| `witness.json` | `zkc.plonky3-air-witness/0` | Prover main trace |
| `arena.json` | `zkc.ring/0` | Exact arena text, captured by the source compiler with `--asset=export=ring-json=FILE` and retained in the authenticated Entry package |
| `bundle*.json` | `zkc.relation-bundle/0` and its configuration, instance and witness | Derived relation-bundle carriers |
| `expected.json` | | Upstream debug-checker failures for the fixture's instance and witness |
| `source-*.json` | Entry input maps | Recurrence only: participant inputs for the [imported AIR source client](../../../examples/projects/imported-air/README.md). Trace requests keep witness, configuration and public values separate; polynomial requests carry assignments prepared by the closed view. `source-expected.json` holds direct `Air::eval` values for each. |

Slot bindings are `["main", column, offset]`, `["preprocessed", column, offset]`,
`["public", index]` and `["selector", kind]`. Assertion `i` is upstream
constraint `i`, the index `DebugConstraintBuilder` reports. The importer
recomputes every derived fact: formation and identity of the arena, slot
validity, next-row declarations, node map, degree multiples, guard form and
feature inventory. A preprocessed table is configuration authored by the AIR and
bound by the export identity; it fixes the trace height. Binding an instance
checks its export identity, a power-of-two height up to 2^24 that matches any
preprocessed height, and the exact public value count.

The relation-bundle carriers follow the [native bundle contract](../../../docs/spec/domains/relation-bundles.md) and are
derived from the export, which remains the source artifact. The bundle has
scopes, not selector inputs. From the checked guard form, each selector is
replaced by the constant one and the assertion is restricted to the selector's
support: none to all rows, first row, last row, transition to rows `i` with
`i + 1 < n`. Under the row-indicator law this keeps every residual value on scope
rows and drops only rows whose residual is identically zero. Assertions
combining different selector kinds, and fixed heights above 2^20, refuse with
`plonky3-bundle-scope` and `plonky3-bundle-height`.

## Maintained evidence

The [client](client/src/lib.rs) is a four-column nonlinear recurrence with a
preprocessed column, public initial and final values, a degree-three transition
and a last-row constraint that reads row zero through the wrap. Its residuals
are not computed from the exported arena by any reference. The tests compare, on
honest traces, every single-cell change of three rows and every changed public
value:

- the adapter's arena interpreter, native scalar and packed rows and direct
  `Air::eval` builders, exactly, under both selector laws and at heights from 1
  to 2^16;
- violation sets with the upstream `DebugConstraintBuilder`, and acceptance with
  `check_constraints`;
- out-of-domain Ext8 values with direct evaluation at barycentric openings, and
  the selector closed forms with upstream `selectors_at_point`;
- native exact coefficients of the composed constraint polynomials with direct
  evaluation on and off the domain, divisibility by `Z_H` with upstream
  acceptance and the recorded degree bound, for heights up to 16; the provider
  refuses height 32 at its degree limit rather than truncating;
- native affine sums over row pairs, and Ext8 promotion of base inputs;
- bundle residuals on scope rows with row-indicator residuals.

The [source client](../../../examples/projects/imported-air/README.md) runs the
recurrence arena through the common compiler and the Entry Host as an evaluator
asset. Its requests come from the closed view of the honest trace, one changed
cell and one changed public value: row assignments under both selector laws,
slot coefficient polynomials, and Ext8 assignments off the domain. Their
expectations are direct `Air::eval` values. The driver writes them only if the
arena interpreter agrees and the nonzero row cells equal the upstream failures.

Controls cover the refusals above, wraparound, stale and self-consistent but
wrong exports (Montgomery constants, rebound reads, changed fixed columns),
broken guards, height, width, public and identity mismatches, and noncanonical
text and scalars.

## Limits and claims

Arena bounds follow the shared contract. The adapter additionally bounds widths
and public counts at 4,096, preprocessed cells at 2^22, upstream nodes visited at
2^22, export text at 64 MiB and witness cells at 2^22. Native providers apply
their own work and element limits.

Closed views revalidate a candidate before binding it. Row materialization and
reference results are limited to 2^22 cells, and reference evaluation to 2^28
work units. The direct inverse DFT reference is limited to height 256 with its
quadratic work checked before interpolation. Bundle reference views borrow the
validated export, check input shapes, and apply the same result/work limits.

`Air::eval` is arbitrary host code. An export records what the selected source
asserted for its declared layout on the pinned upstream, checked against the same
`Air` on supplied traces. It is not a source-adequacy theorem for arbitrary Rust,
a STARK, quotient or FRI implementation, or a proof-format compatibility claim.
Lookups, permutations, periodic columns, challenges and extension-field
constraints are refused, not modelled. Agreement of the row and two-adic laws
covers zero loci only.
