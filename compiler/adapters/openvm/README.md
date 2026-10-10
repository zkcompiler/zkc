# OpenVM relation comparison

This standalone workspace captures a selected subsystem of pinned OpenVM as
ordinary zkc relation-bundle carriers. The C++ compiler and Rust runtime admit
those carriers independently; neither links OpenVM or recognizes a VM table by
name. The adapter compares native residuals and field-weighted bus balances with
upstream evaluation on the same concrete traces.

## Scope and ownership

The selection is the generic RV32 branch-equal subsystem instantiated over
KoalaBear. It uses the upstream BEQ/BNE executor, trace fillers, connector and
range-checking chips. Five AIRs supply the relation:

| Table | Upstream AIR | Authority |
|---|---|---|
| Program | `ProgramAir` | Cached instructions in verifier configuration; usage frequencies in witness |
| Connector | `VmConnectorAir` | Initial/final PC, exit code and termination flag in the public instance |
| Branch | `Rv32BranchEqualAir` | Instruction execution and register reads in witness |
| Range checker | `VariableRangeCheckerAir` | Range-table witness and field-valued frequencies |
| Memory partner | Upstream test utility `MemoryDummyAir` | Unconstrained memory-bus messages and counts in witness |

Program and connector are required; the remaining tables are optional. Present
heights are powers of two from 2 to 2^20, with connector height fixed to two
and range-checker height fixed to 2^(range_max_bits + 1).
Height-one traces are refused because the selector lowering uses distinct
first/interior/last row classes. Program code layout follows the upstream
crate-private program trace generator and names its source in `slice.rs`.
All bus channels lower to **field-balance**, preserving signed field counts;
they are not Boolean multiset counts, and no record declares a count bound.

This is not the deployed OpenVM configuration: that uses BabyBear. Its persistent
memory boundary, memory Merkle tree and Poseidon2 periphery require a field
interface that this KoalaBear instantiation does not implement. The memory
partner is an unconstrained test boundary: `MemoryDummyAir` asserts nothing,
and its witness rows may send or receive any memory-bus message with any field
count. Two reads of one register, even within one step, need not agree.
Acceptance therefore establishes neither execution nor termination under VM
semantics, nor authentication of an initial memory image. An accepted instance
can claim termination for a program that never terminates.
The remaining ISA, executable commitment,
public-value publication, continuations, recursion and proof verification are
outside this selection.

The [accumulator-machine proof](../../../examples/projects/accumulator-machine/README.md)
is a separate executable STARK example. Its three-table Boolean-multiset source
profile does not directly prove this five-table field-balance relation.

## Dependencies and capture

[`Cargo.toml`](Cargo.toml) and [`Cargo.lock`](Cargo.lock) own exact upstream
sources and versions. OpenVM is pinned by revision. Its backend dependency uses
upstream's `main` source identity, with the lockfile fixing the release commit
whose tree matches OpenVM's own locked backend. Always use `--locked`.
This isolated workspace uses OpenVM's Plonky3 family; those types never cross
the native carrier boundary.

The exporter runs the upstream symbolic recorder and key generation. It retains
both the recorder's constraint order and the canonical verifying-key DAG,
including interaction expressions, unused variables, count weights and height
constraints. Selector specialization creates scoped assertion outputs over one
shared ring arena; cyclic reads, public slots and cached/main partitions remain
explicit. The provenance report records each mapping. It is emitted for
inspection; the input contract consumed by native tools is the existing
[relation Bundle format](../../../docs/spec/domains/relation-bundles.md).

The Bundle's field-balance relation is a deterministic sum per exact bus tuple.
An upstream `count_weight` is an interaction's coefficient in a trace-height
inequality `sum(count_weight * height) < p`, not a bound on any row's count, so
every Bundle record declares its count bound as `null`. The weights and
inequalities are retained only in `capture.json` as provenance, not asserted as
security theorems or enforced as additional Bundle satisfaction conditions. A
security comparison must account for those premises and the upstream
interaction argument separately.

## Run the checks

From the repository root:

```sh
cargo test --locked --manifest-path compiler/adapters/openvm/Cargo.toml --workspace
```

For the two native evaluators, first build the compiler and test drivers as in
the [development guide](../../../docs/development/README.md), then select their
output directories:

```sh
ZKC_COMPILER_BIN="$PWD/build/compiler" ZKC_NATIVE_BIN="$PWD/target/release" \
  cargo test --locked --manifest-path compiler/adapters/openvm/Cargo.toml \
  --workspace --features native
```

This is an optional external integration. The default root build and automatic
native CI do not fetch or build OpenVM. Export fresh inspection artifacts into
an output directory with:

```sh
cargo run --locked --manifest-path compiler/adapters/openvm/Cargo.toml \
  -p zkc-openvm-relation-driver --bin zkc-openvm-relation-fixtures -- \
  build/openvm-relation
```

`capture.json` reports provenance and lowering; `candidates.jsonl` contains the
four Bundle carriers per case; `expected.json` labels expected satisfaction and
failure counts. These generated artifacts are not source fixtures.

## Evidence

The corpus includes taken/skipped branches, fall-through, nonzero exit codes,
boundary registers and padding. From one honest run it changes every public
slot; every column of every configuration and witness group on the first,
second and last row; each of those rows as a whole with independent values;
optional table presence; and the range table's padding row to offer an
out-of-range value. Some unused padding changes correctly preserve
satisfaction. Upstream is the oracle, read without the lowering: its recorder
constraints on every row, its logical bus messages and its debug checkers. For
every honest and forged case:

- Upstream `check_constraints` agrees with the recorder residuals,
  `check_logup` with the logical bus messages, and the canonical keygen DAG
  with every recorder constraint.
- Every nonzero upstream residual is reported, with its exact value, by exactly
  one lowered assertion of its constraint whose scope contains the row, and no
  other lowered residual is nonzero. Unbalanced bus keys and sums match exactly.
- Bundle satisfaction equals upstream acceptance.
- Both native evaluators return identical complete reports, whose nonzero
  residuals and unbalanced sums match these expected values.

The corpus reports a residual for every lowered assertion on every row class
that its scope covers at the corpus heights. Deleting any single lowered
assertion, or every assertion of one scope, therefore fails the comparison, and
a test checks both; without the last-row assertions, the forged range table
would satisfy the Bundle. On deterministic arbitrary traces of every table at
heights 2, 4 and 8, assertion scopes and vacuous classes partition each
constraint's row classes, every in-scope lowered output equals the recorder and
DAG value, and the recorder value is zero on every class omitted as vacuous.

Malformed required-table presence, heights, matrix widths and identities are
also refused. Parameter, register, step and timestamp limits have named refusal
controls. This is finite differential evidence about the selected relation and
pin; it does not prove the adapter, relation adequacy or a cryptographic reduction.
