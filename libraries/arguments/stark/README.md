# STARK compositions

These modules construct nonhiding single-table and three-table arguments from an admitted
external [relation Bundle](../../../docs/spec/domains/relation-bundles.md).
The [Fibonacci client](../../../examples/projects/fibonacci/README.md) uses AIRs
exported from Clean and Plonky3. The protocol is authored in `.zkc`; the compiler has no
STARK-specific dispatch or proof callback.

There are two single-table arguments. The
[parameterized argument](#parameterized-single-table-argument) is generic over a
configuration that fixes its fields, challenge derivation, Merkle instance and
data layout; the [parameterized STARK client](../../../examples/projects/stark/README.md)
runs it at the KoalaBear quartic Poseidon2 configuration. The independent
`stark::octic_table` profile below selects the octic extension and Keccak rows;
the three-table argument builds on the same concrete domains.

## Ownership

| Module | Responsibility |
|---|---|
| `stark::configurations::contract` | The `Configuration` interface and layout helpers |
| `stark::configurations::koala_bear_quartic` | The KoalaBear quartic Poseidon2 configuration |
| `stark::configurations::baby_bear_quartic` | BabyBear quartic, width-16 Poseidon2 and direct quartic Merlin draws |
| `stark::configurations::goldilocks_quadratic` | Goldilocks quadratic, width-8 Poseidon2 and direct quadratic Merlin draws |
| `stark::single_table` | The parameterized single-table argument |
| `stark::single_table::low_degree` | The mathematical `FriConfiguration<K>` adapter for the shared FRI component |
| `air::polynomial` | Scope vanishing polynomials and coefficient-block quotient splitting |
| `air::table` | Interpret the Bundle's ordered inputs and scopes; construct quotient and opening equations |
| `stark::configurations::koala_bear_octic` | Concrete fields, row commitments, embedding and characteristic |
| `stark::sampling` | Bounded out-of-domain sampling with explicit exhaustion |
| `stark::octic_table` | Order commitments, sampling, claims, FRI and authentication |
| `air::interaction` | Record fingerprints, signed field balance, Boolean multisets and reduction equations |
| `stark::whole_bundle` | Table presence, heights, phased commitments, global interaction closure, and one shared FRI instance |
| [`zkc::opening`](../../core/polynomial/opening.zkc) | Shared univariate opening quotients and row equations |
| [`fri`](../../protocols/polynomial/fri/lib.zkc) | Low-degree testing and authenticated first-layer values at the returned positions |

Native Relation operations describe the immutable Bundle and substitute its
assertion and interaction expressions. Native polynomial, vector and commitment operations
implement their own mathematical contracts. The source modules choose the
quotient combination, challenge schedule and acceptance conditions.

The arithmetic shares the standard finite library. Quotient-claim
`recombine` folds a `(sum, power)` state over the ordered claims; the
interaction nonzero check folds multiplication with identity one. The latter
can select native `vector.product` after ordinary helper expansion. Prefix
sums and products that actually construct auxiliary columns remain scans.
These are general mathematical operations, with no protocol names in compiler
selection. `--no-finite-bulk` retains checked ordered execution of the same
source. The [consumer controls](../../../common/tests/protocol/test_protocol_finite_consumers.py)
compare arithmetic, empty inputs and admission through complete proofs.

The [measurement tool](../../../common/benchmarks/README.md) compares FRI,
single-table AIR and both machine reductions at several sizes. It retains
compile timings, selected operations, execution charges and proof results.
FRI's terminal polynomial evaluation keeps its native polynomial operation,
preserving the direct evaluation contract and its existing implementation.

`vanishing(height,begin,end,x)` evaluates the product over subgroup rows
`[begin,end)` at any field point, including excluded subgroup roots.
`vanishing_values` evaluates that same polynomial on the supplied two-adic
coset. Both use the complement shortcut where its denominator is nonzero;
the scalar helper falls back at a removable pole, and the vector helper uses
direct products on intersecting cosets. Full scopes keep geometric evaluation.
The STARK profiles use disjoint evaluation domains and retain the fast path.

## Parameterized single-table argument

`stark::single_table::ScalarTableArgument<K, Table, B, LogFinal, Rounds, LogBlowup, Queries>`
and `BlockTableArgument`
prove the assertions of one present table of Bundle `B`, with the same
statement, scopes and quotient equations as the [older profile](#single-table-statement-and-supported-relation).
The trace has height `n = 2^(LogFinal + Rounds)` and is extended to
`N = n * 2^LogBlowup` points of the configuration's coset. FRI makes `Rounds`
binary folds, ends with a polynomial of `2^LogFinal` coefficients and checks
`Queries` positions. The statement holds configuration and public columns
(row-major) and public slots; the configuration fixes the coset shift, so it is
not a statement input. Round and query counts are static, not public inputs.

The entrypoints share preparation, DEEP reduction, FRI commitment and opening
completion. Scalar sampling requires `IndexRandomness`; block sampling requires
`IndexBlockRandomness` and makes one labelled `fri_queries.positions` request.
There is no capability fallback. Both bind the exact sequence into common FRI
query state before completing the same authenticated association check.

### Configurations

A module implementing `stark::configurations::contract::Configuration` is one
configuration. The protocol modules name no concrete field, hash or layout.

| Member | Meaning |
|---|---|
| `Base`, `Extension` | Trace field; field of challenges, quotient, DEEP word and FRI |
| `Challenge`, `challenge` | Field the selected transcript draws; a uniform `Extension` element from one uniform draw |
| `embed`, `lift`, `shift` | Base-to-extension embedding; the coset shift, avoiding every trace subgroup |
| `BaseRows`, `ExtensionRows` | Row commitments over each field; the Merkle and hash instance |
| `commit_*`, `open_*`, `check_*` | Commit natural-order row-major tables; open and check one pruned multi-opening at natural positions |

Positions are natural: position `i` of a size-`n` table is the value at
`shift * g_n^i`. A configuration that commits outer rows in another order
translates positions inside its own opening and checking members.
`reversed_rows` and `reverse_positions` support bit-reversed outer layouts.
FRI's table realization is selected independently at deployment: individual or
antipodal-pair leaves, with natural or bit-reversed order. Those choices do not
change the logical FRI component or authorize omitting a sibling value. Folding
is binary; grouping several folds into one committed layer is not a parameter.

`stark::configurations::koala_bear_quartic::Keccak256` uses direct quartic
challenges and Keccak base/quartic row commitments with pruned multi-openings.
It supports the installed quartic hash-chain suite, including explicit block
sampling. Root, leaf and node bytes are unchanged by multi-opening; the proof
is the exact pruned sibling sequence for the verifier's positions.

`stark::configurations::koala_bear_quartic::Poseidon2` is another installed configuration:

| Choice | Value |
|---|---|
| Fields | `koala-bear` trace; `koala-bear.ext4-binomial3` (`X^4 - 3`) for challenges, quotient, DEEP and FRI |
| Merkle instance | `rows.merkle-poseidon2-16.koala-bear/0` and `rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0`, with pruned multi-openings |
| Outer layout | Natural row order; FRI layout is a separate deployment choice |
| Coset shift | 3, a generator of the multiplicative group |
| Challenges | The first four coordinates of a draw of the octic Merlin suite `merlin3.koala-bear.ext8-binomial3.rejection31le/0` |

This configuration retains octic draws. Their coordinates are independently
rejection sampled, so under the installed uniformity premise the first four
coordinates of a draw are a uniform quartic element.
A suite drawing quartic elements directly replaces the `challenge` member
alone. Index draws use the same suite's `UniformIndex` transition.

`stark::configurations::baby_bear_quartic::Poseidon2` and
`stark::configurations::goldilocks_quadratic::Poseidon2` implement the same
interface with their explicitly named fields and
[row profiles](../../../docs/spec/domains/oracles.md#poseidon2-instances).
Their coset shifts are primitive generators 31 and 7 respectively. Select
`merlin3.baby-bear.ext4-binomial11.rejection31le/0` or
`merlin3.goldilocks.ext2-binomial7.rejection64le/0` in the proof construction;
these suites draw the selected extension directly. The protocol algorithm and
natural outer-row layout are shared with the KoalaBear configuration.

### Protocol order

1. Commit the base-field trace extended to the coset, as rows.
2. Draw the constraint-composition challenge `alpha`; commit the quotient chunks
   as extension rows.
3. Draw one out-of-domain point `zeta`. Both roles stop unless `zeta^n != 1` and
   `zeta^N != shift^N`; rotations by the trace generator then also avoid the coset.
4. Send the input evaluations at their opening points and the chunk evaluations
   at `zeta`. Preserve the AIR input prefix and append a rotation-zero claim for
   each otherwise unread committed witness column, in column order. The verifier
   checks the exact extended count, recomputes known inputs and checks the AIR
   identity using only the original prefix.
5. Draw `gamma` and then a fresh adjustment `delta`. Form D from every witness
   read (including the appended coverage claims) `(T(X)-v)/(X-zeta*g^r)`, then
   every chunk `(Q_j(X)-q_j)/(X-zeta)`, with successive powers of `gamma`.
   Commit the adjusted word `(1+delta*X)D(X)` to FRI. An honest D has degree
   below `n-1`; the adjusted word has degree below `n`. The exact meaning and
   limits are specified in the [reduction contract](../../../docs/spec/domains/stark.md).
6. Shared `fri::Commit<FriConfiguration<K>,...>` sends each actual layer as a
   logical oracle, draws its folding challenge and constructs the virtual fold
   from that exact layer and challenge. It sends the padded terminal polynomial
   after the last fold.
7. Draw every query position in `[0, N)`, consecutively, before any opening.
8. Authenticate the trace and quotient rows at those positions, one pruned
   multi-opening each, and compute their adjusted DEEP values. Call shared
   `fri::QueryAssociated` with that same FRI state and those values.

For every query, the shared checker authenticates the selected initial-layer
value and checks equality with the supplied DEEP value. It evaluates each
virtual fold through its two ordered source reads, checks subsequent actual
layer answers against the preceding fold, and checks the final polynomial at
the final query point. A failed requirement stops before acceptance. Repeated
logical reads remain distinct even when a realization shares their transport.

Both logical sibling values are retained. Complete-leaf authentication,
physical grouping and packet scheduling belong to the checked oracle realizer.
The old specialized sibling-only and layer-major multi-opening route has been
removed. Its message count and proof size do not describe the new route;
measurements must name the selected realization and authentication policy.

### Evidence and limits

The [library tests](../../../common/tests/protocol/test_stark_library.py)
cover generated recurrences, configuration columns, altered messages and public
inputs, wrong openings, and dishonest trace/quotient claims on the shared-FRI
implementation. Prior specialized-FRI measurements are not performance evidence
for the new implementation. The `stark`
[benchmark family](../../../common/benchmarks/README.md) exercises the same AIR
shapes. Current validation is recorded in [status](../../../docs/status.md).

Query positions are separate `index` draws; they are consecutive so that one
block request can replace them. There is no proof-of-work grinding. The
argument covers one table, without interactions. As for the older profile,
these checks are execution and rejection evidence: no theorem here bounds the
soundness of this composition, its sampling or its Fiat–Shamir transform, and
commitments are nonhiding. The proof format is zkc's own, not Plonky3's.

## Single-table statement and supported relation

`TableArgument<Table,B,LogHeight,LogSize,Queries,Attempts>` proves the assertions
of one **present** table. Its witness groups and public/configuration groups
must have base KoalaBear entries, and the combined witness width must be
positive. The caller supplies row-major matrices with
groups concatenated across each row in declaration order. Bundle public slots
have their declared order. Internally each column is contiguous; transposition
at commitment boundaries is explicit.

Both roles construct a `Statement` from their inputs. The verifier's
configuration, public columns, public scalars and shift determine its checks.
Honest execution uses identical statements. The examples bind these inputs through their proof Entries. An optional
relation target identifies the intended statement; naming one does not prove
the verifier implements it.

Let `n = 2^LogHeight`, `N = 2^LogSize`, `H = <g_n>`, and `D = s <g_N>`.
The height must satisfy the table's policy, `n >= 2`, `N >= 2n`, and the
installed two-adic bounds. The shift is nonzero and `s^N != 1`, making `D`
disjoint from `H`. Runtime round, query and attempt counts must equal the
static profile; there is at least one query and one sampling attempt.
The quotient chunk count must also satisfy `chunks * n <= N`.

Finite reads are checked on their active windows. Cyclic reads use exactly the
order-`n` subgroup, so offset `k` denotes evaluation at `g_n^k X`, including
wraparound. Scopes may be all rows, boundary rows, interiors or intervals.
Inactive scopes contribute nothing. Every retained arena input keeps its
original position, even if no assertion uses it.

The single-table protocol does not enforce interactions with other tables or
choose whether an optional table is present. A whole-Bundle client must supply
those obligations. The recurrence example restricts its Bundle to one table
and no interaction channels.

## Quotient and opening equations

For assertion `a`, substitute each read with its column polynomial at the
specified rotation, and each public slot with its scalar. Call the resulting
polynomial `C_a(X)`. For active row set `S_a`, let

```text
Z_a(X) = product_{r in S_a} (X - g_n^r)
Q(X)   = sum_{active a} alpha^position(a) C_a(X) / Z_a(X)
Q(X)   = sum_{j=0}^{chunks-1} X^(j*n) Q_j(X),   degree(Q_j) < n.
```

The prover evaluates the first equation on `D`, interpolates it, checks the
coefficient bound, and splits coefficients into blocks of length `n`.
`relation.table_shape` derives the bound from assertion degrees and scope
sizes. At least one chunk is encoded, including when every quotient is zero.
This coefficient-block convention is part of this profile; it does not claim
compatibility with upstream proof encodings.

After the quotient commitment, both roles select the first sampled `z` outside
`{0} union H union D`. Every one of the fixed number of attempts is drawn and
transmitted, even after a usable point is found. Exhaustion stops explicitly.
Because `D` is stable under multiplication by `g_n`, each rotated opening point
`z*g_n^k` also lies outside `D`.

The prover sends a value for every ordered input and every quotient chunk at
its opening point. The verifier recomputes configuration/public evaluations,
substitutes the assertion expressions and checks the quotient identity at `z`.

For each witness opening `(T,u,v)` and quotient opening `(Q_j,z,q_j)`, combine
`(T(X)-v)/(X-u)` or `(Q_j(X)-q_j)/(X-z)` with successive powers of `rho`.
Multiply the sum by `1 + eta*X`. Honest inputs give degree less than `n`.
FRI tests that bound. At each returned FRI position, the verifier authenticates
the original base-field trace row and extension-field quotient row, recomputes
this same combined value, and compares it with FRI's authenticated value.
Base-field commitment decoding keeps the trace's declared carrier explicit.

## Schedule and verification

1. Commit base-field trace evaluations on `D`.
2. Draw `alpha`; construct and commit the extension-field quotient chunks.
3. Draw all bounded out-of-domain candidates; select `z` or stop.
4. Send input-opening and quotient-opening claims; check the quotient identity.
5. Draw `rho` and `eta`; construct the combined word and run FRI.
6. Authenticate original trace and quotient rows at all returned positions and
   check the combined opening equation.

FRI commits every fold layer before its challenge and sends terminal
coefficients before queries. All its queries precede all openings. The outer
protocol uses the exact positions and values returned by that child call.
Every failed requirement stops; `accepted` is true on continuing paths.

## Evidence and limits

The [polynomial helper tests](../../../common/tests/protocol/test_air_polynomials.py)
compare scope products, column extensions and layouts with independent integer
Ext8 arithmetic. The [protocol tests](../../../common/tests/protocol/test_air_stark.py)
exercise the imported AIR with separate prover/verifier Hosts, several domain
sizes and compilation modes, malformed statements and schedules, altered
commitments, claims and openings, and excluded-set exhaustion. Dishonest prover
variants retain consistent commitments and FRI folds but fail the outer
quotient or DEEP equation. Descriptor checks retain the commitment, claim and
query order through nested protocol calls. Independent integer interpolation
also reconstructs the complete quotient chunks, OOD claims and DEEP word. Native Bundle
polynomial tests independently check descriptors, degrees and substitutions.

[Adversarial controls](../../../common/tests/protocol/test_air_stark_adversarial.py)
reach the verifier with a false trace, a compensated opening lie and a
column whose degree exceeds the declared bound. The
[statement-authority controls](../../../common/tests/protocol/test_air_statement_authority.py)
use interval scopes and public columns, and reject a prover's consistent proof
for different configuration, public-column or scalar inputs. Removing the
specific known-input or degree-adjustment check admits its corresponding
counterexample.

These checks establish bounded execution and rejection evidence. A security
claim still needs a reduction for this exact quotient/opening/FRI composition,
its degree bounds and batching error, the sampling distribution and abort
probability, commitment binding, and the chosen Fiat-Shamir model. No such
end-to-end theorem is supplied here. The example parameters are small testing
parameters. Commitments and openings are nonhiding, and the proof format is
zkc's own.


## Whole-Bundle argument

`stark::whole_bundle::ThreeTableArgument<B,R,MaxLogHeight,LogSize,Queries,Attempts>`
composes three tables from one captured Bundle with one
`air::interaction::Reduction<Extension>` implementation. The fixed three-table
container is a source-library limitation: the native Bundle model supports
more tables. Table names, instruction semantics and memory rules are absent
from the library. The [FemtoCairo example](../../../examples/projects/femtocairo/README.md) selects
its CPU, configured program and indexed immutable memory relation externally.
The [accumulator fixture](../../../common/tests/fixtures/projects/accumulator-machine/README.md)
also exercises optional memory and both reductions.

The selected profile requires:

- Three base-KoalaBear tables and at least one channel. Required tables are
  present. Present heights `h_t` satisfy the Bundle policy and are powers of
  two between 2 and `H = 2^MaxLogHeight`. Configuration remains authoritative
  even for absent optional tables. Their fixed/configured logical heights
  retain the Bundle's range and power-of-two policy, independently of `H`;
  absent instance-height tables use zero. An absent table's effective layout
  height, widths, scopes, quotient chunks and reduction claims are all zero.
- Global interactions active on every row. LogUp accepts signed field-balance
  records and multiset records with declared count bound one. Grand product
  accepts only the latter. The source enforces `m*(m-1) = 0` for multiset records;
  field weights have no Boolean range constraint. Other count bounds and local
  or partial-row scopes are refused. An adapter can express a partial-row
  lookup using a selector constrained to its active rows.
- Positive total witness width and auxiliary width. Absent tables contribute
  no committed columns, openings or unconstrained claims. Empty per-table
  groups and inactive tuples retain their declared semantics.
- A shared coset `D = s<g_N>`, `N = 2^LogSize >= 2H`, disjoint from the
  order-`H` subgroup. Each table's quotient capacity obeys `chunks_t*h_t <= N`.
  As in the single-table profile, runtime counts equal the static parameters.

### Reduction boundary

`Interactions` retains each tuple's kind, channel, side, arity and degrees, including
record expressions of degree greater than one. `Layout` names auxiliary
columns, rotated openings, claims and each constraint's scope and degree.
`Reduction` supplies construction, the same constraint arithmetic over rows or
at one point, table-claim accumulation and global closure. Degree derivation
weights record expressions by their Bundle degrees and auxiliary columns by
one. These objects stay in source; native Relation operations supply immutable
metadata and simultaneous substitution only.

For each channel, draw independent `gamma, delta` after the base commitment and
compress a tuple as `fp = t_0 + delta*t_1 + ...`. Both reductions use the same
base rows and the same record expressions as the table assertions:

| Reduction | Auxiliary equations | Global check and premise |
|---|---|---|
| `LogUp<F>` | Per record `m*(inv*(gamma-fp)-1)=0`; running signed sums of `m*inv` with first, transition and last constraints | Table claims sum to zero per channel; natural multiset counts must remain below the base-field characteristic |
| `GrandProduct<F>` | Prefix products of `m*(gamma-fp)+1-m`, separated by channel and side | Global push and pull products agree and an inverse claim makes the product nonzero |

The Boolean range constraints belong to the original multiset relation.
They are enforced alongside both reductions, and omitted for field-balance
records. A nonzero field weight uses `1/(gamma-fp)` as its inverse column, then
contributes `m*inv` to the sum. An inactive row uses inverse zero
or product factor one, so its unused tuple cannot cause a denominator failure.
Active zero denominators cause an explicit prover abort. The LogUp count bound
prevents equality only modulo the characteristic from substituting for equality
of natural multiplicities. Field-balance channels already mean equality in the
field and do not acquire natural-count semantics. External source models may
require additional cardinality premises, which their adapters must retain.
Random compression collisions, rational/product
identity error and abort probability still need cryptographic bounds.

### Phases

1. Commit the combined base-field witness evaluations.
2. Draw `gamma, delta` for every channel; build and commit extension-field
   auxiliary columns; send table/global claims and check global closure.
3. Draw `alpha`; form the quotient of each table's assertions, Boolean ranges
   and auxiliary constraints; commit all quotient chunks.
4. Draw bounded out-of-domain candidates, excluding zero, the order-`H`
   subgroup and `D`; send input, auxiliary and quotient opening claims.
   Recompute verifier-known configuration/public slots and every table identity.
5. Draw `rho, eta`; combine every base, auxiliary and quotient opening into
   one DEEP word, including the `1+eta*X` degree adjustment. Run FRI at bound H.
6. At the exact FRI positions, authenticate base, auxiliary and quotient rows
   and recompute the combined opening equation.

### Different table heights

Each honest column and quotient chunk of table `t` has degree below `h_t`.
The shared FRI test has bound **H**, so it does not separately enforce each
smaller degree bound. This choice avoids separate FRI sessions and additional
per-column degree-shift words. Its intended extraction takes the resulting
polynomials' values on each table's own subgroup; cyclic rotations still agree
with row reads there. The argument must account for the larger adversarial
bounds when proving that identities hold everywhere.

In particular, under extracted input/auxiliary/chunk degrees below H, a table
with `k_t` chunks can represent a quotient of degree at most
`(k_t-1)*h_t + H-1`. For a constraint of algebraic degree `d_a` on nonempty scope
`S_a`, multiplying the combined quotient equation by `X^h_t-1` gives a bound
no larger than

```text
max(max_a[d_a*(H-1) + h_t - |S_a|], k_t*h_t + H-1).
```

This is a bound to use in the remaining security reduction, not a theorem
supplied by the implementation. Known configuration and public columns are
checked at the sampled point, and their interpolants have degree below `h_t`.

### Machine evidence and remaining scope

The [machine protocol tests](../../../common/tests/protocol/test_machine_stark.py) cover
both reductions, three external executions, differing table heights, absent
and idle memory, ordinary/simplification-disabled/storage-release compilation,
invalid relations and profiles, all commitment phases, and the exact nested
transcript order. The [reduction comparison](../../../common/tests/protocol/test_air_interaction.py)
checks source auxiliary columns, claims and scoped residuals against the
independent staged reference. The [malicious-prover tests](../../../common/tests/protocol/test_machine_stark_adversarial.py)
commit consistent false quotients and auxiliary columns. A valid execution of
another configured program with the same final result is rejected by the known
configuration obligation; disabling that obligation makes the control pass.

The implementation uses small test parameters and its own proof encoding.
Absent configuration uses the captured `relation.table_widths` metadata, which
requires no polynomial domain. Fixed and configured logical heights obey the
Bundle's own policy, including heights 1 and 3 when permitted, and retain exact
configuration lengths even when absent. Instance-height absence uses zero.
Only present tables call `relation.table_shape` and must satisfy this
argument's two-adic height bound `H`, assertion windows and quotient limits.
Static polynomial references check the table and carrier; reached operations
with a height check that actual height.

The [admission controls](../../../common/tests/protocol/test_bundle_admission.py)
compare both native relation evaluators and exercise the source admission
through the Host and both complete reductions. They cover absent fixed and
configured heights 1, 3 and above `H`, absent instance height zero, empty
contributions, configuration shape and authority, and present-table refusal.

The [Clean controls](../../../common/tests/protocol/test_clean_adapter.py) additionally
exercise signed weights, repeated lookups, indexed memory, two independently
authored Fibonacci AIRs and complete source proofs.

Arbitrary table counts, other interaction profiles,
hiding, production parameter selection, and a security theorem for the exact
composition remain separate work. The external VM relation also needs an
adequacy argument connecting its constraints to the intended execution semantics.
