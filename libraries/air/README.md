# AIR polynomials and STARK profiles

These modules construct nonhiding single-table and three-table arguments from an admitted
external [relation Bundle](../../docs/spec/domains/relation-bundles.md).
The [recurrence client](../../examples/projects/air-stark/README.md) uses an AIR
exported from Plonky3. The protocol is authored in `.zkc`; the compiler has no
STARK-specific dispatch or proof callback.

## Ownership

| Module | Responsibility |
|---|---|
| `air_polynomial` | Column interpolation and extension, scope vanishing polynomials, coefficient-block splitting, and matrix layouts |
| `air_table` | Interpret the Bundle's ordered inputs and scopes; construct quotient and opening equations |
| `air_stark` | Select KoalaBear trace rows and Ext8 challenges; order commitments, sampling, claims, FRI and authentication |
| `air_interaction` | Record fingerprints, Boolean multiplicities, and interchangeable LogUp/grand-product auxiliary constraints |
| `air_bundle` | Table presence, heights, phased commitments, global interaction closure, and one shared FRI instance |
| [`fri`](../fri/lib.zkc) | Low-degree testing and authenticated first-layer values at the returned positions |

Native Relation operations describe the immutable Bundle and substitute its
assertion and interaction expressions. Native polynomial, vector and commitment operations
implement their own mathematical contracts. The source modules choose the
quotient combination, challenge schedule and acceptance conditions.

`vanishing(height,begin,end,x)` evaluates the product over subgroup rows
`[begin,end)` at any field point, including excluded subgroup roots.
`vanishing_values` evaluates that same polynomial on the supplied two-adic
coset. Both use the complement shortcut where its denominator is nonzero;
the scalar helper falls back at a removable pole, and the vector helper uses
direct products on intersecting cosets. Full scopes keep geometric evaluation.
The STARK profiles use disjoint evaluation domains and retain the fast path.

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
Honest execution uses identical statements. The selected example binds these
inputs through its proof Entry and names the original base-field relation as
its target. Naming that target does not prove the verifier implements it.

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

The [polynomial helper tests](../../common/tests/protocol/test_air_polynomials.py)
compare scope products, column extensions and layouts with independent integer
Ext8 arithmetic. The [protocol tests](../../common/tests/protocol/test_air_stark.py)
exercise the imported AIR with separate prover/verifier Hosts, several domain
sizes and compilation modes, malformed statements and schedules, altered
commitments, claims and openings, and excluded-set exhaustion. Dishonest prover
variants retain consistent commitments and FRI folds but fail the outer
quotient or DEEP equation. Descriptor checks retain the commitment, claim and
query order through nested protocol calls. Independent integer interpolation
also reconstructs the complete quotient chunks, OOD claims and DEEP word. Native Bundle
polynomial tests independently check descriptors, degrees and substitutions.

[Adversarial controls](../../common/tests/protocol/test_air_stark_adversarial.py)
reach the verifier with a false trace, a compensated opening lie and a
column whose degree exceeds the declared bound. The
[statement-authority controls](../../common/tests/protocol/test_air_statement_authority.py)
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

`air_bundle::ThreeTableArgument<B,R,MaxLogHeight,LogSize,Queries,Attempts>`
composes three tables from one captured Bundle with one
`air_interaction::Reduction<Extension>` implementation. The fixed three-table
container is a source-library limitation: the native Bundle model supports
more tables. Table names, instruction semantics and memory rules are absent
from the library. The [machine example](../../examples/projects/accumulator-machine/README.md)
selects its CPU, configured program and optional memory relation externally.

The selected profile requires:

- Three base-KoalaBear tables and at least one channel. Required tables are
  present. Present heights `h_t` satisfy the Bundle policy and are powers of
  two between 2 and `H = 2^MaxLogHeight`. Configuration remains authoritative
  even for absent optional tables; absent instance-height tables use zero.
- Global multiset interactions active on every row, with declared count bound
  one. The source enforces `m*(m-1) = 0` for each record. Other bounds,
  field-balance interactions and local or partial-row scopes are refused.
- Positive total witness width and auxiliary width. Absent tables contribute
  no committed columns, openings or unconstrained claims. Empty per-table
  groups and inactive tuples retain their declared semantics.
- A shared coset `D = s<g_N>`, `N = 2^LogSize >= 2H`, disjoint from the
  order-`H` subgroup. Each table's quotient capacity obeys `chunks_t*h_t <= N`.
  As in the single-table profile, runtime counts equal the static parameters.

### Reduction boundary

`Interactions` retains each tuple's channel, side, arity and degrees, including
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
| `LogUp<F>` | Per record `m*(inv*(gamma-fp)-1)=0`; running signed sums of `m*inv` with first, transition and last constraints | Table claims sum to zero per channel; the maximum natural push and pull counts are each below the base-field characteristic |
| `GrandProduct<F>` | Prefix products of `m*(gamma-fp)+1-m`, separated by channel and side | Global push and pull products agree and an inverse claim makes the product nonzero |

The Boolean range constraints belong to the original multiset relation.
They are enforced alongside both reductions. An inactive row uses inverse zero
or product factor one, so its unused tuple cannot cause a denominator failure.
Active zero denominators cause an explicit prover abort. The LogUp count bound
prevents equality only modulo the characteristic from substituting for equality
of natural multiplicities. Random compression collisions, rational/product
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

The [machine protocol tests](../../common/tests/protocol/test_machine_stark.py) cover
both reductions, three external executions, differing table heights, absent
and idle memory, ordinary/simplification-disabled/storage-release compilation,
invalid relations and profiles, all commitment phases, and the exact nested
transcript order. The [reduction comparison](../../common/tests/protocol/test_air_interaction.py)
checks source auxiliary columns, claims and scoped residuals against the
independent staged reference. The [malicious-prover tests](../../common/tests/protocol/test_machine_stark_adversarial.py)
commit consistent false quotients and auxiliary columns. A valid execution of
another configured program with the same final result is rejected by the known
configuration obligation; disabling that obligation makes the control pass.

The implementation uses small test parameters and its own proof encoding.
One admission limitation remains: absent fixed-height and configured-height
tables still pass through polynomial shape checks, including the active-table
height bound `H`. This can refuse otherwise valid absent tables. Separating
height-independent table layout from active polynomial admission is needed to
cover the full optional-table contract above.

Arbitrary table counts, other interaction profiles,
hiding, production parameter selection, and a security theorem for the exact
composition remain separate work. The external VM relation also needs an
adequacy argument connecting its constraints to the intended execution semantics.
