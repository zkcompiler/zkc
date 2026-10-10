# AIR polynomials and a selected STARK profile

These modules construct a nonhiding, single-table argument from an admitted
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
| [`fri`](../fri/lib.zkc) | Low-degree testing and authenticated first-layer values at the returned positions |

Native Relation operations describe the immutable Bundle and substitute its
assertion expressions. Native polynomial, vector and commitment operations
implement their own mathematical contracts. The source modules choose the
quotient combination, challenge schedule and acceptance conditions.

`vanishing(height,begin,end,x)` evaluates the product over subgroup rows
`[begin,end)` at any field point, including excluded subgroup roots.
`vanishing_values` evaluates that same polynomial on the supplied two-adic
coset. Both use the complement shortcut where its denominator is nonzero;
the scalar helper falls back at a removable pole, and the vector helper uses
direct products on intersecting cosets. Full scopes keep geometric evaluation.
The STARK profiles use disjoint evaluation domains and retain the fast path.

## Statement and supported relation

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

The [polynomial helper tests](../../tests/protocol/test_air_polynomials.py)
compare scope products, column extensions and layouts with independent integer
Ext8 arithmetic. The [protocol tests](../../tests/protocol/test_air_stark.py)
exercise the imported AIR with separate prover/verifier Hosts, several domain
sizes and compilation modes, malformed statements and schedules, altered
commitments, claims and openings, and excluded-set exhaustion. Dishonest prover
variants retain consistent commitments and FRI folds but fail the outer
quotient or DEEP equation. Descriptor checks retain the commitment, claim and
query order through nested protocol calls. Independent integer interpolation
also reconstructs the complete quotient chunks, OOD claims and DEEP word. Native Bundle
polynomial tests independently check descriptors, degrees and substitutions.

[Adversarial controls](../../tests/protocol/test_air_stark_adversarial.py)
reach the verifier with a false trace, a compensated opening lie and a
column whose degree exceeds the declared bound. The
[statement-authority controls](../../tests/protocol/test_air_statement_authority.py)
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
