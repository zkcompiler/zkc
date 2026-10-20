# AIR equations

`air` interprets a captured [relation Bundle](../../../docs/spec/domains/relation-bundles.md)
using ordinary library functions. It selects no commitment, transcript, field
preset or participant schedule.

| Module | Responsibility |
|---|---|
| [polynomial](polynomial.zkc) | Scope vanishing polynomials, quotient chunk bounds, coefficient-block splitting and recombination |
| [table](table.zkc) | Ordered relation inputs, rotations, configuration authority, assertions, quotient identities and opening equations |
| [interaction](interaction.zkc) | Record compression, signed field weights, Boolean multisets, LogUp and grand-product equations |

Common interpolation, coset arithmetic, vector layouts and opening quotients
come from [`zkc`](../../core/README.md). Complete single-table and whole-Bundle
schedules live in [`stark`](../../arguments/stark/README.md). This direction keeps relation
arithmetic usable without selecting a proof system.

## Contracts

Columns are contiguous internally. Relation inputs retain declaration order;
cyclic read offset `k` means evaluation at `g_height^k X`. Public scalars,
configuration columns and public columns retain their verifier authority.
Witness openings remain obligations until an enclosing protocol authenticates
and checks them. Shape records are ordinary values, not proof certificates.

`table::read_quotients(slots, witness, assignments, height, zeta, rho, initial,
first_weight)` takes a checked `coset::ColumnBatch` for `witness`. Construct it
with `coset::column_batch(coset::coset_domain(shift, size), width, values)`.
Only witness slots (kind 1) contribute quotients and consume weights, in declared
read order; the returned weight is `first_weight * rho^witness_count`. Rotated
points are constructed before the native column/pole scan. Known reads retain
their separate verifier checks. Even an empty witness selection checks the
trace-rotation domain, checked batch geometry and initial extent before returning
the unchanged values and weight.

`vanishing(height, begin, end, x)` evaluates the subgroup product on `[begin,end)`.
The vector form evaluates the same polynomial on a coset. Both use complement
products where valid and direct products at removable poles. `split_quotient`
checks the coefficient capacity before padding into blocks. `recombine` uses
increasing powers of `x^height`; an empty list gives zero.

`interaction::Reduction<F>` specifies auxiliary layouts, scoped equations,
claims and global closure. `LogUp<F>` and `GrandProduct<F>` implement this
contract with actual prefix scans. `supports(kind)` admits signed field-balance
records (`0`) or bound-one natural multisets (`1`). LogUp supports both; the
grand product supports multisets. Only multiset records receive Boolean range
equations. Their scalar helpers also support independent
[LogUp clients](../../../common/tests/fixtures/projects/logup-rows/README.md). Multiplicity and
characteristic assumptions belong to the enclosing argument's admission; the
interface supplies no cryptographic theorem.

The [polynomial tests](../../../common/tests/protocol/test_air_polynomials.py)
compare against independent extension-field arithmetic. The
[interaction tests](../../../common/tests/protocol/test_air_interaction.py)
compare both reductions with the independent staged reference. Full schedules,
malicious prover controls and supported-profile limits are documented with STARK.
