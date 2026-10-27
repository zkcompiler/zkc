# Prepared exact quotient-ring matrices

The local `quotient_matrix` value represents a checked matrix over
`R(q,n) = (Z/qZ)[X]/(X^n+1)` and a nonnegative signed-digit bound `B`.
Its compiler representation is `!runtime.quotient_matrix`, a local execution
value rather than a formal `!poly.quotient` value. Its meaning uses the [quotient-ring coefficient and centered-representative
conventions](quotient-rings.md). Compute-prime residues are an implementation
representation; they do not change the protocol modulus `q`.

## Executable interface

The bindings have no static arguments or operation attributes. Their native
implementation names are `native/` followed by the contract name.

| Contract | Inputs | Result |
|---|---|---|
| `quotient.prepare_matrix` | `indices, index q, index n, index rows, index columns, index B` | `quotient_matrix` |
| `quotient.matvec` | `quotient_matrix, indices` | `indices` |

Preparation requires `q >= 2`, positive rows and columns, and a power-of-two
`n` in `[2,65536]`. The input contains exactly `rows*columns*n` canonical
coefficients, in row-major, then column, then ascending coefficient order.
Each polynomial therefore occupies one contiguous length-`n` segment.
The modulus may be composite or even and may reach `2^64-1`.

A product input contains exactly `columns*n` canonical protocol residues.
Every coefficient `d` must satisfy `abs(center_q(d)) <= B`. This check concerns
the actual input, including negative digits and the negative even midpoint.
The result contains `rows*n` canonical coefficients of

```text
result[row] = sum_column matrix[row,column] * digits[column] in R(q,n).
```

The source module [`zkc::quotient_matrix`](../../../libraries/core/primitives/polynomial/quotient_matrix.zkc)
exposes `PreparedMatrix`, `prepare` and `multiply`. The value is private,
immutable local computation data with Copy and Drop. It has no wire encoding,
equality operation, byte import, or unchecked constructor. Copies share the
prepared storage. A verifier may prepare a local matrix from its own admitted
inputs; private preparation is not a proof, capability or public binding.

## Exact RNS realization

The installed provider chooses a prefix of the compute primes
`[2013265921, 1811939329, 469762049]`. Their corresponding generator candidates
are `[31,13,3]`; preparation independently validates primality and the selected
primitive `2n`-th roots using the full scalar transform contract. Coordinates
use natural evaluation order and the same forward-basis identity for forward
and inverse operations. Inversion derives the reciprocal root internally and
normalizes by the degree.

Let `A` be the largest absolute centered matrix coefficient and `P` the product
of the selected compute primes. Let `B_eff = min(B, floor(q/2))`: canonical
protocol residues already satisfy this tighter centered magnitude bound.
One chunk of `C` columns has integer coefficient magnitude at most
`C*n*A*B_eff`. The declared `B` remains the input admission contract. Its required reconstruction condition is

```text
2*C*n*A*B_eff < P.
```

Preparation selects the smallest prefix that can lift the whole row. If the
three-prime product cannot lift the whole row, it chooses
`C = floor((P-1)/(2*n*A*B_eff))`, capped at the row width. Zero `A` or `B_eff` permits
one whole-row chunk. A zero capacity refuses preparation. Successive exact floor divisions avoid
overflowing the denominator; an otherwise representable capacity is not
refused merely because `2*n*A*B_eff` would overflow a machine word.

Matrix coefficients and digits first use their centered protocol representatives,
then reduce into each compute prime. Each safe chunk is accumulated in transform
coordinates, inverted, reconstructed by signed Garner conversion, reduced modulo
`q`, and added to the result modulo `q`. The triangle bound makes each centered
lift equal to its intended integer coefficient. Reduction modulo `q` commutes
with summing the exact chunks. The argument requires neither primality of `q`
nor an NTT root modulo `q`.

This differs from merely converting a residue modulo `P` into another basis.
Without the capacity premise, a correct centered conversion can describe the
wrong integer for the intended product. The prepared carrier retains the
validated basis, dimensions, digit bound and chunk plan with its coordinates.
A caller cannot attach different metadata to arbitrary stored transforms.

## Refusal and storage

Preparation validates modulus, nonzero degree, exact shape, transform profile,
and every residue before performing transforms. A nonrepresentable host shape
refuses. Product admission validates exact input shape and all residues/digit
bounds before destination mutation. Errors use `quotient-modulus`,
`quotient-degree`, `quotient-shape`, `quotient-transform-profile`,
`quotient-residue`, `quotient-rns-capacity`, `quotient-digit-bound`, and
`quotient-operands`. These remain reached, ordered partial operations even when
their results are unused. Ordinary policy exhaustion is separate.

For `L` limbs, prepared storage contains `L*rows*columns*n` unsigned 64-bit
coordinates. Its retained charge is the actual coordinate capacity times eight,
plus `sizeof(PreparedMatrix)`, `sizeof(Value)`, and the ordinary 256-byte wrapper
allowance. Preparation uses `n` temporary words and transfers its owned coordinate
vector directly into the immutable carrier. The charged final storage and scratch
coexist; there is no second coordinate allocation during publication. Each product retains `rows*n` output words plus the
ordinary 256-byte value charge and uses
`L*columns*n + (L+1)*n` scratch words. Inputs and prepared storage remain immutable.
The input vector is transformed once per limb and reused across rows and chunks.

Reached preparation first admits the coefficient array's object limit, then
charges `8*coefficient_count + 3*65536` work units before scanning coefficients
or constructing compute bases. Product invocation rechecks the prepared object's
current policy, admits its input array limit, and charges four units per input
coefficient before checking shape, residues and the declared bound. These
precharges are retained even when admission refuses. Successful admission then
checks the output allowance, charges the kernel's conservative transform/product
`work()` score, and reserves scratch plus final storage. Work charges include
scans, transforms, coordinate products and reconstruction; they are admission units rather than timing estimates.
Allocation failure and exact work, scratch, output and live-value limits refuse
without publishing a result. A prepared object retains mathematical facts,
not the preparing backend's policy or invocation authority. Actual installation
identity, active frames, timing grants and shared execution allowances remain
under the ordinary runtime contract. No constant-time execution is claimed.

The installed provider supports this profile rather than arbitrary exact
integer matrix arithmetic or wider protocol moduli. Existing schoolbook
quotient operations remain available for other ring dimensions. This delivery
provides a source-to-native arithmetic consumer; a general compiler rewrite
from arbitrary formal module expressions, RNS candidate readers, and a Lean
native correspondence theorem are separate work.
