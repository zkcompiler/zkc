# Negacyclic quotient rings

For integers `2 <= q <= 2^64-1` and `n > 0`, define
`R(q,n) = (Z/qZ)[X]/(X^n+1)`. The modulus may be composite and the degree
need not be a power of two. A representative has exactly `n` coefficients,
each in `[0,q)`, in ascending degree order. Leading zero coefficients remain;
zero is the length-`n` zero vector. Admission rejects noncanonical residues
rather than reducing them or interpreting them as signed words.

These values have a different meaning from both
[formal and normalized field polynomials](polynomials.md) and
[Ring expression assets](ring-expressions.md). The coefficient ring and
polynomial quotient need not be fields. For example, `(X-4)(X+4)=0` in
`R(17,2)` although both factors are nonzero. Field inversion and cancellation
laws do not apply to arbitrary quotient elements.

## Operations

The executable contracts have no static binding arguments or attributes.
Their installed implementations are `native/` followed by the contract name.
Both coefficient inputs use the existing `indices` carrier; `q` and `bound`
use `index`. The nonempty degree is the common input length.

| Contract | Inputs | Result |
|---|---|---|
| `quotient.add` | `a, b, q` | Canonical coefficients of `a+b` |
| `quotient.subtract` | `a, b, q` | Canonical coefficients of `a-b` |
| `quotient.multiply` | `a, b, q` | Canonical coefficients of `a*b` modulo `X^n+1` |
| `quotient.norm_within` | `a, b, q, bound` | Boolean integer norm predicate below |
| `quotient.project` | `a, q, n` | Reduction of the finite sequence as a polynomial into `R(q,n)` |
| `quotient.ntt` | `a, q, r` | Natural-order evaluation at the odd powers of `r` |
| `quotient.intt` | `a, q, r` | Inverse evaluation in the same forward-root basis `r` |
| `quotient.pointwise` | `a, b, q` | Coordinate-wise modular products |

For multiplication, the coefficient at `k` is the canonical residue modulo
`q` of

```text
sum_{i+j=k} a[i]*b[j] - sum_{i+j=k+n} a[i]*b[j].
```

All arithmetic in this definition is over integers before reduction. Host
integer wrapping, a different polynomial modulus, and pointwise multiplication
of coefficient arrays do not implement this contract.

Define `center_q(c) = c` for `c < ceil(q/2)`, and `c-q` otherwise. Its range
is `[-floor(q/2), ceil(q/2))`; the midpoint of an even modulus is negative.
`quotient.norm_within(a,b,q,B)` returns exactly

```text
sum_i center_q(a[i])^2 + sum_i center_q(b[i])^2 <= B.
```

The sum and comparison are over integers, with an inclusive bound. Neither
field arithmetic nor floating-point approximations are involved. A total norm
larger than the machine accumulator range must still produce `false` for an
admitted `index` bound. This predicate measures the specified representatives;
it does not recover an original signed integer from its residue.

Malformed moduli, empty degree, unequal lengths and noncanonical residues
refuse with `quotient-modulus`, `quotient-degree`, `quotient-shape` and
`quotient-residue`, respectively. Operand-type or operation mismatches refuse
with `quotient-operands`. Native admission independently checks these conditions
at each reached invocation, including calls without the source library wrapper.

## Projection and transform coordinates

`quotient.project(a,q,n)` intentionally accepts any finite unsigned sequence,
including empty input and coefficients greater than or equal to `q`. It returns
the canonical coefficients of `sum_i a[i] X^i` in `R(q,n)`. Block `i/n` contributes
with alternating sign to coefficient `i mod n`. This explicit reduction is
distinct from validating an already canonical coefficient representation.
Only `q >= 2` and `n > 0` are mathematical parameter preconditions; native size
and allocation admission also apply.

Transforms admit an odd prime `q < 2^31`, a power-of-two input length
`2 <= n <= 65536`, and `2n` dividing `q-1`. The root parameter is a canonical
residue with `r^n = -1 mod q`, giving exact order `2n` under these conditions.
Unsupported ring parameters refuse with `quotient-transform-profile`; invalid
root coordinates refuse with `quotient-transform-root`. Input residues remain
canonical and are independently validated. Forward coordinates are

```text
E[k] = sum_j a[j] * r^((2k+1)*j) mod q.
```

`quotient.intt(E,q,r)` uses `s = r^-1 mod q` internally and means
`a[j] = n^-1 * s^j * sum_k E[k] * s^(2*k*j) mod q`.
Forward and inverse calls use the same forward root parameter.
Each raw call validates its own root; it cannot infer the provenance of a raw
input array or reject a different valid basis by examining its coefficients.
Compiler correspondence must therefore bind the basis across operations.
No bit reversal is visible at this interface. The inverse includes the `n^-1`
normalization and inverse twist.

`quotient.pointwise(a,b,q)` computes `a[i]*b[i] mod q`; it is not coefficient
convolution. It accepts the same canonical, equal-length, nonempty inputs as
`quotient.add`. Interpreting these values as evaluation coordinates requires a
common basis established by the calling algorithm. ML-KEM's quadratic decomposition is outside this full scalar transform profile.

The independent kernel API distinguishes borrowed coefficient polynomials from
borrowed evaluations. Evaluations retain an admitted transform basis; inverse
transforms and pointwise products reject a different basis before writing a
destination. Admitting a raw array as evaluations checks canonical residues and
extent, but cannot establish its provenance. Compiler correspondence must bind
actual roots, producers and consumers across the complete algorithm.

## Source views

[`zkc::quotient`](../../../libraries/core/polynomial/quotient.zkc) owns
`Polynomial<Q,N>` with private coefficient storage. `polynomial<Q,N>(data)`
requires static `2 <= Q`, `1 <= N`, exact length `N` and residues below `Q`.
Both static parameters participate in nominal source identity. `add`,
`subtract`, `multiply` and `norm_within` accept operands with identical `Q,N`;
the arithmetic operations return that same type. `coefficients` observes its
canonical storage. Construction guards use ordinary source `require` rejection.

This is a checked library value, not a native refinement type or proof object.
Entry inputs and messages carry raw `Indices`; each recipient constructs its
own view. Lowered native operations retain the explicit modulus operand and
validate actual coefficient arrays. A serialized native program cannot assert
the source invariant merely by naming a record. No evaluation-form or NTT
representation crosses this API.

## Mathematical values and realization

The source [`zkc::quotient_math`](../../../libraries/core/primitives/polynomial/quotient_math.zkc)
exposes `Element<Q,N> = formal("quotient",Q,N)` and total mathematical
projection, canonical observation, addition, subtraction and multiplication.
`project` reduces any finite unsigned sequence; it does not assert that its
input is canonical. This differs from the checked `Polynomial<Q,N>` constructor
above, which rejects noncanonical storage. Both views have this page's exact
ring meaning. Formal values can cross transparent mathematical helper calls,
but executable signatures, messages and source relation-data leaves exclude them.

[Poly IR](../ir/mathematics.md) retains modulus and degree until realization.
The coefficient recipe projects inputs, schedules the selected ring operations
and erases canonical observations to their actual coefficient SSA value. An
independent reader checks the original operations against actual contracts,
modulus/degree constants, ordered operands, outputs, bindings and occurrence
association; it does not rerun the emitter. A same-typed arithmetic substitution
is still a source correspondence failure.

Mathematical totality does not make installed calls infallible. The current
native path retains reached admission and work/storage/publication failures.
A different algorithm must state its resource and observation relation before
it can replace this realization. These compiler checks and arithmetic tests do
not establish a native execution or cryptographic theorem.

[Prepared matrix products](quotient-matrices.md) use exact bounded integer lifts
over independent compute primes while retaining this protocol-ring meaning.
