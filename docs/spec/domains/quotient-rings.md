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
| `quotient.intt` | `a, q, s` | Inverse evaluation using inverse-root parameter `s` |
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

`quotient.intt(E,q,s)` means
`a[j] = n^-1 * s^j * sum_k E[k] * s^(2*k*j) mod q`.
For inversion of a particular forward transform, `s` must equal `r^-1`.
Each raw call validates its own root; it cannot infer the provenance of a raw
input array or reject a different valid basis by examining its coefficients.
Compiler correspondence must therefore bind the basis across operations.
No bit reversal is visible at this interface. The inverse includes the `n^-1`
normalization and inverse twist.

`quotient.pointwise(a,b,q)` computes `a[i]*b[i] mod q`; it is not coefficient
convolution. It accepts the same canonical, equal-length, nonempty inputs as
`quotient.add`. Interpreting these values as evaluation coordinates requires a
common basis established by the calling algorithm. These contracts match the
[qualified external arithmetic profile](../realization/heir-arithmetic.md),
while ML-KEM's quadratic representation remains outside the full scalar profile.

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

## Execution and scope

The implementation borrows immutable operands and constructs a private exact
destination under the [native numerical contract](../runtime/numerical.md).
Repeated aliases are allowed. Output publication follows successful completion;
failure produces no partial result. Mathematical admission precedes work and
workspace admission, and numerical limits do not bound the prior input scan.

Multiplication uses schoolbook convolution, `O(n^2)` arithmetic and one
`n`-coefficient destination. A coefficient product fits in `u128`; reducing
each term bounds the running residue, including for `q=2^64-1`. Addition and
subtraction take `O(n)` work. The paired norm consumes a decreasing integer
budget while visiting every coefficient, avoiding overflow of the full sum.
These algorithms provide no constant-time execution guarantee.

The current native work scores are `8*n*n + 2*n + 1` for multiplication and
`8*n + 1` for addition, subtraction and the norm predicate, with checked score
arithmetic. A vector result reserves `256+8*n` retained bytes and
`256+16*n` managed bytes for overlapping staging and final storage. The norm
reserves the existing Boolean retained-value charge, with no coefficient
workspace. Element, output, work, managed-memory and allocation limits retain
their existing exhaustion diagnostics. Scores are admission bounds, not timing
measurements or promises to match a source loop's exhaustion behavior.

Projection uses score `8*(input_length+n)+1`. Pointwise multiplication uses
`8*n+1`. Radix-two transforms use one destination, `O(n log n)` arithmetic and
score `8*n*log2(n)+16*n+65536`, including a conservative parameter-check allowance.
Their retained and managed destination charges are the same as coefficient
arithmetic. Input validation and bounded primality/root checks precede work
admission. No persistent transform preparation or hidden scratch is allocated.

The [lattice library](../../../libraries/relations/lattice/README.md) composes
these operations into an arithmetic short-preimage predicate. Signature byte
decoding, signed-response bounds, challenge hashing, parameter authentication,
proof generation and cryptographic security remain separate contracts.
[Status](../../status.md) records native coverage; the
[design rationale](../../rationale/quotient-rings.md) explains the present
representation and external-dialect boundary. There is no maintained Lean
correspondence claim for these native operations.
