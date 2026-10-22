# External quotient arithmetic profile

The optional [HEIR arithmetic package](../../../compiler/external/heir/README.md)
defines a compiler-internal comparison for arithmetic over
`R(q,n) = (Z/qZ)[X]/(X^n+1)`. It does not replace the
[checked coefficient operations](../domains/quotient-rings.md). The profile is
conditional on canonical input coefficients; native entry validation and
execution admission remain separate obligations.

## Subject and coordinates

An admitted module contains exactly one defined, single-block `func.func`, with
fixed, one-dimensional `tensor<nxi32>` arguments and results. The common degree
is a power of two between 2 and 65536. The coefficient modulus is an odd prime
less than `2^31`, and `2n` divides `q-1`. Integer storage carries values in `[0,q)`.
No tensor encoding, function argument/result attributes, control flow, external
callee or unknown operation attribute is admitted. Function identity, visibility,
signature, operand positions and result order belong to the compared subject.

The admitted operations are `mod_arith.encapsulate`, standard `mod_arith.lift`,
`polynomial.from_tensor`, `polynomial.to_tensor`, `polynomial.add`,
`polynomial.sub`, `polynomial.mul`, `polynomial.ntt`, `polynomial.intt` and
`func.return`. Tensor inputs enter through encapsulation; ring values are formed
with the exact `X^n+1` quotient. All arithmetic uses one ring per function.
Outputs observe standard lifts of coefficient tensors. Constants, RNS values,
centered lifts, norm observations and arbitrary upstream operations require
additional reader coverage before admission.

For a primitive `2n`-th root `r`, evaluation coordinates mean

```text
E[k] = sum_j a[j] * r^((2k+1)*j) mod q,  0 <= k < n.
```

Coordinates use natural `k` order. Forward transforms carry `r`; inverse
transforms carry `r^-1` and normalize by `n^-1`. The reader validates the root's
coefficient type, canonical value and degree, and checks `r^n = -1 mod q`.
Under the admitted prime and power-of-two conditions, this gives the required
exact order. Evaluation arithmetic requires the same root on both operands.
An inverse transform must match the incoming evaluation basis. A label saying
only `form=eval` does not establish this condition.

`mod_arith.encapsulate` does not validate or normalize an integer buffer in the
selected lowering. Callers must establish canonical input values before entering
this subject. Reading a well-typed arithmetic module does not establish that
precondition for an external buffer.

## Independent comparison and publication

The reader walks actual SSA definitions separately in the source and candidate.
It assigns an indeterminate to each ordered input ring element, normalizes sums,
differences and products as commutative ring expressions modulo `q`, and tracks
coefficient/evaluation forms and roots independently of that normalization.
Equal normalized output expressions with equal interfaces are sufficient for
acceptance under the stated input interpretation. Quotient elements are never
treated as field elements: inversion and cancellation are not used.

The finite reader admits at most 1024 inputs and results, monomials of at most
64 factors, and a budget of one million operation/operand/result and expression
inspection units per subject. Unsupported expressions and capacity exhaustion
refuse. A refusal does not establish mathematical inequivalence.

`placeTransforms` first admits the source, clones it, runs the selected HEIR
placement, root attachment, canonicalization and common-subexpression passes,
and compares the actual candidate with the retained source. Failure returns no
candidate. Placement minimizes the upstream transform cost subject to its
solver limits; this is not a latency or memory optimum.

The comparison covers the structured arithmetic edge. It does not prove that
Polynomial-to-ModArith lowering, bufferization, LLVM generation, compiled code,
or runtime execution realizes that edge. Qualification tests exercise those
later stages on bounded inputs. Connecting the package to the main compiler
requires the existing [candidate discipline](../../compiler/verification.md),
source admission and managed execution contracts at each subsequent boundary.

## Relation to other profiles

Falcon and ML-DSA arithmetic fit the full scalar NTT condition at their usual
ring parameters. ML-KEM's `q=3329,n=256` does not; it uses quadratic components
and needs a separately interpreted product representation. Composite moduli
and arbitrary positive degrees remain supported by the coefficient fallback,
not by this transform profile.

RNS basis conversion, centered integer reconstruction, signed decomposition,
encoding and norm checks are separate mathematical observations. They cannot be
admitted by extending this operation list without interpreting their meaning
and capacity conditions. No Lean correspondence or protocol-security claim is
made by this native comparison.
