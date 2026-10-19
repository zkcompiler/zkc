# KZG evaluation algebra

`kzg` evaluates a polynomial represented on a checked roots-of-unity domain
and computes its opening quotient. It selects no curve, trusted setup, pairing,
transcript or external wire format. Those choices belong to a construction such
as [Ethereum EIP-4844](../../constructions/ethereum/eip4844/README.md).

Construct `zkc::evaluation_domain::EvaluationDomain<F>` with `checked_roots`,
`two_adic` or `two_adic_bit_reversed`, then call `evaluations(unity, values)`
to establish equal extent. Private fields prevent replacing the admitted roots
or their order. These views enter only through local admission, not raw Entry
inputs or messages.

`evaluate(input: Evaluations<F>, z)` returns `p(z)`. At a domain point it reads
the corresponding value; elsewhere it uses the barycentric identity
`p(z) = (z^n - 1)/n * sum_i values[i] points[i] / (z - points[i])`.
`quotient(input, z)` computes that value itself and returns `(quotient, y)`.
The caller cannot supply an inconsistent `y`. The quotient retains the same
domain order, including the derivative value at a domain point.

`in_domain` and `position` accept an admitted `EvaluationDomain`. General
root-list admission checks nonempty size, nonzero field image of the size,
distinct points and every root equation; its pairwise scan is quadratic. The
fast power-of-two path checks the exact generator order and materializes points
in linear space, including the singleton domain. It requires no particular
installed two-adic generator and preserves a construction's selected generator.

[Independent polynomial tests](../../../common/tests/kernels/test_polynomial_views.py)
cover arbitrary root order, natural and bit-reversed order, singleton domains,
points inside and outside the domain, malformed domains and constructor privacy.
These are algebra and admission checks, not a KZG security proof.
