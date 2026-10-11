# Checked nested matrix collections

This rule is an instance of the ordered mathematical correspondence for
[finite computations](finite.md), under the installed field and matrix primitive
contracts and sufficient native capacity. It does not equate instruction counts,
allocations, retained storage, exhaustion, or arbitrary provider failures.

For a matrix `M` over the exact nominal field `F`, a vector `x` over `F`, and a
uniform scalar seed `s : F`, collecting the ordered fold of `s + a*b` over every
row gives the vector whose entry `r` is

```text
s + sum(c in [0, columns(M)), M[r,c] * x[c]).
```

The column analogue gives entry `c` equal to
`s + sum(r in [0, rows(M)), M[r,c] * x[r])`. Field associativity and commutativity
justify the installed contraction, including logical sparse zero entries. They
do not authorize changing a callback with effects, an opaque operation, a
predicate, a different nominal field, or an explicit implementation binding.

The outer domain is precisely the corresponding `indices(M)` axis. The inner
matrix view uses that same matrix and the actual outer index. The other factor
is the actual captured vector, identified through the nested call and callback
parameter mappings. The seed is a captured scalar or a field constant and is
independent of the outer index. The returned step has exactly the admitted
field multiplication and addition; either commutative operand order is allowed.
Additional ignored vector lanes and nested strict zips retain their admission.

If the outer extent is zero, the result is an empty vector. No inner domain
constructor or shape check is evaluated. Otherwise, constructors are admitted in
source order for the first outer index, zero: matrix view bounds precede that
view's inner extent, and each strict zip compares its first child's extent to
each subsequent child in order. Unused descriptor constructors retain their
checks. Successful first admission establishes the same shape equations for all
remaining outer indices; the exact outer indices domain establishes their
selector bounds. The callback then has no logical stop.

The nonempty branch performs exactly one `matrix.mul_vector` or
`matrix.transpose_mul_vector`, fills an outer-length vector with the uniform
seed, and adds the two vectors. A zero inner extent is admitted normally and
produces a vector containing the seed at every outer position. Shape disagreement
must be rejected by the explicit `control.require` guards before the native
matrix primitive. The selected native outcome interpretation maps those guards
to the original finite admission rejection (`rejected:require`); a native
`matrix-shape` backend failure is not substituted for that logical stop.

Each synthesized admission guard retains the inner finite declaration's
diagnostic location and its ordinary finite realization leaf site (`finite_N`
in admission emission order). The existing local expansion record associates
that leaf with the inner declaration and the original nested call path, relative
to the outer collection. Previously expanded helper paths remain full paths;
an encoded site is not reinterpreted as an authored leaf. Canonical local site
encoding, its 128-byte hashing threshold, and cumulative origin budgets are
shared with ordinary [local expansion](protocols.md#executable-local-calls-and-type-use).
Final expansion prefixes later caller paths and retains the inner location.
This is source provenance for diagnostics, not a cryptographic identity or a
promise to preserve the generated control structure and every executable site.

The preparation service retains an immutable source until an owned candidate
has been admitted and independently checked. Its checker reads actual domain
constructors, helper SSA, captures, scalar-law applications, seed and result,
and actual candidate operands, branch captures and ordered guards. It does not
consult the selector's recognition result. It reconstructs guard leaf identities,
locations and occurrence records from the retained source and checks them
against the candidate, including full paths when names are hashed. The checker
also preserves every
surrounding definition and its order, permits only used new primitive bindings,
and replaces only the outer finite declaration with a same-name Local function.
Ordinary finite realization consumes this accepted subject as its own source,
while projection structurally preserves the resulting accepted Local bodies.
