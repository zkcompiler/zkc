# Table expressions mean more than the quadratic compiler accepts

A [table expression](../spec/domains/polynomials.md#table-expressions) is a
list of weighted terms, each with an ordered list of factor occurrences. Every
finite list has a meaning, including the empty sum, the empty product and
dimension zero. The
[quadratic table compiler](../spec/profiles/sumcheck/quadratic.md#table-compilation)
accepts terms with at most two occurrences and returns `none` for any other.
When it succeeds, its output equals the source meaning at every point. When it
fails, the
[table-bound entry](../spec/profiles/sumcheck/interactive.md#checked-evaluation-and-table-bound-entry)
refuses before any interaction or coin consumption.

## Alternatives

**Restrict every source to degree two.** The limit of one verifier profile
becomes part of the compiler's foundation. A
[profile](../spec/profiles/README.md) restricts its own judgment; it does not
specialize the language to its degree bound.

**Compile through a general sparse polynomial type or a degree-indexed
algebra.** More expressions would compile, but the representation, its
algorithms and their proofs would be chosen before a supported workload needs
any of them.

## Reason

A partial compiler states the supported subset honestly and leaves the point
of extension visible: the meaning is already there for the terms it declines.
Its test counts occurrences. A repeated identifier counts twice, which is
right, because two occurrences of a table denote the square of its extension
and not the extension of a
[pointwise product](../spec/domains/polynomials.md#equality-away-from-boolean-points).
The test is sufficient, not exact: three factors on disjoint coordinates are
declined even when their degree in each coordinate fits. A refusal claims
nothing about the expression.

The quadratic coefficient object has `3^n` coefficients. It connects the
source meaning to the verifier's terminal evaluation; it is not the proposed
representation of tables. Evaluating a multilinear extension in time linear in
the table, and restricting coordinates in order without expanding
coefficients, are standard [1], so a table or
[residual](../spec/domains/polynomials.md#ordered-residuals) implementation can
refine the source meaning directly. The conversion theorem gives no cost bound.

## Reopen when

A required expression has a term with more than two occurrences, or an
efficient factor or residual plan needs a representation that the quadratic
object cannot supply.

## References

1. Justin Thaler, *Proofs, Arguments, and Zero-Knowledge*, §3.5, Lemmas
   3.7–3.8, and §4.4.
   [Author PDF](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf).
