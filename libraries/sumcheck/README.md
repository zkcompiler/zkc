# Sumcheck

The pair-valued [multilinear protocol](lib.zkc) and coefficient-valued
[expression protocol](expression.zkc) share the same composition pattern.
They have different round messages and are not interchangeable encodings.

| Declaration | Contract |
|---|---|
| `Reduce` | Check each received round polynomial, draw and deliver a challenge, and return a remaining evaluation obligation |
| `Evaluation<F>` | Verifier's MSB-first point and expected value; ordinary data, not a certificate |
| `Sumcheck` | Complete public-table composition, including terminal evaluation |
| `sumcheck::expression::check`, `check_factors` | Check public factor tables or authenticated factor values against the captured expression |
| `sumcheck::check` | Check a multilinear evaluation against the caller's table, including its final dimension |

`Reduce` gives P its delivered point and residual table, and V its independently
recorded point and expected value. The same random service is threaded through
all rounds. The caller binds the original polynomial, its dimension and, when
applicable, its commitment before the relevant challenges. The `rounds` input
must agree between participants and is bounded by `Max`.

Each pair-valued round fixes one leading Boolean coordinate. An expression
round fixes one coordinate of every ordered factor table; its coefficient count
is `A::Degree + 1`, with `A::Inputs` factors and exactly one output. Expression
composition must check `A(f1(point), ..., fk(point))`, not an unrelated single
polynomial evaluation. P's residual preserves remaining entries/factor values.
After a partial prefix, the obligation is the sum of the remaining Boolean
rows, rather than a full-dimensional evaluation. The caller supplies the
remaining reduction or check.

With zero rounds the point is empty and the initial claim remains. The public
multilinear composition accepts only a one-entry matching table; the expression
composition requires exactly one row of `A::Inputs` factors and evaluates it.
Insufficient rounds reject the multilinear terminal predicate or stop at the
expression shape requirement. Invalid splits and malformed round coefficients
stop; a wrong final value returns false. These are distinct outcomes.

Public-table verification runs after the interaction, using the recorded point.
A malformed verifier table is therefore detected during this final local
computation. Received round checks still precede their challenges. Construction
handlers on a complete Sumcheck use `reduce.round`, `reduce.challenge` and
`reduce.delivery`; direct reductions use `round`, `challenge` and `delivery`.

See the [composed client](../../examples/projects/composed-sumcheck/README.md)
for two independently discharged reductions and the public-table clients for
[multilinear](../../examples/projects/sumcheck/README.md) and
[expression](../../examples/projects/expression-sumcheck/README.md) Entries.
