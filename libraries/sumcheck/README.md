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

`Reduce` accepts a checked `multilinear::Table<F>` at P and returns its residual
as the same view, preserving width and remaining dimensions. P also receives
its delivered point; V receives its independently recorded point and expected
value. Construct a table from raw data before the first reduction; pass the
residual directly to later reductions. The same random service is threaded through
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
The complete `Sumcheck` wrappers check the prover table against the full
`rounds` dimension before the first message. `Reduce` permits a partial prefix;
requesting more rounds than its residual dimension stops before sending.
Malformed round
coefficients stop; a wrong final value returns false. These are distinct outcomes.

Public-table verification runs after the interaction, using the recorded point.
A malformed verifier table is therefore detected during this final local
computation. Received round checks still precede their challenges. Construction
handlers on a complete Sumcheck use `reduce.round`, `reduce.challenge` and
`reduce.delivery`; direct reductions use `round`, `challenge` and `delivery`.

See the [composed client](../../examples/projects/sumcheck/composed/README.md)
for two independently discharged reductions and the public-table clients for
[multilinear](../../examples/projects/sumcheck/README.md) and
[expression](../../examples/projects/sumcheck/product/README.md) Entries.

## Source relation contracts

The pair-valued `Sumcheck<F, Max>` checks a public table indexed by Boolean vectors,
using MSB-first variable order. Its `public_sum` target selects V's `values`, V's initial `claim`,
and V's returned `accepted` Boolean. `Sum<F>` is a total mathematical fold of the
selected vector. It does not check the vector's shape; decoding and dimension
are separate obligations of a property consumer and of the executable checker.

`Reduce<F, Max>` returns V's `Evaluation { point, value }` and P's residual table.
Its `initial_sum` input clause uses `TableSum<F>` over the original table entries.
That clause is an authored input proposition, not a runtime guard or a claim
that an adversarial initial statement is true. Purpose `parameter` identifies a
mathematical argument; it does not assign authority, secrecy, or quantifiers.

A residual security request must fix one original table before interaction and
reuse it in both the initial sum and the residual predicate:

```
length(pointV) = rounds
sum over remaining Boolean variables of originalTable(pointV, suffix) = valueV
```

For the public wrapper, this fixed table must decode V's input vector. For a
reduction experiment it may be a typed external parameter; any agreement with
P's runtime input is an explicit additional premise. A separate existential
table for each clause, or substitution of P's returned residual for the original
table, changes the property and can make it vacuous.

The source currently has no formula-backed residual continuation. Dynamic
prefix restriction uses Local operations; the total mathematical layer cannot
call those operations. A monomorphic opaque relation can express a continuation
clause, but the current opaque declaration profile cannot express the generic
field/table signature of this library.
The Lean source-contract client therefore exposes an explicit external residual
request with checked output selectors. A caller needs a terminal discharge
against that same fixed table before claiming acceptance. This limitation is
not hidden behind a placeholder source relation or a new compiler primitive.

The formal source adapters concern retained concrete instantiations and retain
their actual count maxima, malformed-input behavior, stops, and uniform-service
assumptions. The total source fold's structured interpretation also retains
finite-domain capacity admission. These interfaces establish no native compiler,
provider, commitment-opening, or Fiat–Shamir correctness by themselves.

See the [checked contract bindings](../../lean/ZkcExamples/Structured/SumcheckContractBindings.lean),
[fixed-table call instantiation](../../lean/ZkcExamples/Structured/SumcheckContractInstantiation.lean),
[complete clause interpretations](../../lean/ZkcExamples/Structured/SumcheckContractInterpretations.lean),
and [optional source bounds](../../lean/integrations/arklib/ZkcSecurity/Examples/CausalSumcheck/SourceContracts.lean).
They retain source-formula adequacy and fixed-table assumptions separately from
probabilistic acceptance and residual truth.
The public caller's proof uses the child's residual bound through a generic
probabilistic bind rule. It checks the actual terminal on arbitrary returned
point/value pairs, so the caller theorem also applies to a replacement child
with the same returned ABI and residual guarantee. The child's implementation
and its own bound are proved separately.

The expression-valued variant in `sumcheck::expression` has its existing arena
semantics and is outside these pair-valued source-contract adapters.
