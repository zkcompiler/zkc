# Ring-expression interpretations

This model fixes a commutative coefficient ring `R`, an input type `I`, and
finite expression trees with constants, inputs, addition, multiplication and
negation. It specifies algebraic substitution independently of the
[native arena format](../../../../docs/spec/domains/ring-expressions.md).

## Evaluation and substitution

An assignment `I → R` gives each input one immutable value. Evaluation follows
the expression tree. The input list is syntactic: multiplication by zero does
not remove a read. Assignments agreeing on every listed input give equal
results. Definedness of a trace read must therefore be established by the
consuming relation before evaluation.

Replacing inputs by expressions and then evaluating equals evaluation under
the corresponding substituted assignment. A ring homomorphism transports both
coefficients and assigned values. For lane-indexed functions with pointwise
arithmetic, evaluation at each lane equals scalar evaluation on that lane.
These laws do not choose memory layouts or prove a SIMD implementation correct.

## Polynomial interpretation

An assignment `I → Polynomial R` substitutes full polynomials for inputs.
Evaluating the resulting polynomial at a point equals evaluating the original
expression on the input polynomials at that point. Multiplication remains
polynomial multiplication, including all high-degree terms.

An input degree bound determines a structural bound: constants have degree
zero, addition takes the maximum, multiplication adds, and negation preserves
the bound. If every used input polynomial satisfies its supplied bound, the
result's natural degree is at most the structural bound. Bounds are premises
of the interpretation; values at finitely many points cannot establish them.

## Finite AIR embedding

The existing finite AIR expression maps public inputs and `(offset, column)`
reads into disjoint ring-input namespaces. Translation preserves scalar
evaluation, polynomial interpretation and the AIR degree calculation with
public inputs weighted zero and reads weighted one. It does not alter row
scopes, turn finite reads into cyclic reads, or discharge read-window checks.

The declarations are in `Zkc.Algebra.RingExpression` and
`Zkc.Relation.AIR.RingExpression`. The native arena additionally has typed
field identities, explicit embeddings, DAG sharing, admission limits and byte
encoding. Correspondence for those representations is a separate obligation.
