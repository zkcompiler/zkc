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

## Arena sharing

An arena is a list of nodes whose operands are indices; it is well formed when
every operand index is strictly below the node's own index. Unfolding with a
fuel bound turns a node into a tree of the model above, or nothing when the
fuel is exhausted or an index is missing. In a well-formed arena every node
resolves with any fuel above its index, and the resolved tree does not depend on
the fuel.

A node map `f` from arena `A` into arena `B` is label preserving when, for every
index `i` of `A`, the node `B[f i]` exists, carries the same constant or input
label as `A[i]`, and has operands `f` of the operands of `A[i]`, in order. For
such a map every node of a well-formed `A` unfolds, at every fuel, to the same
tree as its image, and an ordered output list, including repeated positions,
unfolds to the trees of its image list. Evaluation, degree bounds and syntactic
input lists transfer because they are functions of the tree. The map is purely
structural: a product by zero, a folded sum or swapped operands are not images.

A node map may be required only on a *live* set of nodes that is closed under
operands. Every live node of a well-formed arena then unfolds, at every fuel, to
the same tree as its image, and live ordered outputs unfold to the trees of
their image list; nodes outside the set, which no live node reaches, need no
image. Dropping the operations a result never reaches is this restriction with
the nodes reachable from the outputs as the live set.

## Pointwise maps

A map operand is either a scalar shared by every row or a list of row values.
The row count of an operand list is defined only when at least one operand is
rowwise and every rowwise operand has the same length, within the vector limit;
otherwise the count refuses with `map-rows`, `vector-shape` or `vector-limit`.
Every rowwise operand takes part in this check, including operands the formula
never reads. A formula whose inputs are positions in the operand list is mapped
by evaluating it once per row, reading row `i` of each rowwise operand and the
shared value of each scalar operand. An input beyond the operand list refuses
with `map-signature` before any row is read.

A successful map has the common row count and, at row `i`, the formula
evaluated on that row (`map_length`, `map_coordinate`); equivalently it is the
lane interpretation above on the lanes `0, …, n-1` (`map_lanes`). Two rowwise
operands of different lengths never succeed, whatever the formula reads
(`map_shape`, `map_shape_code`), and scalar operands alone never succeed
(`map_scalars`).

Three laws describe what a realization may do with a map without changing its
rows. Fusion: mapping an outer formula over the outputs of inner maps of the
same operands equals mapping the substituted formula over those operands in one
pass; the composed map reads the same operands, so a shape refusal is preserved
(`map_substitute`). Hoisting: a subformula whose inputs are all scalar operands
has one value for every row, and replacing it by that value preserves a
successful map (`map_hoist`). Dead nodes: an arena node that no output reaches
is covered by the restricted node maps of the sharing section. None of these
laws removes a shape check; each applies to the same operand list.

## Pointwise values and interpolation

Mapping a formula over the lists of values that input polynomials take at
ordered points gives the list of values of the substituted polynomial at those
points (`map_polynomial`). This is the only sense in which a pointwise map
computes a formal polynomial: the rows are evaluations, not coefficients.

Over a field, interpolating those pointwise values at a finite set of nodes
recovers the substituted polynomial if its structural degree bound,
derived from degree bounds on the input polynomials, is below the node count
(`interpolate_polynomial`). When the substituted polynomial has degree at least
the node count, the interpolant is a different polynomial that agrees with it
on the nodes (`interpolate_ne_polynomial`); it may also agree at some other
points. The structural bound is sufficient and can overestimate the actual
degree. Agreement at the nodes alone does not establish either bound.

## Finite AIR embedding

The existing finite AIR expression maps public inputs and `(offset, column)`
reads into disjoint ring-input namespaces. Translation preserves scalar
evaluation, polynomial interpretation and the AIR degree calculation with
public inputs weighted zero and reads weighted one. It does not alter row
scopes, turn finite reads into cyclic reads, or discharge read-window checks.

The declarations are in `Zkc.Algebra.RingExpression`,
`Zkc.Algebra.RingExpression.Sharing`, `Zkc.Algebra.RingExpression.Pointwise`
and `Zkc.Relation.AIR.RingExpression`. The native arena additionally has typed
field identities, explicit embeddings, admission limits and byte encoding, and
its sharing checker is native code; the native map realizer and its
correspondence reader are native code as well. Correspondence for those
representations is a separate obligation.
