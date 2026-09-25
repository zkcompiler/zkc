# Constraint relations and protocol views

A constraint representation defines a [relation family](../properties/relations.md#relation-families-and-instances).
Its public layout, mathematical domain and constraints determine which statements
and witnesses satisfy it. A witness generator is a separate partial computation;
its outputs do not define the set of permitted witnesses. Importing constraints
also does not select a proof protocol, transcript construction or cryptographic
backend.

This chapter defines two domain views: sparse rank-one constraints and finite
arithmetic traces. Neither is a mandatory representation for other relations or
for directly authored group protocols. [Source encoding adequacy](../properties/relations.md#source-encoding-adequacy)
is a separate obligation from the meaning of either view.

## Sparse rank-one constraints

Fix a commutative ring `F`, dimensions `m,n`, and three matrices
`A,B,C : Fin m → Fin n → F`. The row predicate on an assignment `z` is:

```text
Rows(z) := ∀ i, (A z)[i] * (B z)[i] = (C z)[i].
```

Fix a bijection from the disjoint slots `ONE`, `Public(Fin p)` and
`Witness(Fin w)` to `Fin n`. In particular, `n = 1+p+w`; no coordinate is
unclassified and public slots cannot alias. For statement `x : Fin p → F`:

```text
Bound(x,z) := z[ONE] = 1 ∧ ∀ j, z[Public(j)] = x[j]
R(x,z) := Bound(x,z) ∧ Rows(z).
```

Equivalently, a witness-only family inserts `1` and `x` into their fixed slots
and supplies the remaining `w` coordinates. Every bound arbitrary assignment
can be reconstructed this way. Auxiliary variables belong to those witness
coordinates; they need not be uniquely determined by the source witness.

Homogeneous rank-one equations always admit the all-zero assignment. They do
not enforce `ONE = 1`, even if one row is `ONE * ONE = ONE`. Public values must
also be bound independently. A protocol using a committed assignment must
establish these equalities for the actual committed coordinates. Comparing
uncommitted prover-supplied values with the statement is insufficient.

### Sparse representations and views

A sparse linear form is a finite list of `(column, coefficient)` pairs, with
meaning `sum_(j,a) a*z[j]`. Duplicate columns add; zero terms contribute zero.
Canonical external encodings may require sorted, unique columns and omit zeros.
That encoding restriction does not change the additive meaning of internal
contractions, which can create repeated columns.

The protocol-facing views are:

```text
products(z)              = (A z, B z, C z)
contract_M(u)[j]          = sum_i u[i] * M[i,j]
evaluate_M(u,v)           = sum_i sum_j u[i] * M[i,j] * v[j]
evaluate_M(u,v)           = dot(contract_M(u),v)
```

These are [matrix contraction laws](vectors.md#linear-combinations), with exact
row and column dimensions. Sparse storage, dense storage and formulas for
structured matrices can implement the same view under an explicit denotation
law. Their resource behavior remains a separate execution obligation.

For Boolean-cube dimensions, use the established
[ordered multilinear basis](polynomials.md#multilinear-extension):

```text
M̃(r,s) = sum_i sum_j χ_i(r) * M[i,j] * χ_j(s).
```

Rows and columns have independent dimensions. Evaluation at non-Boolean points
is part of this definition. It must not be replaced by pointwise evaluation of
an unrelated polynomial product. Padding adds zero matrix entries and zero
assignment cells at specified positions; it preserves the original public and
ONE layout. The native consumer's minimum cube size is an engineering choice.

Coefficient normalization preserves the matrix denotation. Removing exact
duplicate row triples preserves every satisfying assignment because both row
sets cover each other. This does not justify deleting a different row that
happens to vanish on one generated witness. These mathematical laws do not by
themselves prove the native sorting, padding or deduplication algorithms.

## Finite arithmetic traces

Fix a nonempty trace `T : Fin h → Fin c → F` and a public statement. An
expression contains field constants, public coordinates, relative reads
`read(offset,column)`, addition and multiplication. Negation abbreviates
multiplication by `-1`. Relative offsets are nonnegative; evaluation does not
wrap around the end of the trace.

A constraint pairs an expression with one scope:

| Scope | Rows to which the constraint applies |
|---|---|
| Every | All rows |
| First | Row zero |
| Last | Row `h-1` |
| Transition with lookahead `k` | Rows `i` satisfying `i+k < h` |

An applicable constraint requires its expression to evaluate to zero. Every
actual read must satisfy `i+offset < h`. An out-of-range window is a refusal,
not an implicit zero or a cyclic read. Transition declarations must cover the
expression's actual maximum offset. A positive lookahead can yield no transition
rows on a short trace; it does not erase separately declared first/last checks.
Both first and last scopes apply on a singleton trace.

### Derived facts and their use

Read coordinates are derived from syntax: a read contributes its coordinate,
addition and multiplication combine their operands' reads, and constants/public
values contribute none. Agreement at these coordinates implies equal expression
values. A compiled evaluator may fetch each required cell once and reuse it
across expressions if its input describes one immutable trace. Such a selective
reader establishes no claim about unused, unprovided cells.

The conservative degree in trace variables is zero for constants and public
values, one for reads, maximum for addition, and sum for multiplication. If each
read is represented by a polynomial of degree at most `D`, the expression's
polynomial interpretation has degree at most `degree(expression)*D`. Declared
bounds must cover derived facts; they cannot override them.

This is not a STARK quotient-degree theorem. Domain selection, row shifts,
boundary selectors, vanishing polynomials, quotient construction and authenticated
openings require additional consumer contracts. Lookups, permutations, cyclic
traces, challenge phases and preprocessed columns are outside this selected
finite view. An adapter must preserve them through another explicit view or
refuse; it cannot discard them when exporting this subset.

For example, a consumer with fixed columns must bind the table selected by its
authorized configuration and statement, then interpret finite reads over the
ordered join of witness and fixed columns. A prover-selected commitment alone
does not establish that binding. Fixedness with respect to the witness also does
not imply degree zero for the column's interpolation polynomial. This specifies
an obligation on a richer consumer; it adds no preprocessed-column syntax or
adapter to the installed finite view.

### Polynomial interpretation of finite scopes

Fix distinct domain points and a polynomial for each actual read. At every
active original row, polynomial evaluation must equal the finite read. Legal
windows remain required. For active row set `A`, write
`Z_A(X) = product_(r in A) (X - point(r))`. Over a field:

```text
constraint holds iff Z_A divides its polynomial interpretation C.
```

For multiplicative points `g^r`, the shifted polynomial `T_column(g^offset X)`
realizes a read only when interpolation and the original finite window agree.
Neither a cyclic read nor a boundary moved to a padded row is an instance of
this law. Domain size can exceed the original height when the translation
preserves these premises; padding does not enlarge the active row set.

If the read polynomials have degree at most `D`, the expression has conservative
degree `d`, and `C = Z_A Q` with `Q` nonzero, then
`|A| + degree(Q) <= d*D`. When `d*D < |A|`, exact divisibility requires `C = 0`;
natural-number subtraction cannot turn this into a nonzero constant quotient.
An empty active set imposes no constraint. The complement vanishing polynomial
`S` permits an equivalent common-divisor form `Z_A*S divides C*S` because it is
nonzero. Its degree must be included before subtracting the common divisor's
degree.

These equivalences are **per constraint**. Divisibility of a fixed weighted sum
does not imply all its summands satisfy their constraints. Random batching is
a separate protocol reduction whose challenge order and error bound must be
established. Quotient chunking also needs an explicit degree bound; an
expression-degree-only rule such as `d-1` chunks is insufficient for general
scopes.

[`Zkc.Relation.AIR.Polynomial`](../../../formal/Zkc/Relation/AIR/Polynomial.lean)
mechanizes the per-constraint divisibility, shift and degree laws. These laws do
not assert interpolation implementation correctness, FRI proximity, BCS
soundness or hiding.

## Binding and implementation scope

A verifier fixes its intended relation, field and ordered statement independently
of the prover. A normalized relation digest identifies an encoding under its
stated version; it is neither a semantic equivalence proof nor evidence that an
external frontend preserved constraints. Source provenance, mathematical subject
identity and physical representation identity serve different purposes.

Relation structure may be specialized into local program code or retained as
immutable public matrix inputs. In the latter case the actual matrix values,
shape and statement must participate in the protocol's public binding. A
coefficient-independent program is a reusable consumer, not authentication of
whatever relation file a prover supplies.

The mathematical correspondence is recorded in
[the domain map](../correspondence/domains.md#relation-domain-foundation).
Native ingestion, staging and trust boundaries are described in the
[compiler guide](../../compiler/relation-ingress.md). Neither changes PIR's
execution model or supplies a general imported-protocol security theorem.
