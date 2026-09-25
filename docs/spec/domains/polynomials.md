# Tables and polynomials

A table first denotes its multilinear extension. A table expression then forms
sums of products of those extensions. Table order, factor multiplicity and
coordinate order are operands of this meaning, independently of a storage plan
or a proving protocol.

## Univariate coefficient objects

A univariate polynomial over `F` has a finite ascending coefficient sequence:
`p(X) = sum_i c[i] * X^i`. Its normalized sequence omits trailing zero
coefficients; the zero polynomial has an empty sequence. Construction may
normalize coefficients, while canonical wire ingress rejects a non-normalized
encoding. This canonicalization concerns coefficient objects, not equality of
the functions they induce on a finite field.

The predicate `degreeAtMost(p,d)` accepts zero and otherwise requires the highest
nonzero coefficient index to be at most `d`. An implementation's allocation limit
does not establish this protocol-specific degree bound. When the permitted
message domain includes arbitrary univariate polynomials, a sumcheck verifier
checks its bound before drawing the next challenge. The existing
[quadratic coefficient type](../profiles/sumcheck/quadratic.md#quadratic-coefficient-objects)
is a stronger admitted domain with three coefficients and bound two; it need
not acquire an unchecked arbitrary-degree message interpretation.

Evaluation and Boolean boundary have meanings `p(r)` and `p(0)+p(1)` respectively.
Neither depends on a prover's intended construction of the coefficients.

## Two-adic cosets and folding

`TwoAdicField(F)` supplies a declared compatible family of two-power roots,
in addition to `Field(F)`. A particular installation states its maximum order
and root convention. This capability does not follow merely from being a field.
The current KoalaBear and octic-extension installations admit power-of-two
sizes through `2^24`, with smaller execution limits. Their size-`n` root is
`1791270792^(2^24/n)` in the base field, embedded explicitly for the extension.
Extension challenges and coset shifts may be outside the base field; domain
points stay in their selected nominal field.

The logical order of a size-`n` coset with nonzero shift `s` is
`x_i = s * g_n^i`, for `0 ≤ i < n`. `poly.domain_root<F>(n)`,
`domain_point<F>(s,n,i)` and `domain_points<F>(s,n)` use this order. Invalid sizes,
a zero shift or an out-of-range coordinate refuse. Internal DFT layouts never
change this order.

`poly.coset_evaluate<F>(p,s,n)` requires at most `n` coefficients and returns
`[p(x_i)]`. `coset_interpolate<F>(v,s)` returns the unique normalized interpolant
of degree below `length(v)` on that coset. Interpolation is not a low-degree test.
`poly.coefficient_count<F>` counts the normalized coefficients; the zero
polynomial has count zero. It requires only the polynomial coefficient domain.

`poly.even_odd_fold` additionally requires `CharacteristicNotTwo(F)`: its
division by two is not a generic field law. For an even-sized coset,
`poly.even_odd_fold<F>(v,s,beta)` pairs positions `i` and
`i+n/2`, returning
`(v_i+v_(i+n/2))/2 + beta*(v_i-v_(i+n/2))/(2*x_i)`.
Its next domain has shift `s^2` and size `n/2`. This operation is defined on any
admitted vector. The polynomial identity
`p(X)=p_even(X^2)+X*p_odd(X^2)` and the degree bound for
`p_even + beta*p_odd` are proved in `Zkc.Polynomial.EvenOdd`;
cryptographic FRI proximity soundness is a separate obligation.

`poly.divide_opening<F>(p,z,y)` checks `p(z)=y` and returns normalized coefficients
of `(p(X)-y)/(X-z)`, including zero/constant cases. It works over the coefficient
ring and requires no two-adic domain. `poly.opening_quotient<F>(v,s,z,y)` instead
returns pointwise `(v_i-y)/(x_i-z)`, refusing `z` on the coset; it does not assert
that `v` has low degree or that `y` is a valid evaluation. The distinction matters
when a verifier consumes hostile messages.

An opening-quotient combination for source degree below `n` should have degree
at most `n-2`. FRI terminal capacity below `n` leaves one degree of slack if it
tests that combination directly. Multiplication by `X` alone is also insufficient:
on a nonzero sampling domain, it accepts an extra reciprocal-word direction.
The authored AIR example tests `(1 + rho*X) D(X)`, with fresh rho after D's
underlying commitments and claims are fixed and before the first FRI root.

`Zkc.Polynomial.DegreeAdjustment` proves an arbitrary-word common-agreement law:
if two distinct corrections agree with polynomials of degree below n on a set
of more than n points, the word has a zero or degree-at-most-n-2 representative
there. It also proves honest correction completeness and uniqueness of an
exceptional exact-membership challenge. These are algebraic facts. Obtaining
common agreement from FRI acceptance, unbatching multiple opening claims and
applying Fiat–Shamir remain separate security obligations.

### Compiler-visible domain facts

An ordered coset identity consists of its nominal field, size, shift and
installed compatible root/order convention. Equality of ordered domains requires
equality of these mathematical parameters; a storage layout is not a parameter.
Different shifts can order the same underlying point set differently, so
ordered-domain inequality does not assert disjoint sets. Distinct nominal
fields remain distinct even when an explicit embedding exists.

An analysis may retain exact expressions for size and shift without knowing
their runtime values. Actual SSA identity (including aliases), canonical
constants and installed operation equations can establish congruence. A vector
result of coset evaluation or domain-points formation has the requested size;
interpolation uses its input vector's length. The even/odd result has size
`n/2`, shift `s²` and the compatible smaller root. These facts are conditional
on the relevant operations succeeding. They do not discharge nonzero-shift,
size, coordinate, coefficient-count or resource checks, or prove that success
is reachable.

May-dependency and authored names do not establish runtime equality. Each
reception is a distinct value boundary; neither its sender's value nor a domain
association is inherited. Reusing the same received value preserves its local
identity, while comparing separate receptions requires additional evidence.
Different unknown origins establish neither equality nor inequality. Missing
domain transfers or root conventions must remain unknown. Interpreting a word
on another domain is allowed, and coefficient polynomials are reusable across
domains; an analysis must not reject these algorithms merely for incompatibility.

The native `domain-inspect SOURCE ENTRY [--compare=LEFT,RIGHT]` command admits
source and uses the bounded execution occurrence view. Its report includes
exact-expression terms, parameter origins, installed conventions, congruence
classes, producer-to-consumer compatibility and explicit unknown/different
reasons. IDs are local to that report. The installed analysis uses optional
operation facets in `Protocol/Contracts`; unsupported operations, including
multilinear folds, acquire no coset fact. Immediate may-dependency edges are
reported separately from exact terms, with sender provenance marked separately
at receptions.

These are conditional mathematical domain associations, including for arbitrary
words. They supply no low-degree, proximity, authentication, acceptance or
security judgment. They can inform future sharing and lowering, but confer no
CSE, hoisting, allocation, failure-order or accounting permission. Native
extraction and backend correspondence are tested boundaries, not formally
verified by this analysis. No runtime domain carrier is required.

## Points and Boolean tables

For a type `X`, an indexed vector of length `n` is a function `Fin n → X`, using
the [finite index type](../conventions.md#mathematical-notation).
The unique vector of length zero is written `empty`. For `x : Fin n → X`,
`cons(a,x)` has length `n+1`, first element `a`, and element `x i` at position
`i+1`. Conversely, `tail x i = x(i+1)` removes the first coordinate.

A Boolean table with values in `F` and dimension `n` has type:

```text
Table F n = (Fin n → Bool) → F
```

This table type and its flat indexing require no algebraic structure on `F`.
Subsequent extension and expression definitions take `F` to be a commutative
ring. A point then has type `Fin n → F`.

## Flat-table indexing

The selected flat-table representation is `v : Fin (2^n) → F`. Define:

```text
index(0,b) = 0
index(n+1,b) = (if b[0] then 2^n else 0) + index(n,tail b)
```

The result has type `Fin (2^n)` at dimension `n`; the displayed arithmetic
denotes its bounded natural value. The first coordinate selects the low or
high half of the vector.

For `i : Fin (2^n)`, its inverse `vertex(n,i) : Fin n → Bool` is:

```text
vertex(0,i) = empty
vertex(n+1,i) =
  if i < 2^n then cons(false,vertex(n,i))
  else cons(true,vertex(n,i-2^n))
```

Each recursive index is in `Fin (2^n)` by the tested inequality and the input
bound. The inverse laws are:

```text
index(n,vertex(n,i)) = i
vertex(n,index(n,b)) = b
```

The meaning of a flat vector is `ofVector v b = v(index(n,b))`. In particular:

```text
ofVector v (vertex(n,i)) = v i.
```

At dimension zero there is one input cell. A raw adapter establishes exactly
`2^n` cells and their actual identifier binding. Padding, transposition,
truncation or a zero-default lookup is not implicit. Other indexing conventions,
including Merkle path directions, require their own correspondence.

*Example.* A flat vector `[a,b,c,d]` denotes `a` at `(false,false)`, `b` at
`(false,true)`, `c` at `(true,false)`, and `d` at `(true,true)`. Swapping the
coordinates exchanges the middle two cells.

## Multilinear extension

Let `F` be a commutative ring. For `T : Table F n` and `x : Fin n → F`, define:

```text
extension(0,T,x) = T(empty)
extension(n+1,T,x) =
  (1-x[0]) * extension(n,fun b => T(cons(false,b)),tail x)
  + x[0] * extension(n,fun b => T(cons(true,b)),tail x)
```

For a Boolean vector `b`, define `booleanPoint b i = if b i then 1 else 0`,
using zero and one of the same ring. The extension recovers the table:

```text
extension(n,T,booleanPoint b) = T b.
```

Consequently, for actual flat input `v` and position `i`:

```text
extension(n,ofVector v,booleanPoint(vertex(n,i))) = v i.
```

These equations do not require a finite field. A root-count bound, field-size
argument or injective sample embedding supplies its stronger assumptions at
the statement that uses them.

## Table expressions

For a table identifier type `J`, fix an actual environment
`tables : J → Table F n`. A term and an expression are:

```text
Term F J       = F × List J
Expression F J = List (Term F J)
```

The second component of a term is its ordered list of factor occurrences.
For `x : Fin n → F`, define:

```text
factors tables x [] = 1
factors tables x (j :: rest) =
  extension(n,tables j,x) * factors tables x rest

eval tables x [] = 0
eval tables x ((c,occurrences) :: rest) =
  c * factors tables x occurrences + eval tables x rest
```

The empty sum is zero; the empty product is one. Repeated identifiers contribute
repeated factors, including repeated scales if scales are moved into a term's
coefficient. All finite occurrence lists have meaning. The
[degree-two compiler](../profiles/sumcheck/quadratic.md#quadratic-coefficient-objects)
is a separate selected subset.

For raw table inputs, the adapter resolves every used identifier and preserves
each occurrence. A total mathematical environment does not authorize treating
an unresolved identifier as an all-zero table.

## Boolean summation

For `f : (Fin n → F) → F`, define:

```text
cubeSum(0,f) = f(empty)
cubeSum(n+1,f) =
  cubeSum(n,fun x => f(cons(0,x)))
  + cubeSum(n,fun x => f(cons(1,x)))

expressionSum tables e = cubeSum(n,fun x => eval tables x e)
```

This enumerates Boolean assignments in coordinate order, retaining their
multiplicity. At dimension zero the sum has one summand. In particular, an empty
product contributes its coefficient at every Boolean assignment; an empty
expression contributes zero.

## Equality away from Boolean points

An algebraic replacement used at arbitrary points establishes equality at every
point in its claimed domain. Agreement on the Boolean cube alone does not
justify replacing a product of extensions by the extension of a pointwise
product table.

*Example.* Over the field with five elements, the one-coordinate table `[0,1]`
has extension `x`. Two occurrences denote `x²`, which is `4` at `x=2`.
The pointwise product table is again `[0,1]`; its extension is `2` at that point.
Deleting the repeated occurrence also gives `2`. Both changes preserve all
Boolean evaluations while changing the polynomial used by a later challenge.

Equality of evaluations is also distinct from equality of a coefficient object.
Different coefficient objects can induce the same function over a small field.
A coefficient encoding or degree claim identifies its representation explicitly.
Algebraic value equality alone does not permit changing state or deleting
observable work; that requires the applicable
[transformation judgment](../verification/refinement.md#preservation-subjects).

## Ordered residuals

For a fixed prefix `r : Fin m → F` and remaining point `x : Fin n → F`, define
`join(m,r,x) : Fin (n+m) → F` by:

```text
join(0,r,x) = x
join(m+1,r,x) = cons(r[0],join(m,tail r,x))
```

The first `m` coordinates come from `r`; the remaining `n` come from `x`.
For an object `p` with declared evaluator `evalP p : (Fin (n+m) → F) → F`, its
residual meaning after that prefix is:

```text
residual(p,r)(x) = evalP p (join(m,r,x)).
```

A materializer returning an object `q` with evaluator
`evalQ q : (Fin n → F) → F` is correct when:

```text
∀ x : Fin n → F, evalQ q x = residual(p,r)(x).
```

This is a correspondence obligation for the chosen representation, not an
assumption that every representation has a materializer. A stored residual and
a recomputing plan identify the same original object, ordered axes, fixed prefix
and actual prefix values. The quadratic coefficient profile provides one
construction; the common obligation does not prescribe that dense storage.

## Coordinate-list admission

An indexed point can be represented by the list of its entries in increasing
index order, written `toList x`. An admitted list for a point of dimension `n`
has length exactly `n` and denotes those entries at the corresponding indices.

The mathematical helper `coordinates n values` is total and uses zero for a
missing entry. Its exact correspondence laws are:

```text
coordinates n (toList x) = x
length values = n ⇒ toList(coordinates n values) = values

length fixed = m ∧ length tail = n ⇒
  join(m,coordinates m fixed,coordinates n tail) =
    coordinates (n+m) (fixed ++ tail)
```

The length premises are required when using this helper to represent actual
source inputs. A source guard establishes the claimed arity and availability;
the helper's totality neither admits a missing coordinate nor permits dropping
an extra coordinate.

## Contractions

Let `A` be a finite index type, `B` a suffix type, `w : A → F` and
`T : A → Bool → B → F`. Define a contracted table and its next fold by:

```text
contraction w T bit b = Σ a : A, w a * T a bit b
fold r H b = (1-r) * H false b + r * H true b
recomputeFold r w T b =
  Σ a : A, (w a * (1-r)) * T a false b + (w a * r) * T a true b
```

For every `r : F` and `b : B`, the checkpoint law is:

```text
fold r (contraction w T) b = recomputeFold r w T b.
```

Replacing each factor by an equal contracted or recomputed value preserves
sums of products under the same coefficients and occurrence lists. More
explicitly, for finite `B,U`, coefficients `c : U → F`, occurrences
`occ : U → List J` and values `L,R : J → B → F`, the premise
`∀ j b, L j b = R j b` gives:

```text
Σ b : B, Σ u : U, c u * product(map (fun j => L j b) (occ u)) =
Σ b : B, Σ u : U, c u * product(map (fun j => R j b) (occ u)).
```

`product [] = 1` and `product (a :: xs) = a * product xs`; repeated occurrences
are retained. These are algebraic laws and supply no native allocation, wire,
probability or protocol-security claim.

## Applied and pending challenges

A delivered challenge and an applied prefix are distinct state. If `H` represents
the already applied prefix and `r` is the next delivered challenge, the completed
residual applies the fold at `r` before export. At the last coordinate its value
is `H false () + r * (H true () - H false ())`, for `H : Bool → Unit → F`.
Exporting `H false ()` instead omits that challenge's effect.

The [module contract](../profiles/compiler/factor-preparation.md#outcome-specific-summaries) governs
availability, overwrite and invalidation. An identifier or cache hit alone does
not establish the residual equation or prove that a pending challenge was applied.

## Ordered domains beyond multilinear tables

A new interpolation domain identifies its ordered nodes, axis order and the
hypotheses under which interpolation exists and evaluation agrees. Equal field
and cell count do not identify that domain. Storage permutation preserves logical
coordinates only under its reindexing law; exchanging logical axes changes the
polynomial in general. Mixed domains therefore add a selected interpretation
and conversion laws rather than changing existing MLE operations implicitly.
