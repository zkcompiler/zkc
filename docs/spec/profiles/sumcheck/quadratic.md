# Quadratic coefficients and table compilation

This profile represents polynomials with per-coordinate degree at most two.
It compiles the selected ordered [table expressions](../../domains/polynomials.md#table-expressions)
and supplies the coefficient object used by the complete verifier.

## Quadratic coefficient objects

For a value type `F` and ordered dimension `n : Nat`, define:

```text
Quadratic F 0     = constant(c : F)
Quadratic F (n+1) = node(a,b,c : Quadratic F n).
```

For a semiring `F`, evaluation at `x : Fin n → F` is:

```text
eval(constant c, x) = c
eval(node(a,b,c), x) =
  (eval(a,tail x) + x(0)*eval(b,tail x))
    + (x(0)*x(0))*eval(c,tail x),
```

where `tail x(i)=x(i+1)`. The representation has per-coordinate degree at
most two. Its squared coefficients can be nonzero. It is a logical ordered
coefficient object, without a prescribed native storage layout.

Addition and left scaling act recursively on corresponding children:

```text
add(constant a, constant b) = constant(a+b)
add(node(a,b,c), node(d,e,f)) = node(add(a,d),add(b,e),add(c,f))
scale(r,constant a) = constant(r*a)
scale(r,node(a,b,c)) = node(scale(r,a),scale(r,b),scale(r,c)).
```

For a commutative semiring, these operations preserve pointwise addition and
scaling. Define first-coordinate restriction and Boolean summation by:

```text
restrict(node(a,b,c),r) = add(add(a,scale(r,b)),scale(r*r,c))
booleanSum(p) = cubeSum(n, x ↦ eval(p,x)).
```

The [Boolean sum](../../domains/polynomials.md#boolean-summation) counts ordered
Boolean assignments, with one empty assignment at dimension zero. Restriction
satisfies `eval(restrict(p,r),t)=eval(p,cons(r,t))` for `p : Quadratic F (n+1)`.
For that same dimension:

```text
booleanSum(p) = booleanSum(restrict(p,0)) + booleanSum(restrict(p,1))
booleanSum(restrict(node(a,b,c),r)) =
  (booleanSum(a) + r*booleanSum(b)) + (r*r)*booleanSum(c).
```

Repeated materialization and direct recomputation use the same
[ordered-prefix laws](../../domains/polynomials.md#ordered-residuals).

## Table compilation

For this conversion let `F` be a commutative ring. A table denotes its
[multilinear extension](../../domains/polynomials.md#multilinear-extension).
Write `t₀` and `t₁` for its first-coordinate low and high halves, and
`t₁-t₀` for pointwise table subtraction. Define:

```text
tableCoefficients₀(t) = constant(t(empty))
tableCoefficientsₙ₊₁(t) =
  let low  = tableCoefficientsₙ(t₀)
      high = tableCoefficientsₙ(t₁)
  in node(low, add(high,scale(-1,low)), scale(0,low))

productCoefficients₀(t,u) = constant(t(empty)*u(empty))
productCoefficientsₙ₊₁(t,u) =
  node(productCoefficientsₙ(t₀,u₀),
       add(productCoefficientsₙ(t₀,u₁-u₀),
           productCoefficientsₙ(t₁-t₀,u₀)),
       productCoefficientsₙ(t₁-t₀,u₁-u₀)).
```

The first represents one table extension; the second represents the product
of the two extensions at every point. It is not the multilinear extension of
their pointwise product table.

Let `tables : J → Table F n` bind actual tables to identifiers, and let the
source be a [list of weighted factor occurrences](../../domains/polynomials.md#table-expressions).
Write `evalExpression(tables,x,source)` for that expression evaluator and use
the common [Boolean sum](../../domains/polynomials.md#boolean-summation)
`expressionSum(tables,source)`. The partial compiler has `tables` implicit in
these defining equations:

```text
compileFactors([])    = some(tableCoefficientsₙ(1))
compileFactors([j])   = some(tableCoefficientsₙ(tables(j)))
compileFactors([j,k]) = some(productCoefficientsₙ(tables(j),tables(k)))
compileFactors(other)= none

compile([]) = some(scale(0,tableCoefficientsₙ(1)))
compile((weight,occurrences)::rest) =
  match compileFactors(occurrences), compile(rest) with
  | some term, some tail → some(add(scale(weight,term),tail))
  | otherwise           → none.
```

Here `1` is the constant-one table. Ordered occurrences are retained, including
two occurrences of the same identifier. A term with more than two occurrences
is unsupported even when its weight is zero, its factors are constant or its
denotation happens to have lower degree. This is a sufficient compiler subset,
not an exact degree detector. The source meaning permits longer lists.

If `compile(tables,source)=some p`, then, for every point `x : Fin n → F`:

```text
eval(p,x) = evalExpression(tables,x,source)
booleanSum(p) = expressionSum(tables,source).
```

Actual flat input vectors `values : J → Fin(2^n) → F` determine `tables` through
the common [indexing map](../../domains/polynomials.md#flat-table-indexing). The
first coordinate selects the low or high half. The same values and occurrence
list feed both source meaning and compilation.

*Example (informative).* Over the field of order five, the one-coordinate table
`[0,1]` denotes `x`. Two occurrences denote `x²`, whose value at `2` is `4`.
Deduplicating the occurrence or extending the pointwise square table instead
gives `2`. Boolean-point agreement would miss this error.

## Ordered coefficient encoding

The logical flattened coefficient list is:

```text
coefficients(constant c) = [c]
coefficients(node(a,b,c)) =
  coefficients(a) ++ (coefficients(b) ++ coefficients(c)).
```

Its length is `3^n`, and it is injective at fixed `F,n`. The dimension fixes
the child boundaries during reconstruction. This is an encoding of coefficient
objects, not a byte codec or a canonical representation of field functions.
Over small fields, distinct coefficients can induce the same function.
