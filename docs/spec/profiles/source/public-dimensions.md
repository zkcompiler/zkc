# Public dimension expressions

This profile forms and evaluates natural-number dimensions from an ordered
public scope. Domain interpretation and actual shape correspondence use the
common [value laws](../../domains/values.md).

## Public dimensions

A public dimension environment is `ρ : Fin k → Nat`, using the
[finite index type](../../conventions.md#mathematical-notation) and containing
already available public values.
The selected dimension-expression profile is indexed by that scope:

```text
Dim k = lit(value : Nat)
      | param(position : Fin k)
      | add(left : Dim k, right : Dim k)
      | mul(left : Dim k, right : Dim k)
```

Evaluation is defined by:

```text
evalDim ρ (lit v)   = v
evalDim ρ (param i) = ρ i
evalDim ρ (add a b) = evalDim ρ a + evalDim ρ b
evalDim ρ (mul a b) = evalDim ρ a * evalDim ρ b
```

Arithmetic here is natural-number arithmetic. A finite machine's capacity or
overflow behavior is supplied by its admission/realization contract. `Dim k`
contains no hidden-value or future-value constructor. Supplying `ρ` also requires
the public provenance of its actual entries; the type alone does not establish
that provenance.

## Dimension formation

The raw dimension syntax has the same literal, addition and multiplication
forms, and references `pub(i)`, `hidden(i)` and `future(i)` for natural `i`.
Its scoping function `scope k : RawDim → Option (Dim k)` is:

```text
scope k (lit v)    = some (lit v)
scope k (pub i)    = if i < k then some (param i) else none
scope k (hidden i) = none
scope k (future i) = none
scope k (add a b)  = combine add (scope k a) (scope k b)
scope k (mul a b)  = combine mul (scope k a) (scope k b)
```

The checked `i < k` justifies the `Fin k` argument to `param`.
`combine f (some x) (some y) = some (f x y)`; `combine` returns `none` if either
argument is `none`. Formation therefore requires both operands to be in scope,
including in a product with literal zero.

For raw public values `xs : List Nat`, `publicEnv xs k` returns `none` unless
`length xs = k`. On success it returns `some ρ`, where `ρ i` is the actual
entry at position `i` in `xs`. The equality of lengths ensures that every such
lookup is in range. There is no missing-value default in a successfully formed
environment.

Successful construction satisfies the following law, where `xs[i]?` denotes
optional lookup at position `i`:

```text
publicEnv xs k = some ρ ⇒
  length xs = k ∧ ∀ i : Fin k, xs[i]? = some (ρ i).
```

*Example.* `mul(lit 0,hidden 0)` fails formation. Its arithmetic result would
be zero for any supplied hidden value, but that does not make the raw reference
part of this public dimension language.

## Dimension substitution

For `σ : Fin k → Dim l`, substitution replaces public parameters while retaining
the expression structure:

```text
substDim σ (lit v)   = lit v
substDim σ (param i) = σ i
substDim σ (add a b) = add (substDim σ a) (substDim σ b)
substDim σ (mul a b) = mul (substDim σ a) (substDim σ b)
```

For every `e : Dim k` and `ρ : Fin l → Nat`:

```text
evalDim ρ (substDim σ e) = evalDim (fun i => evalDim ρ (σ i)) e.
```

This is substitution of already scoped public expressions. It supplies no
permission to specialize on an unavailable challenge or private invocation input.
