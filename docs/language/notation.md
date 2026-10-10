# Write mathematical notation

Names and notation are separate choices. Unicode names follow the
[source text contract](../spec/language/lexical.md); operators and delimiters
are ordinary callable bindings under the
[notation contract](../spec/language/notation.md). Named APIs remain available.
[Status](../status.md#source-and-application-boundary) records implementation
coverage.

## Names and editor input

Names such as `α`, `β₂` and `結果` use the pinned Unicode 17 identifier profile.
`β₂` is one name; it is distinct from `beta_2` and does not mean indexing or
squaring. Every name must already be NFC. The compiler preserves the supplied
UTF-8 bytes and rejects a non-NFC spelling rather than correcting it. Source
strings and decimal literals retain ASCII syntax; comments may contain UTF-8.

Enter symbols with an editor's Unicode input or paste their literal characters.
For example, `α` is U+03B1, `⊙` is U+2299, and `⟪`/`⟫` are U+27EA/U+27EB.
Backslash abbreviations, if an editor provides them, must expand before the
compiler reads the file. zkc provides no input-method dependency, formatter or
LSP server. Named functions are useful when a symbol is inconvenient to type.

Logical module names and Entry selectors use the same exact spelling. Quote a
Unicode module key in a project manifest, for example `"αλγεβρα" = "algebra.zkc"`
under `[modules]`; paths still name explicit files and imports never discover them.

## Import notation and keep named calls

```zkc
use zkc::vector as vec;
fn weighted<F: Field>(a: vec::Vector<F>, b: vec::Vector<F>,
                     weights: vec::Vector<F>, α: F) -> F {
  let blended = a * (1 - α) + b * α;
  return ⟪weights, blended⟫;
}
```

The module alias imports public notation. Vector `+` calls `vec::add`, vector
`*` calls `vec::scale` with a scalar on the right, `a ⊙ b` calls
`vec::hadamard(a, b)`, and `⟪a, b⟫` calls `vec::dot(a, b)`. Hadamard
multiplication keeps the native `vector.mul` operation and its length checks.
Vector `*` does not silently become a dot or Hadamard product.

To use names without activating notation, import selected names:
`use zkc::vector::{Vector, dot};`. To select notation as well, write
`use zkc::vector::{Vector, operator ⊙, notation ⟪};`. `pub use` reexports
the selected bindings with their original identities. A qualified function
reference alone does not activate operators.

The same rules cover matrix `*` applied to a vector, group `point * scalar`
and formal polynomial `+`/`*`. These keep their existing operand kinds and
body modes. A symbol does not make an ordered vector operation valid in
total `math fn` code.

## Declare a callable spelling

The vector library exposes these declarations:

```zkc
pub fn hadamard<F: Field>(left: Vector<F>, right: Vector<F>) -> Vector<F>
    = primitive("vector.mul");
pub operator infixl(70) ⊙ = hadamard;
pub notation ⟪ left, right ⟫ = dot(left, right);
```

`infixl`, `infixr` and `infix` select left, right and nonassociative infix.
`prefix` and `postfix` take one operand. Custom powers range from 1 to 99;
larger numbers bind more tightly. Fixed `*` is 70, `+` and `-` are 65,
`==` is nonassociative at 50, `!` is 75, `&&` is 20 and `||` is 10.
Parentheses make grouping explicit. Equal-power chains cannot mix associations
or include a nonassociative operator without grouping.

An existing unambiguous descriptor permits the short form
`operator ⊙ = another_hadamard;`. Prefix and infix may share a symbol, which
then requires an explicit fixity when binding it. Postfix and infix cannot
share a symbol. Custom operators are single admitted mathematical scalars;
arbitrary words and strings are not operators. `∑` and `∏` use the separate
reduction declarations below.

Delimiter declarations name holes, not variables to substitute into arbitrary
code. `dot(left, right)` must use each hole once in that order. A wrapper function
can rearrange already evaluated values. Every notation operand evaluates once
in written order, preserving the target's effects, stops and resource rules.
Targets need the matching number of data parameters and a written result type.
Static arguments and explicit component members work as for named calls.

Module bindings apply throughout the module. Inside a body, place bindings
before statements; the complete declaration prefix is visible, including later
explicit descriptors. A local binding replaces that descriptor's inherited
callable family. A type mismatch does not fall back to an outer binding.
Return types and effects cannot choose between targets accepting the same fixed
input types; use a named call or an explicit local binding to resolve ambiguity.

## Reduce finite vectors

```zkc
use zkc::vector as vec;
fn weighted<F: Field>(xs: vec::Vector<F>, ys: vec::Vector<F>, α: F) -> F {
  return ∑ [(x, y) in zip(xs, ys)] { x * y + α };
}
fn shifted_product<F: Field>(xs: vec::Vector<F>, α: F) -> F {
  return reduce vec::product [x in xs] { x + α };
}
```

The vector library declares `pub reduction ∑ = sum;` and
`pub reduction ∏ = product;`. Named `reduce vec::sum [...] { ... }` and
`reduce vec::product [...] { ... }` remain available without symbol imports.
For selective imports, write
`use zkc::vector::{Vector, reduction ∑, reduction ∏};`. A body declaration
prefix can select a different reducer with `reduction ∑ = my_sum;`; it follows
ordinary callable resolution and local replacement rules.

Collections evaluate once in written order; captures such as `α` are then read
once in first textual-use order. Row names exist only inside the scalar body
and may shadow outer names. Explicit `zip` is strict: every vector must have
the same length, including a row written `_` or unused by the body. Matched
empty rows give zero for library sum and one for library product.

This profile accepts field vectors and pure field-ring scalar bodies in local
functions, with immutable whole-scalar captures of the same field. Nested
binders, arbitrary collections, mutable or aggregate captures, and effectful
scalar bodies are unsupported. A custom defined local reducer can stop and
retains its ordinary behavior. See the [finite reduction contract](../spec/language/definitions.md#finite-vector-reductions)
for the precise body and helper limits.

## Inspect notation and locations

The source inspection view is `zkc check --notations`, separate from
`--declarations` and package `zkc inspect`. Its public inventory describes
descriptors, bindings, scopes and occurrences. `--notation-private` includes
captured private/local records; `--notation-installation` independently includes
installation records. The C++ surface is `inspectNotations` with
`NotationInspectionOptions.includePrivate` and `includeInstallation`, both false
by default. Both CLI visibility switches require `--notations`. The default inventory includes public captured declarations.

The `zkc.notations/0` view is diagnostic data, bounded to 8 MiB. Canonical named-call
renderings explain selected targets and operand order; they are not a promise
that rewriting source preserves capture or artifact bytes. Lower SDK limits are
rechecked against retained descriptor and hole maxima.

Spans are half-open UTF-8 byte intervals into the original source buffer, and
rendered diagnostic columns are one-based byte columns. A client displaying
UTF-16 positions or grapheme columns must convert from those original bytes;
counting one column per byte misplaces multibyte names. Excerpts may escape
non-ASCII bytes, so displayed carets need not equal source display columns.
