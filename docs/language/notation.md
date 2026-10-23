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
formal polynomial `+`/`*`, and formal quotient-ring `+`/`-`/`*`. These keep their existing operand kinds and
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
Static arguments and explicit module members work as for named calls.

Module bindings apply throughout the module. Inside a body, place bindings
before statements; the complete declaration prefix is visible, including later
explicit descriptors. A local binding replaces that descriptor's inherited
callable family. A type mismatch does not fall back to an outer binding.
Return types and effects cannot choose between targets accepting the same fixed
input types; use a named call or an explicit local binding to resolve ambiguity.

## Reduce finite domains

```zkc
use zkc::vector as vec;
use zkc::finite_domain::{zip};
use zkc::finite::{product};
fn weighted<F: Field>(xs: vec::Vector<F>, ys: vec::Vector<F>, α: F) -> F {
  return ∑ (x, y) ∈ zip(xs, ys), (x * y + α);
}
fn shifted_product<F: Field>(xs: vec::Vector<F>, α: F) -> F {
  return product(xs, fn(x) => x + α);
}
```

The vector module reexports `finite`'s paired `∑` and `∏` bindings. Named calls
use the same checking and lowering. Selective imports can request
`reduction ∑` and `reduction ∏`. Other collections, records, tuple items and
nested finite domains use the same scoped callback path, including directly in
protocols. `in` is an ASCII alternative to `∈`.

`fn(x) => expression` supplies an anonymous computation to a scoped parameter.
Use `fn(x, y) => ...` for two inputs and `fn((x, y)) => ...` to destructure one
tuple input. A block body uses `fn(x) => { statements; result }`. These literals
use the same keyword as named `fn` declarations and infer their types from the
receiving signature. They can capture surrounding values under the
[scoped computation rules](../spec/language/definitions.md#scoped-computations).

```zkc
let selected = ∑ x ∈ xs with enabled, checked_term(x);
let independent = ∑ (x ∈ xs) (y ∈ ys), x * y;
let dependent = ∑ i ∈ rows, (∑ j ∈ columns(i), term(i, j));
```

Independent groups form a Cartesian product. `zip` checks equal extents and
never truncates, even for ignored rows. False predicates skip their bodies.
Domains evaluate once before capture snapshots; empty library sums return zero
and products return one. Bodies can use checked Local computations and immutable
aggregate captures. Use a binding from `finite_math` for a total mathematical
function, with the required formation and access conditions.

The body binds more tightly than addition: `∑ x ∈ xs, x + c` adds `c` to the
completed sum. Write `(x + c)` or `{ x + c }` to add it for every item. A local
`reduction ∑ = my_sum, my_filtered_sum;` chooses one pair explicitly. Importing
both Local and Math families requires a local choice or selective imports;
the compiler does not infer that choice from the body's effects.

An arbitrary vector reducer uses `vec::reduce(rows, fn(x) => term(x),
fn(terms) => custom(terms))`. It receives the collected vector once, including
empty input, and keeps its own failure behavior. See the
[source contract](../spec/language/definitions.md#finite-reduction-binders) for
selection, bounds and retained checks.

## Index collections

```zkc
use zkc::vector::{Vector, indices, indexing []};
use zkc::finite_math::{sum};
math fn energy<F: Field>(xs: Vector<F>) -> F {
  return sum(indices(xs), fn(i) => xs[i] * xs[i]);
}
fn checked_pick<F: Field>(xs: Vector<F>, i: index) -> F {
  indexing values[position] = zkc::vector::get(values, position);
  return xs[i];
}
```

The vector library declares `pub indexing values[position] = at(values, position);`.
The total accessor uses bounds established by `indices(xs)` above. Matrices expose
`matrix[row, column]`; matrix coordinates establish both bounds. Sequence, group,
index and field-array collections expose the same one-index form through their
own modules. Named `at` calls retain exactly the same conditions.

The Local example explicitly selects checked `get`. An unavailable bound does
not change which accessor the compiler selects. A binding in a body declaration prefix replaces the
inherited indexing family of the same arity, so keep each intended collection
binding in that prefix when several are needed. Access follows the named target's
ownership and effect rules. Fixed source arrays still use literal projections
such as `pair[0]`, without importing indexing. For indexed record fields, write
`let record = rows[i];` before using `record.field`.

## Inspect notation and locations

The source inspection view `zkc inspect --view=notations` describes
descriptors, bindings, scopes and occurrences. `--notation-private` includes
captured private/local records; `--notation-installation` independently includes
installation records. The C++ surface is `inspectNotations` with
`NotationInspectionOptions.includePrivate` and `includeInstallation`, both false
by default. Both CLI visibility switches require `--view=notations`. The default inventory includes public captured declarations.
Use `--json` for the structured command report, whose `checked.notations` member contains
this inventory.

The `zkc.notations/0` view is diagnostic data, bounded to 8 MiB. Canonical named-call
renderings explain selected targets and operand order; they are not a promise
that rewriting source preserves capture or artifact bytes. Lower SDK limits are
rechecked against retained descriptor and hole maxima.

Spans are half-open UTF-8 byte intervals into the original source buffer, and
rendered diagnostic columns are one-based byte columns. A client displaying
UTF-16 positions or grapheme columns must convert from those original bytes;
counting one column per byte misplaces multibyte names. Excerpts may escape
non-ASCII bytes, so displayed carets need not equal source display columns.
