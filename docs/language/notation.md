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
compiler reads the file. zkc provides syntax-preserving formatting and authoring
queries without an input-method dependency. Named functions are useful when a
symbol is inconvenient to type.

Logical module names and Entry selectors use the same exact spelling. Quote a
Unicode module key in a project manifest, for example `"αλγεβρα" = "algebra.zkc"`
under `[modules]`; paths still name explicit files and imports never discover them.

## Declare and import notation

4.1 uses one `notation` declaration head. Every declaration spells its operand
holes and forwards each ordinary hole once in written order:

```zkc
pub def first<T: Type>(a: T, b: T) -> T:
    a
pub notation infixl(70) a ⊙ b = first(a,b)
pub notation ⟪ a, b ⟫ = first(a,b)
pub notation xs[i] = first(xs,i)
```

Targets use ordinary declaration lookup, static arguments and invocation checks.
Generic and associated module targets work as in named calls. A wrapper function
may rearrange already evaluated parameters; a notation template cannot discard,
duplicate or reorder its holes. Public notation requires a public target.
Notation asserts no algebraic law or optimizer permission.

`infixl`, `infixr` and `infix` select left, right and nonassociative infix.
`prefix(80) √ x = identity(x)` and `postfix(80) x ⊙ = identity(x)` follow the same
`notation` head. Custom precedence ranges from 1 through 99; larger numbers bind
more tightly. Fixed `*` is 70, `+` is 65 and `==` is nonassociative at 50.
Equal-precedence chains need compatible association or explicit parentheses.
The fixed `^` syntax needs an ordinary callable binding. The current catalog
does not supply an exponentiation target; source declarations may bind a callable
with the fixed right-associative precedence 72.

```zkc
use ops::{⊙, ⟪ ⟫, [], ∑}
```

Each bare selector must identify one exported descriptor. If a module exports
both prefix and infix `⊙`, select `use ops::{notation infix ⊙}`. For several index
arities, `use ops::{notation index(2)}` selects a receiver and one index.
Import order, types and body modes cannot choose syntax. `pub use` reexports the
selected descriptors and original callable identities. A module alias activates
all its public notation; a name-only import or qualified call does not.

## Reduce finite domains

A reduction declaration fixes one ordinary scoped finite consumer:

```zkc
pub notation ∑ x ∈ D, body = sum(D, fn(x) => body)
pub notation ∑ x ∈ D with p, body = sum_where(D, fn(x) => p, fn(x) => body)
```

Either form can be declared alone. These templates accept exactly the domain
and unary callbacks shown; they do not execute arbitrary expansion code or
capture ambient bindings. The selected consumer owns finite repetition,
callback modes, origin conditions and stopping behavior. View target admission
belongs to the enclosing computation package.

```zkc
value = ∑ x ∈ rows with enabled(x), term(x)
independent = ∑ (x ∈ rows) (y ∈ columns), x * y
dependent = ∑ i ∈ rows, (∑ j ∈ columns(i), term(i,j))
```

Occurrence binders admit names, ignored items and tuple patterns. `in` is an
ASCII alternative to `∈` at occurrences. Independent groups construct eager
ordered products. Domains evaluate once before callback capture snapshots;
false predicates skip their bodies. The consumer determines empty results.
Callbacks follow the ordinary [scoped rules](../spec/language/definitions.md#scoped-computations).

The body binds more tightly than addition: `∑ x ∈ rows, x + c` adds `c` after
the reduction. Write `(x + c)` to include it for every item. Multiple visible
targets for the same reduction form require explicit import selection or a
named call; mode and effects never resolve that ambiguity.

## Index collections

`notation values[position] = at(values,position)` binds suffix access at power
100. Receiver and indices evaluate once from left to right. Multiple index
counts have separate descriptor keys. Layout indexing requires a total target;
collection bounds must be established at the call site. An unavailable bound
does not select a stopping accessor or an oracle query.

Fixed source arrays retain literal projections such as `pair[0]`, without
importing notation. Indexed record fields require a named intermediate value
before dot projection. Standard library brace-format sources retain their
existing parser and declarations until the parent library migration; the
retired `operator`, `indexing` and `reduction` heads are not layout aliases.

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
