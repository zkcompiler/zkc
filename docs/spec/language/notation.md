# Mathematical notation

This native contract defines callable operators, paired-delimiter calls and
general finite reduction bindings and library indexing.
The [lexical profile](lexical.md#mathematical-tokens) admits their tokens;
[definition checking](definitions.md#library-defined-operators) owns callable
selection and native checks. [Status](../../status.md#source-and-application-boundary)
records implementation coverage.

## Declarations and descriptors

```text
[pub] notation infixl(PRECEDENCE) LEFT SYMBOL RIGHT = CALLABLE(LEFT, RIGHT)
[pub] notation infixr(PRECEDENCE) LEFT SYMBOL RIGHT = CALLABLE(LEFT, RIGHT)
[pub] notation infix(PRECEDENCE) LEFT SYMBOL RIGHT = CALLABLE(LEFT, RIGHT)
[pub] notation prefix(PRECEDENCE) SYMBOL HOLE = CALLABLE(HOLE)
[pub] notation postfix(PRECEDENCE) HOLE SYMBOL = CALLABLE(HOLE)
[pub] notation OPENER HOLE ("," HOLE)* CLOSER = CALLABLE(HOLE, ...)
[pub] notation RECEIVER[INDEX ("," INDEX)*] = CALLABLE(RECEIVER, INDEX, ...)
[pub] notation SYMBOL BINDER ∈ DOMAIN, BODY = CALLABLE(DOMAIN, fn(BINDER) => BODY)
[pub] notation SYMBOL BINDER ∈ DOMAIN with PREDICATE, BODY = CALLABLE(DOMAIN, fn(BINDER) => PREDICATE, fn(BINDER) => BODY)
```

The 4.1 layout surface has one `notation` declaration head. `operator`,
`indexing` and `reduction` declaration heads are retired in this surface.
Legacy brace-format sources retain their existing parser until the enclosing
library migration; they are not aliases in the layout grammar.

`infixl`, `infixr` and `infix` mean left-associative, right-associative and
nonassociative infix. Custom precedence is an ASCII integer from 1 through 99.
ASCII syntax has fixed precedence and association even in an explicit binding.
Infix calls have two data operands; prefix and postfix calls have one.
A delimited call has one or more comma-separated expression holes.

An operator descriptor is keyed by symbol and position: prefix, infix or
postfix. Precedence, association and arity are properties of that descriptor,
not overload selectors. A delimiter descriptor is keyed by its opener; its
closer and hole count must agree wherever that key is visible. Matching
descriptors can carry multiple callable targets. Conflicting shapes refuse
before type inference, regardless of whether any expression uses them.
Prefix and infix may share a symbol. Postfix and infix may not share a symbol
in one environment. Every declaration writes its holes and exact target call;
there is no short operator declaration in 4.1.

A reduction descriptor has its own position, a domain and a scoped body, with
an optional scoped predicate. Its non-ASCII mathematical symbol has fixed body
binding power 67. ASCII operators and `∈` cannot name a reduction. Prefix and
reduction descriptors cannot share a token. An operator-position selector does
not import a reduction descriptor.

The fixed grammar is:

| Tokens | Position and association | Binding power | Library binding |
|---|---|---:|---|
| `\|\|` | Left infix | 10 | No |
| `&&` | Left infix | 20 | No |
| `==` | Nonassociative infix | 50 | Yes |
| `+`, `-` | Left infix | 65 | Yes |
| `*` | Left infix | 70 | Yes |
| `^` | Right infix | 72 | Yes |
| `!` | Prefix | 75 | No |
| Projection and method suffixes | Suffix | 100 | Fixed syntax |

The five overloadable ASCII positions can only repeat these descriptors.
New positions require admitted non-ASCII symbols; ASCII unary minus is not
introduced. Boolean control/formula syntax cannot acquire library bindings.
Calls and grouping retain their fixed syntax. Natural expressions in type and
static arguments retain their separate arithmetic grammar.

The fixed `^` descriptor has no installed exponentiation binding in the current
catalog. An ordinary source callable can bind that descriptor; syntax alone
provides no exponentiation semantics.

## Expression association

An infix operator at power `p` is consumed when `p` meets the current minimum.
Left-associative and nonassociative operators parse the right operand at minimum
`p + 1`; right-associative operators use `p`. A prefix at `p` can begin only
when the current minimum is at most `p`, then parses its operand at `p`.
A weaker prefix in a stronger operand position requires parentheses.

A postfix at `p` is consumed when it meets the current minimum and continues
the suffix loop. Projection and method suffixes use power 100 in that same
loop, including after postfix notation. Repeated postfix tokens apply in source
order. Parenthesized expressions restart at minimum zero and create an
association boundary.

Different symbols may share a power and have different associations in one
environment. An unparenthesized equal-power infix chain is admitted only when
all its operators have the same left or right association. A nonassociative
operator or mixed association in that chain requires parentheses. This checks
both child roots at the same power and does not cross explicit grouping or
an intervening different-power root. Imports of unrelated descriptors at the
same power are not themselves a conflict. Parsing never uses types, effects,
backtracking or declaration order to choose a grammar.

## Delimiter calls and targets

```zkc
pub notation ⟪ left, right ⟫ = dot(left, right)
```

Each hole name is distinct. The right-hand side is exactly one callable
application, using every hole exactly once in textual order. Repeated, omitted,
reordered or extra holes and arbitrary right-hand expressions refuse. The
signature supplies hole types through ordinary inference; holes do not need
separate type annotations or concrete types at declaration time. Each use
supplies exactly the declared number of expressions and the matching closer.

Targets are ordinary mathematical or local callables with the descriptor's
number of data inputs and one written result type. Protocols and implicit
services are not targets. Static arguments use ordinary callable syntax,
including named arguments and inference holes. Target references resolve in the
binding's definition scope. A public binding requires a public target, even
when its descriptor was introduced privately. Unused bindings are checked.

Operands evaluate once in authored order, then their values enter the target.
A wrapper function may rearrange already evaluated parameters or perform more
computation; a notation declaration cannot substitute, duplicate or reorder
expressions. The call retains ordinary stop behavior, resource moves,
participant ownership and mode/effect checks. A local vector operation remains
invalid in a `math fn`, even when written with mathematical symbols. Declaring
a symbol asserts no algebraic law and adds no optimizer or proof rule.

## Finite reduction syntax

```text
SYMBOL PATTERN in DOMAIN [with PREDICATE], BODY
SYMBOL PATTERN ∈ DOMAIN [with PREDICATE], BODY
SYMBOL (PATTERN ∈ DOMAIN) (PATTERN ∈ DOMAIN) ... [with PREDICATE], BODY
```

`in` and `∈` are equivalent membership spellings. Patterns use ordinary names,
`_` and tuples. One domain may itself yield a tuple; independent parenthesized
groups construct ordered Cartesian products. Explicit `zip` provides strict
pairwise traversal. Dependent domains use nested binders. The body is parsed at
binding power 67: `∑ x ∈ xs, x * x + c` means `(∑ x ∈ xs, x * x) + c`.
Parentheses or an expression block include an addition in the body. A binder can
begin an operand expression, including the right operand of multiplication.

```zkc
pub notation ∑ x ∈ D, body = sum(D, fn(x) => body)
pub notation ∑ x ∈ D with p, body = sum_where(D, fn(x) => p, fn(x) => body)
pub notation ∏ x ∈ D, body = product(D, fn(x) => body)
```

Each occurrence requires one canonical visible binding for its filtered or
unfiltered form before inferring the body or result. The unfiltered target has
a domain input followed by one unary scoped callback. A filtered target takes
the domain, a Boolean predicate callback and the body callback in that order.
The binder and all ordinary holes have distinct names. The right-hand side must
use the same binder in each callback and forward the domain, predicate and body
holes exactly once in written order. Ambient captures and arbitrary expansions
in a declaration template refuse. Either reduction form can be declared alone;
neither declaration creates the other target.

Targets are ordinary Math or Local finite consumers with one written result and
no data or service inputs. Their callback item types, mode/effect ceilings and
origin maps must pass the existing finite-consumer contract. Mode and effects
never choose between multiple visible targets for one form. Each target keeps
its own independently checked conditions and module identity. A View target
requires the parent computation package's View admission; notation does not
grant that permission.

The legacy brace parser retains its paired `reduction` bindings and their
cross-signature checks until library migration. Existing installed source
closures are not rewritten by the layout notation change.

Expansion creates an ordinary call with unary `fn(...) => ...` callbacks and structural
domain products. Product construction never looks up a generated textual
`product` name. Predicate and body callbacks retain distinct immutable expression
identities, including their lexical parameter definitions, even though both
parameter patterns refer to the same written binder spans. The
[source binder contract](definitions.md#finite-reduction-binders)
defines evaluation, captures and retained checks. Named calls remain available
without notation imports; the old `reduce callable [...] {...}` syntax is removed.

## Imports and lexical scope

`use ops as selected` activates the module's public notation and imports a
module alias. `use ops::{Vector, dot}` imports only those named declarations.
Bare selectors `{⊙, ⟪ ⟫, [], ∑}` select unique exported descriptors, including all
callable targets with that exact shape. The delimiter selector includes its
closer. A glyph exported at both prefix and infix positions, or `[]` exported
at several arities, refuses with `source.notation-ambiguous` even if unused.

Explicit selectors `notation prefix ⊙`, `notation infix ⊙`,
`notation postfix ⊙`, and `notation index(2)` select an existing descriptor key.
The index arity counts the receiver. These are import selectors, not declaration
heads. A named export mechanism is unnecessary in this bounded profile: distinct
positions/arities have explicit keys, and different shapes at one key already
conflict in the exporting module. Import order, callable types, modes and effects
never resolve descriptor ambiguity.

```zkc
use ops::{Vector, ⊙, ⟪ ⟫, [], ∑}
```

Missing exports refuse with `source.import`. A qualified named call alone
activates no notation. `pub use` reexports original identities and resolved
descriptors; duplicate paths to the same declaration deduplicate. Capturing a
module remains separate from importing it; imports never discover source files.

Module declarations have whole-module scope, including uses in earlier bodies.
Children inherit their parent's notation. Syntax environments are ordered by
lexical containment and the original sites of imported notation; name-only
imports add no notation dependency. A parent importing a child's notation while
that child inherits the parent environment forms a cycle and refuses.
Legacy brace bodies collect their declaration prefix and freeze its environment
before parsing statements. Layout body-local declarations remain outside this
projection; the module syntax environment is fixed before body parsing.

A local binding replaces the inherited callable family for its descriptor key.
Nested blocks inherit that replacement; unsuitable local targets never trigger
fallback to outer targets. Prefix and infix families remain separate. Local
replacement cannot change an inherited shape or repair conflicting module
imports. Module dictionaries remain explicit.

Reduction bindings follow the same module, reexport and declaration-prefix
rules. A legacy body-local reduction declaration replaces its descriptor's inherited
family; an unsuitable target never selects the outer library sum instead.

## Indexing

`notation values[position] = at(values, position)` binds `values[position]`
to an ordinary callable. Multiple indices, as in `matrix[row, column]`, are
separate operands. Receiver and indices evaluate once from left to right;
the declaration must forward every hole once in that order. The descriptor has
fixed suffix binding power 100, and its key includes operand count. Different
index counts can coexist. Ordinary operand types choose among targets of the
same count; result types, effects and bounds cannot resolve an overlap.

`use ops::{[]}` requires one exported indexing arity;
`use ops::{notation index(2)}` selects the receiver-plus-one-index shape. Module aliases
and `pub use` follow the ordinary notation rules. Legacy body-local indexing declarations
replace the inherited family for the matching arity. Standard collection modules
bind their total `at` accessors, whose conditions must be established in a total
context. Legacy Local bindings can select a checked `get` accessor; 4.1 notation
requires a total target for indexing, with any bounds established at its call site.
Selecting `at` never falls back to `get` when bounds are unavailable.

Fixed source arrays `[T; N]` retain numeric literal projection without an import.
A library binding does not replace that projection. Generic array lengths require
the existing static bound. Dynamic source-array indices, symbolic static indices
and assignment through indexing are not supported. Library `field_array` is a
separate native container and uses the ordinary library indexing path.

A subscript retains its original syntax through checking. The receiver's known
type constructor distinguishes fixed array projection from library access;
unresolved library receiver constructors need a type annotation or named call.
Without a visible indexing family, existing deferred static projection inference
is preserved. Dynamic access captures the receiver container and evaluates the
index inside a callback; static array access captures the projected element.
Inspection records emitted library accesses as indexing occurrences and omits
static projections. Dot projection still requires a named place: bind an indexed
record to a local name before projecting its fields.

## Staging and retained evidence

Capture validation and lexing precede fixed declaration headers and opaque body
token ranges. The existing acyclic import/export graph determines immutable
module notation environments. Bodies then parse in those environments before
ordinary declaration and callable checks. This applies to helpers, protocols,
relations, inline relation members and module members. Invalid syntax in an
unused body still rejects the project. Both parser traversals consume work;
tokens, declarations and operations are counted once.

Checked notation retains descriptor identity, definition-site binding, scope,
authored operands and the selected ordinary call. Callable selection and the
independent [binding witness](definitions.md#library-defined-operators) use the
same descriptor arity; the witness reconstructs the lexical family independently
of the solver. Specialization preserves definition-site selection.
Finite binder callbacks retain their authored scopes through the common scoped
extraction and specialization witnesses. Domain recipes and selected binding
families are independently compared with the retained source records before
native source-to-IR comparison. This does not independently verify parsing.

## Inspection

Spans use a `source` index into the checked source inventory. Logical module
scopes have a declaration owner and an optional parent; lexical body scopes also
have a `body` index. Binding and call `receiver` fields identify a statically
bound module, separately from the source location's `module` name.


`inspectNotations(CheckedProject, NotationInspectionOptions, Limits)` is the
read-only Language inspection surface. `NotationInspectionOptions` has
`includePrivate` and `includeInstallation`, both false by default. The
CLI view is `zkc inspect --view=notations`; `--notation-private` includes captured
private/local records and `--notation-installation` includes installation records.
Both visibility switches require `--view=notations` and apply only to source inspection.
The command report exposes the inventory under `checked.notations`.
See [status](../../status.md#source-and-application-boundary) for API and CLI
availability.

The `zkc.notations/0` diagnostic JSON contains descriptors, bindings, scopes and
occurrences. It retains checked-project-local identities, source origins and
original UTF-8 byte spans. Default public inventory omits private/local data,
including descriptors confined to private module scopes;
installation data is independently opt-in. Descriptor views explain spelling,
fixity, power or delimiter shape; bindings explain targets, statics, visibility
and definition locations. A filtered-only declaration carries
`filtered_only: true`; occurrences explain authored operand order and checked
selection. Record identities are local to the retained checked project, not
persistent cross-build identifiers.

Canonical named-call rendering is a diagnostic aid. It is not a byte-preserving
rewrite, and named and symbolic captures need not have equal artifact identities.
Binder renderings show `fn(...) => ...` callbacks and use `×` to display structural products;
that diagnostic product spelling is not an implicit source name lookup.
Syntax metadata does not enter the native Entry interface or grant execution
authority. Retained inventories survive the temporary parser and checker without
requiring either to run again. The independent [authoring surface](authoring.md) provides checked-syntax
formatting in the retained notation environment. Formatting preserves notation
declarations and occurrences instead of replacing them with canonical calls.

## Bounds

`Limits.notationDescriptors` is 4096 distinct active descriptor keys per module
or block environment, including the fixed arithmetic and Boolean descriptors.
`Limits.notationHoles` is 64 holes per delimited or indexing descriptor.
`Limits.notationInspectionBytes` is 8 MiB for inspection output. Callers may
lower these ceilings; the CLI uses defaults.

Repeated declaration sites count toward the existing declaration ceiling;
reexports deduplicate original sites. Environment insertions, comparisons,
deduplication, graph edges and traversals consume work. Cardinality and hole
bounds are checked before allocation. Parser recursion and constructed expression
height are bounded separately, including a flat left-associative chain.

Checked storage retains maximum environment cardinality and hole count. Requests
with lower limits recheck that retained evidence before reuse, including closure
and inspection. Serialization enforces its byte ceiling while producing output;
an exceeded limit refuses without a partial document. Rust Entry readers receive
no notation environments and therefore no syntax-budget transport.
