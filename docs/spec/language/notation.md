# Mathematical notation

This native contract defines callable operators, paired-delimiter calls and
finite-vector reduction bindings.
The [lexical profile](lexical.md#mathematical-tokens) admits their tokens;
[definition checking](definitions.md#library-defined-operators) owns callable
selection and native checks. [Status](../../status.md#source-and-application-boundary)
records implementation coverage.

## Declarations and descriptors

```text
[pub] operator SYMBOL = CALLABLE;
[pub] operator FIXITY(PRECEDENCE) SYMBOL = CALLABLE;
[pub] notation OPENER HOLE ("," HOLE)* CLOSER = CALLABLE(HOLE, ...);
[pub] reduction SYMBOL = CALLABLE;
```

`FIXITY` is `infixl`, `infixr`, `infix`, `prefix` or `postfix`. The first three
mean left-associative, right-associative and nonassociative infix respectively.
Custom precedence is an ASCII integer from 1 through 99. Infix calls have two
data operands; prefix and postfix calls have one. A delimited call has one or
more comma-separated expression holes.

An operator descriptor is keyed by symbol and position: prefix, infix or
postfix. Precedence, association and arity are properties of that descriptor,
not overload selectors. A delimiter descriptor is keyed by its opener; its
closer and hole count must agree wherever that key is visible. Matching
descriptors can carry multiple callable targets. Conflicting shapes refuse
before type inference, regardless of whether any expression uses them.

The short form `operator ⊙ = hadamard;` requires exactly one visible descriptor
for `⊙`. It binds a target to that descriptor; callable arity and operand types
never choose syntax. An explicit declaration creates a descriptor or repeats
an identical visible shape. Prefix and infix may share a symbol. Postfix and
infix may not share one symbol in the same environment.

A reduction descriptor has its own position, one semantic data operand (the
mapped vector), and fixed bracket/body syntax. Its symbol is `∑` or `∏`;
it has no user-selected precedence, holes or association. A prefix and a
reduction descriptor cannot share a token. An `operator` declaration or selector
does not bind or import a reduction descriptor.

The fixed grammar is:

| Tokens | Position and association | Binding power | Library binding |
|---|---|---:|---|
| `\|\|` | Left infix | 10 | No |
| `&&` | Left infix | 20 | No |
| `==` | Nonassociative infix | 50 | Yes |
| `+`, `-` | Left infix | 65 | Yes |
| `*` | Left infix | 70 | Yes |
| `!` | Prefix | 75 | No |
| Projection and method suffixes | Suffix | 100 | Fixed syntax |

The four overloadable ASCII positions can only repeat these descriptors.
New positions require admitted non-ASCII symbols; ASCII unary minus is not
introduced. Boolean control/formula syntax cannot acquire library bindings.
Calls and grouping retain their fixed syntax. Natural expressions in type and
static arguments retain their separate arithmetic grammar.

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
pub notation ⟪ left, right ⟫ = dot(left, right);
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
reduce CALLABLE [NAME in COLLECTION] { SCALAR_BODY }
reduce CALLABLE [(NAME, NAME, ...) in zip(COLLECTION, COLLECTION, ...)] { SCALAR_BODY }
SYMBOL [NAME in COLLECTION] { SCALAR_BODY }
SYMBOL [(NAME, NAME, ...) in zip(COLLECTION, COLLECTION, ...)] { SCALAR_BODY }
```

`CALLABLE` is an ordinary static callable reference with optional static
arguments. `SYMBOL` requires a visible reduction binding. A row name may be `_`;
tuple binders require at least two rows and exactly the same number of explicit
`zip` operands. There is no implicit zip or arbitrary pattern comprehension.
The braces delimit a scalar expression block; its row names are scoped only to
that block. These forms can occur as ordinary expressions.

The library declarations are `pub reduction ∑ = sum;` and
`pub reduction ∏ = product;`. Their targets are defined static local callables
of type `Vector<F> -> F`, with one written scalar result and no service inputs.
Ordinary callable inference, lexical identity and effects remain in force;
a reduction symbol supplies neither an algebraic law nor permission to
substitute another reducer. The [source reduction contract](definitions.md#finite-vector-reductions)
defines collection evaluation, captures, body admission and helper extraction.

## Imports and lexical scope

`use zkc::vector as vec;` activates the module's public notation and imports a
module alias. `use zkc::vector::{Vector, dot};` imports only those named exports.
Selectors `operator ⊙`, `notation ⟪` and `reduction ∑` explicitly import their
respective bindings; an operator selector imports all exported operator fixities
for its token. For example:

```zkc
use zkc::vector::{Vector, operator ⊙, notation ⟪, reduction ∑};
```

These selectors require the corresponding public exports. A qualified named
call alone activates no notation. `pub use` reexports original identities and
resolved descriptors; duplicate paths to the same declaration deduplicate.
An exported short binding carries the descriptor resolved in its original
definition environment, not a descriptor chosen by its importer. Capturing a
module remains separate from importing it; imports never discover source files.

Module declarations have whole-module scope, including uses in earlier bodies.
A body or nested block first collects its entire declaration prefix, adds its
explicit descriptors, resolves short bindings and freezes the environment before
parsing statements. A short binding can therefore refer to an explicit descriptor
later in that prefix. Bindings after executable statements refuse.

A local binding replaces the inherited callable family for its descriptor key.
Nested blocks inherit that replacement; unsuitable local targets never trigger
fallback to outer targets. Prefix and infix families remain separate. Local
replacement cannot change an inherited shape or repair conflicting module
imports. Component dictionaries remain explicit.

Reduction bindings follow the same module, reexport and declaration-prefix
rules. `reduction ∑ = my_sum;` in a block replaces that descriptor's inherited
family; an unsuitable target never selects the outer library sum instead.

## Staging and retained evidence

Capture validation and lexing precede fixed declaration headers and opaque body
token ranges. The existing acyclic import/export graph determines immutable
module notation environments. Bodies then parse in those environments before
ordinary declaration and callable checks. This applies to helpers, protocols,
relations, inline relation members and component members. Invalid syntax in an
unused body still rejects the project. Both parser traversals consume work;
tokens, declarations and operations are counted once.

Checked notation retains descriptor identity, definition-site binding, scope,
authored operands and the selected ordinary call. Callable selection and the
independent [binding witness](definitions.md#library-defined-operators) use the
same descriptor arity; the witness reconstructs the lexical family independently
of the solver. Specialization preserves definition-site selection.
Reduction extraction also preserves the original body scope and its selected
notation occurrences in generated helpers. Its separate
[extraction witness](definitions.md#finite-vector-reductions) precedes native
source-to-IR comparison.

## Inspection

`inspectNotations(CheckedProject, NotationInspectionOptions, Limits)` is the
read-only Language inspection surface. `NotationInspectionOptions` has
`includePrivate` and `includeInstallation`, both false by default. The
CLI view is `zkc check --notations`; `--notation-private` includes captured
private/local records and `--notation-installation` includes installation records.
Both visibility switches require `--notations` and apply only to source checking.
See [status](../../status.md#source-and-application-boundary) for API and CLI
availability.

The `zkc.notations/0` diagnostic JSON contains descriptors, bindings, scopes and
occurrences. It retains checked-project-local identities, source origins and
original UTF-8 byte spans. Default public inventory omits private/local data;
installation data is independently opt-in. Descriptor views explain spelling,
fixity, power or delimiter shape; bindings explain targets, statics, visibility
and definition locations; occurrences explain authored operand order and checked
selection. Record identities are local to the retained checked project, not
persistent cross-build identifiers.

Canonical named-call rendering is a diagnostic aid. It is not a byte-preserving
rewrite, and named and symbolic captures need not have equal artifact identities.
Syntax metadata does not enter the native Entry interface or grant execution
authority. Retained inventories survive the temporary parser and checker without
requiring either to run again. Compiler spans and inspection support do not
constitute an LSP server or source formatter.

## Bounds

`Limits.notationDescriptors` is 4096 distinct active descriptor keys per module
or block environment, including the fixed arithmetic and Boolean descriptors.
`Limits.notationHoles` is 64 holes per delimited descriptor.
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
