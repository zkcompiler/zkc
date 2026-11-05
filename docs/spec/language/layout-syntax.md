# Layout source syntax

This contract defines the native layout syntax API in `zkc/Source` and
`zkc/Syntax`. It is the syntax foundation for the selected frontend revision.
The existing production compiler entry remains in place until its consumers
migrate. Parsing this surface alone grants neither executable admission nor a
formal judgment. [Status](../../status.md#source-and-application-boundary)
records which consumers are connected.

## Source and layout

`source::Revision` owns an immutable source buffer and document version. Its
path is a diagnostic label; the source/syntax libraries never open files or
start processes. Spans use UTF-8 byte offsets. Position conversion supports
UTF-8 and UTF-16 columns, rejects split scalars/surrogates and nonexistent lines,
and clamps overlong columns to the physical line end. CRLF maps to one line
boundary. Edits create a new revision, require an increasing version, validate
replacement UTF-8 and enforce the caller's byte ceiling.

The [Unicode identifier profile](lexical.md) remains authoritative. Identifiers
require their authored NFC spelling. Decimal tokens retain ASCII spelling;
the checker owns numerical range admission. Line comments start with `//`.
Strings retain the unescaped ASCII policy, with literal tabs admitted as content
by the layout contract. Backslash escapes and block comments are not admitted.

LF and CRLF are accepted. Four spaces introduce one suite level; dedentation
must reach a prior level. Tabs outside comments and strings refuse. Empty and
comment-only lines do not affect suites. Parentheses, brackets, braces, paired
Unicode delimiters and tight static lists suppress logical newlines. Each
physical byte belongs to exactly one real token, including erroneous input.
Logical line ends, indentation and dedentation have zero width.

A static application is tight: `f<F>(x)`, `Vec<Vec<F, 2>, 3>`. Comparisons use
spaces, as in `a < b`. `section <F: Field>:` has an explicit declaration rule.
These choices do not depend on names or types. Comparisons cannot chain.
A nonempty spaced section continuation starts at a line head with a typed
binder (`name:`); an ordinary value named `section` still uses spaced comparisons.

## Declarations and bodies

An optional initial `module path` declares the file module; nested modules use suites. `module M: I:`
selects an interface explicitly. `section <...>:` supplies static parameters
without introducing a namespace. Protocols own their roles, parameters and
results; an optional `spec for P:` attaches a contract. A named
`pub spec Audit for P:` contains requests and cannot redefine that contract.
`scheme S = P<...>:` selects a construction and its associated requests.
Section headers accept only static parameters; `roles`, `effects` and `where`
are rejected rather than inherited or discarded.

```zkc
module example

pub protocol Deliver<F: Field> roles(P, V)(x: F@P) -> F@V:
    delivered <- send x to V
    return delivered

spec for Deliver:
    ensures out == x
```

The syntax tree also retains definitions, relations, interfaces, structs, enums,
type/domain declarations, oracle definitions, notation declarations, attributes
and laws. It does not assert that all these forms have an executable or formal
projection. `use lean Project.Module as formal` retains an import request;
parsing never evaluates Lean text.

Pure bindings use `=`, ordered actions use `<-`, and updates use `:=`.
`@(P = left, V = right)` is an explicit role-assembly expression.
It is syntactically distinct from a suffix role annotation such as
`call(args) @(P, V)`. Assembly entries are named component selections, not
an argument list to a user-resolved function. Formation and the absence of an
implicit equality claim are specified in [layout execution](layout-execution.md).
`fn(pattern, ...) => expression` retains a scoped literal with one parameter
list and one lexical expression body. Its mode comes from its expected signature.
`fn(A) -> B` and `local fn(A) -> B effects(...)` are signature forms, with optional
named inputs and callback-local `where item_from(input, domain)` clauses.
`local fn(...) => ...` is not an alternative literal spelling. A vertical-bar
expression remains a delimiter form, not a callback alias.

Declaration `where` clauses project the existing native requirements, including
`in_bounds(index_input, collection_input[, axis])` and
`equal_extent(left_input, right_input[, left_axis, right_axis])`.
Selectors are input names followed by dotted record fields or decimal tuple
indices, such as `pair.0.values`. Axes are decimal literals zero or one and
default to zero. Arguments are positional; labels, bindings, computed selectors
and partial axis lists are invalid. Collection types, valid axes, duplicate
conditions, fixed extents and interface inclusion follow the
[native data-condition contract](definitions.md), without additional inference.
These are mathematical declaration premises, distinct from callback-local
`item_from`, static natural inequalities, `Copy`/`Drop`, installed capabilities
and installed type consumer requirements such as `NativeMessage(T)`.

The layout grammar accepts one `where` expression: `where ()` is empty,
`where equal_extent(xs, ys)` is a single premise, and
`where (equal_extent(xs, ys), in_bounds(i, xs))` is a list. Parentheses around
a single premise and a trailing comma in a parenthesized list are accepted.
An unparenthesized comma list is invalid. Written-source export retains data
requirements as `requirement` nodes with `input_selector` children and their
written paths and axes; checked signatures and replay use the existing logical
input positions.

`mut` marks a mutable binding. Structured bodies include `for`, `if`, `match`
and `return`. `if` and `match` may also produce values in expression positions;
value-producing `if` requires an `else`. Exhaustiveness, typing, effects,
mutability and role/resource joins belong to checking.

`guard condition` is a runtime action, with an optional explicit `@Role`.
`guard(condition)` at a statement head has the same priority. A lone `guard`,
qualified `Helpers::guard(x)`, projection `guard.field`, or a call inside a
binding remains an ordinary expression. `send value from P to V` always has
written recipients; sender omission is retained for checking. Random services
remain explicit inputs and calls, such as `coins.draw()`.

A specification retains `requires`, `ensures`, `target` and
`reduces R(...) to S(...)` separately, with optional clause labels. A target
may retain an explicit acceptance expression: `target statement: R(x) accept accepted`.
No acceptance expression is inferred from an output position. `security:` groups
request expressions in an indented suite, or introduces one inline expression.
Requests may have ordinary labels (`knowledge: library::knowledge(...)`) or omit
them. The group itself is not a request label or a security property. Clause heads
have priority in that suite. A request-only suite cannot redefine the subject's
contract. Within formal expressions, `site path` retains an authored event
selector, including dotted paths; `site(value)` remains an ordinary call. Neither
parsing a selector nor grouping requests establishes a proof. No request name
becomes a reserved security property. Retired `impl`, `require`,
`deployment`, `proof`, `pub spec protocol` and receiver-less `send` spellings
are not aliases.

## Syntax environments and recovery

`parseHeaders` retains declaration signatures and opaque bodies. `parseBodies`
parses the same source revision under supplied notation descriptors, optionally
scoped by declaration byte offset. Both return immutable snapshots. A descriptor
contains only token shape, syntactic position, precedence, association and arity;
name resolution and callable types never select a parse. Imported notation must
be resolved by the caller before body parsing. The exact environment remains
available with every node.

Notation preserves the [bounded families](notation.md): prefix, infix, postfix,
paired delimiters, indexing and reductions. ASCII descriptors have their fixed
syntax. Conflicting descriptors, conflicting positions and mixed association
at equal precedence refuse even when the conflicting descriptor is unused.
Callable meaning and required laws remain checker/library concerns.

A snapshot contains ordered tokens, node/child arenas, typed views, diagnostics
and one of `Complete`, `Partial`, `Cancelled` or `ResourceExhausted`. Missing
nodes have zero-width source spans; recovery never invents an authored action.
Synchronization uses logical line ends, matching suite boundaries and outer
declaration heads. An unclosed delimiter can be abandoned before an independent
outer declaration. No partial result can serve as a checked project.

Invocation budgets can lower, but cannot raise, the implementation ceilings:
1 MiB source, 1,000,000 tokens/nodes/child entries, 4,096 bytes per code token,
128 identifier bytes, depth 64, 8,000,000 work units, 100 diagnostics and 1,024
missing-node insertions. Each effective limit is the minimum of its requested
value and its implementation ceiling. A larger enclosing allowance does not
itself exhaust parsing; callers debit the actual reported parser work.
Notation environments admit at most 4,096 descriptors
with at most 64 holes. Both recursive descent and constructed node height are
bounded. Cancellation is shared by the request and its computation. A stopped
parse retains the remaining bytes in an invalid token, an end token and a
fixed error leaf even when the caller supplies zero storage budget.

## Formatting

The formatter uses the snapshot's exact notation environments. It normalizes
LF, trailing whitespace, signature separators, bindings, binary operators,
projections and calls. Legal suite/continuation indentation, comments, string
contents, token order and authored parentheses are preserved. It reparses under
the same environments and checks structural equivalence before returning an
edit. Formatting is idempotent. Incomplete syntax is retained with
`syntax.format.partial`; failed equivalence retains the original source with
`syntax.format.equivalence`. A cancelled or exhausted operation returns no edit.

Formatting changes exact source bytes. Consumers must recompute captured source
identities rather than reuse evidence tied to the previous revision.

## Contextual words and delimiter decisions

Layout parsing uses word tokens with priority in the following contexts; a word
is not a globally registered security property or installed operation merely
because it occurs in this table.

| Context | Structural words |
| --- | --- |
| Declaration suite | `pub`, `use`, `section`, `module`, `interface`, `local`, `def`, `protocol`, `spec`, `relation`, `ghost`, `oracle`, `law`, `type`, `domain`, `struct`, `enum`, `notation`, `scheme`, `entry` |
| Header continuation | `roles`, `where`, `effects`, `for`, `as`, `lean` where the owning production admits them |
| Statement head | `return`, `for`, `if`, `else`, `match`, `mut`; `guard` has the explicit exceptions described above |
| Ordered action | `send`, `from`, `to`, `query`, `at` |
| Contract suite | `requires`, `ensures`, `target`, `accept`, `reduces`, `to`, `security`; other request labels remain ordinary names |
| Formal expression | `site` before an identifier path; callable `site(...)` remains ordinary |
| Expression/binder | `true`, `false`, `if`, `else`, `match`, `and`, `or`, `not`, `ghost` in an actual argument; parameter-purpose words in parameter lists |

This is contextual parsing: naming a declaration with a word does not suppress
that word's structural role at a statement or expression head. Use a qualified
reference when the bare spelling would select a structural production. Captured
module paths also obey the shared reserved-path validation in
[the source name contract](lexical.md). Retained brace syntax has its own reserved
words and is not silently reparsed as layout syntax.

The core `|...|` form uses a fixed syntactic decision, independent of resolved
types. `|name, ...| body` starts a lambda. `|name| body` starts a lambda only when
the following token is a word, number, `(` or `[`. Otherwise it is paired
delimiter notation. Parenthesize a lambda body beginning with a prefix operator,
for example `|x| (-x)`. A delimiter expression followed by a binary operator,
`|x| + y`, remains a delimiter application and an addition. Parsing the delimiter
does not install a cardinality meaning; its callable meaning still requires a
visible binding. Empty lambdas are outside this profile.

`(x)` is grouping and `(x,)` is a one-element tuple. The accepted tuple separator
`;` also preserves tuple intent. The authored model retains this distinction,
including in formal clauses. Formatting preserves these separators. All notation
declarations write their operand holes and exact target call. Imports require
a unique descriptor or an explicit position/index-arity selector.
