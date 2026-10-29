# Native layout execution

`CaptureOptions.format = "zkc-layout"` selects the development frontend for
captured source files. The compiler CLI exposes the same selection through
`--source-format=zkc-layout`. This format selection participates in the capture
identity. Installation sources retain their installed syntax. The default
project/Rust SDK frontend remains `zkc` until production migration; this is a
migration entry, not a permanent compatibility language.

The [layout parser](layout-syntax.md) feeds the existing native name, type,
role, resource, effect and specialization checkers. It does not translate text
into the older grammar. The same translation and independent actual-IR reader
then check the emitted original. A supported protocol can execute without a
specification or Lean process.

## Supported executable profile

The development entry supports:

- Protocol-owned static parameters, explicit role rosters, typed data ports,
  named or unnamed results, explicit `Random<F>` services, and installed field
  and group domains.
- Mathematical `def`, ordered `local def`, and Host `entry def`; named/static
  arguments, ordinary structural inference, and mathematical final expressions.
- File and nested modules, ordinary imports, explicitly typed interface members
  and their native conformance, type aliases, associated types, records, enums,
  patterns, and native resource attributes.
- Static natural, permission and capability requirements. Explicit section
  parameters expand before each declaration's own parameters, outermost first,
  including unused parameters. An enclosing module/interface supplies its
  parameters to members once. A section creates no namespace or visibility.
  Section headers cannot carry `roles`, `effects` or `where` clauses. Native
  effect contracts apply to callables, not modules, interfaces or data types.
- Prefix/infix/postfix, delimiter and indexing declarations at module scope,
  with explicit import selectors such as `use ops::{operator ⊕}`. Headers and
  imports fix the syntax environment before body parsing; type resolution does
  not select a parse.
- Pure bindings and mutable updates, ordered calls, reached guards,
  single-recipient sends, local branches/matches/loops, and bounded protocol
  repetition with explicit roles and a maximum.

The maintained [Schnorr source](../../../compiler/test/fixtures/layout/schnorr.zkc)
exercises the real compiler and Rust Host through
[execution tests](../../../common/tests/protocol/test_language_layout.py).
It selects two random services and three deliveries. A valid witness returns
true and a different witness returns false. Adding an unused draw consumes
service capacity; adding a guard makes an invalid witness a reached refusal.
These execution checks establish no security theorem.

## Binding and ownership rules

`=` and `:=` accept pure expressions. `<-` requires one outer ordered helper,
protocol, Host operation, or service action. Nested ordered calls, an ordered
service alias, and `<-` applied to a pure value refuse. A service alias denotes
the same service. Pure operands are evaluated in authored order. The actual
resolved callable kind determines this check, not its spelling.

An omitted send source is selected from the current payload's availability
before checking the receiver or receiving binding. A shared payload therefore
requires `from Role`, even if excluding the receiver would leave one candidate.
Future statements cannot resolve the sender. The source value remains at the
sender and the receiving value has its own identity. A reached false `guard`
refuses at its selected role; a spec premise cannot replace that operation.

Same-scope bindings cannot shadow an input or previous local. Nested lexical
scopes retain distinct bindings. Existing native permission, constructor,
ingress and codec rules still apply: a new spelling does not grant external
construction authority for an affine or opaque associated value.

Native match arms use bare alternative names, checked against the scrutinee's
resolved variant. Qualified arm patterns currently refuse; their qualifiers
cannot be discarded. A `site` attribute must select a checked protocol action.
Explicit returns and implicit result expressions cannot carry such a label.

## Optional specifications

Collect declarations before resolving spec subjects. An anonymous, unqualified,
unspecialized reference to a protocol in the same module or interface is its
owner spec. There is at most one owner spec per resolved declaration. It adds
no executable signature. Sections reuse that protocol's existing telescope.
Named specs and other anonymous references are request-only audits; they cannot
add provider premises, targets, reductions or postconditions. Named audits have
separate visibility and names. Explicit clause, request and goal-alias labels
are checked in their respective namespaces.

The native check retains the full authored syntax of specs, relations, ghost
definitions, laws and `use lean` imports. Formal expressions, audit static
arguments, exported Lean dependencies and laws are **not elaborated** by this
native projection. They cannot supply native runtime types, values or proof
facts. Execution does not start a Lean worker to resolve them.

`CheckedProject::pendingSpecifications()` exposes source occurrences and their
resolved protocol declaration, distinguishing owner specs from audits. This is
attachment information, not a typed proposition. `language-check` reports
`assurance.status` as `not-requested` when no layout spec exists, otherwise
`unavailable`, with the pending specifications. Native `status: checked` refers
to native checking. Requesting `--source-claims` with a retained layout spec
refuses with `source.assurance-unavailable`; it cannot return an empty claim
export that hides the request. Typed catalogues, generated obligations,
companions and canonical Lean admission remain a separate integration boundary.

## Written source and comparison

Headers freeze before section expansion and attachment. Bodies freeze after
notation resolution and before semantic inference. The existing
[written-source format](source-ast.md) retains section grouping, null omitted
senders, null unnamed output binders, pure/ordered evaluation, and formal syntax.
Inferred owners and signatures belong to checked/association data.

The independent interface comparison rereads captured layout headers to check
the pending-spec occurrence inventory. It continues to read and compare actual
emitted native operations. Formal requests do not become executable relation
clauses merely because their source was retained. The source AST and row
associations remain proposals; the general elaboration theorem is still open.
Parsing work is charged to the aggregate native invocation, including both
header and body passes. Exhaustion cannot create a checked partial program.

## Remaining native projection work

The parser also recognizes forms outside this executable profile. They refuse
at their semantic boundary, including shortened interface implementation
binders, ghost runtime ports, schemes, oracle execution, multiple-recipient
sends, scoped lambdas/reductions, and local notation declarations. Sections
currently group declarations; imports and notation belong to their enclosing
module. A standalone bodyless protocol is rejected.

The existing mathematical IR has no ordered regions. Total mathematical
branches/loops and participant-owned protocol branches therefore still need
their selected lowering; they are not reclassified as local computation.
Local structured control and bounded protocol repetition use the existing
checked operations. Completing these projections, formal integration, and
migrating current source consumers are prerequisites for production cutover.
