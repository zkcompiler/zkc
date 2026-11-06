# Native layout execution

`CaptureOptions.format = "zkc-layout"` selects the development frontend for
captured source files. The compiler CLI exposes the same selection through
`--source-format=zkc-layout`. This format selection participates in the capture
identity. Installation sources retain their installed syntax. A project selects
it with `source-format = "zkc-layout"` in every manifest of its closure, and
explicit SDK and CLI module maps name it the same way; this is a migration
entry, not a permanent compatibility language.

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
- Scoped Math/Local callback signatures and `fn(pattern, ...) => expression`
  arguments, retaining lexical captures, forwarding, effect ceilings and
  whole-item origin requirements.
- Canonical home-module methods on nominal receivers, including generic aliases;
  see [method binding](definitions.md#arguments-and-inference). The existing
  direct logical-family profile admits protocol methods only when the receiver
  uniquely determines every declared role.
- Oracle custody ports, ordered query and delivery, dynamic shape bounds,
  holder and shape views, and bounded oracle sequences; see the
  [oracle source profile](oracles.md) for exact coverage.
- File and nested modules, ordinary imports, explicitly typed interface members
  and their native conformance, type aliases, associated types, records, enums,
  patterns, and native resource attributes.
- Static natural, permission and capability requirements. Explicit section
  parameters expand before each declaration's own parameters, outermost first,
  including unused parameters. An enclosing module/interface supplies its
  parameters to members once. A section creates no namespace or visibility.
  Section headers cannot carry `roles`, `effects` or `where` clauses. Native
  effect contracts apply to callables, not modules, interfaces or data types.
- Unified `notation` declarations for prefix/infix/postfix, delimiters, indexing
  and finite reductions at module scope, with imports such as `use ops::{⊕}`.
  Headers and imports fix the syntax environment before body parsing; type
  resolution does not select a parse.
- Pure bindings and mutable updates, ordered calls, reached guards,
  single-recipient sends, selected Math/Protocol branches and matches, Local
  control, and bounded Protocol repetition with checked participants and a
  bounded maximum.

The maintained [Schnorr source](../../../compiler/test/fixtures/layout/schnorr.zkc)
exercises the real compiler and Rust Host through
[execution tests](../../../common/tests/protocol/test_language_layout.py).
It selects two random services and three deliveries. A valid witness returns
true and a different witness returns false. Adding an unused draw consumes
service capacity; adding a guard makes an invalid witness a reached refusal.
These execution checks establish no security theorem.

## Structural View and finite consumers

`view def` selects one structural mode. A resolved installed descriptor result
selects its typed family implementation; an ordinary forwarding result remains
ordinary data. The family follows the resolved alias, not the token `Finite`.
The following standalone 4.1 source uses the same installed association and
finite implementation as the maintained legacy library:

```zkc
domain F = field("koala-bear")
type Vector<E: Field> = builtin("vector", E)
type Finite<I: Type + Copy + Drop> = builtin("finite", I)
view def elements<E: Field>(xs: Vector<E>) -> Finite<E> = domain("elements")
view def forwarded<I: Type + Copy + Drop>(rows: Finite<I>) -> Finite<I>:
    return rows
def fold<I: Type + Copy + Drop, S: Type + Copy + Drop>(
    rows: Finite<I>, initial: S,
    step: fn(S, item: I) -> S where item_from(item, rows)
) -> S = finite("math.fold")
pub protocol Total roles(P)(xs: Vector<F> @P, initial: F @P) -> F @P:
    return fold(forwarded(elements(xs)), initial, fn(state, item) => state + item)
```

Native definition associations accept exact installed constructor/consumer
identities and validate the complete signature. An absent or incompatible
association refuses. `domain(...)` requires a resolved Finite result; View mode
alone does not authorize a constructor. Descriptor result modifiers, including
custody with no receivers, refuse before category normalization. Definitions
without an applicable native association require an authored body.

Ordinary View results use mathematical native inputs/results. Local bodies
and Local callbacks invoke them through `exec.compute`, retaining their View
declaration mode. Independent admission replays ordinary bodies and exact
returns from authored syntax, whether or not a result annotation is present.
It obtains replay obligations from the authored headers even when the candidate
has no remaining View declarations.

Abstract ordinary View members supply the same inherent empty effect contract
as defined ordinary Views. Generic owner/member dispatch works from Math and
Local bodies and from their scoped computations. Ordinary View calls also
compose directly with `and` and `or` in Protocol formulas, in either operand
position. The View result must be ordinary data; descriptor-producing calls,
Local calls with empty effects and Local callback literals remain ineligible
there.

A scoped input uses `fn(A) -> B` for Math or
`local fn(A) -> B effects(...)` for Local. `fn(parameter, ...) => expression`
is a scoped literal checked once in its receiving mode. `fn((x, y))` binds one
tuple item, while `fn(x, y)` binds two parameters. Named callback inputs may
retain the existing `where item_from(item, rows)` obligation. Finite formation
retains callbacks without executing them. Ordinary stored functions and implicit
mode retries are not introduced.

The retained source graph uses complete descriptor contracts at parameters and
nodes, with one checked declaration result contract. Each child edge retains an
independent expected contract, checked against its selected node after static
substitution. Closure, inference, interface conformance and authored replay
compare the family, arity and every typed parameter. Graph identity includes
node and edge contracts; its cached key is never replay authority. The selected
result node supplies the closed result contract without a duplicate family or
item field. Ordinary runtime operands remain distinct from these static indices.
Finite conversion extracts an item only after checking Finite and arity one.
The native finite Domain representation and its enumeration/admission semantics
are unchanged. Checked contracts also distinguish
[structural descriptor products and sequences](definitions.md#structural-descriptor-contracts),
including optional natural extents. Their source aggregates, installed schemes,
ordered formation and Finite projection follow the
[structural formation contract](descriptor-formation.md). Static natural
constructor configuration, callable payloads and new native descriptor families
still require their own installed formation and consumer rules.

Finite closure retains the entire selected factory recipe, including unused
constructors and shared dependencies, in dependency order. Each reached consumer
admits that graph afresh; zero result cardinality does not suppress invalid
constructors. Exact operand origin, transitive lexical availability and callback
whole-item obligations remain checked. Independent replay compares the retained
recipe with its authored View source before closure and native comparison.

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

Native match arms use bare alternatives or qualified constructors. A qualifier
must resolve to the scrutinee's nominal variant; a different enum with the same
alternative spelling refuses. Imported module aliases use ordinary resolution.

`Callee(args) @(CallerP, CallerV)` substitutes roles in the callee's declared
roster order. The default maps equal role names, not declaration position in
the caller. The substitution must be injective, available in the active roster,
and compatible with every actual argument. It does not move data or insert sends.

`@(P = delivered, V = sampled)` assembles a value from existing role
components. Each entry selects its expression's component at that named role.
The expressions have the same ordinary total shared type and permit `Copy`;
the nonempty role list has no duplicates and lies within the active roster.
Each selected component must already be available. Components are evaluated in
written order. This pure expression neither communicates nor asserts that the
components are equal. Oracle handles, managed services, custody and owner-local
carriers are excluded, including inside ordinary aggregates. Generic assembly
rechecks these data requirements after static substitution.

For example, after `delivered <- send sampled to P`, the sender's `sampled`
and receiver's `delivered` remain distinct values. An explicit
`@(P = delivered, V = sampled)` can supply a family-wide parameter. The source
and native common-control analyses derive agreement from the actual completed
delivery on its normal continuation. They do not turn that conditional execution
fact into an adversarial-honesty or security proof.
Each ordinary layout leaf lowers to `protocol.assemble_roles`; empty unit
layouts have no physical leaves. Independent source/IR comparison checks every
ordered operand/role pair. Participant projection selects the actual component
and removes assembly before execution.

Expression suffix roles are accepted only for protocol-call substitution and
the holder/receiver family of `oracle.empty`. A second suffix refuses. To
restrict an ordinary value's availability, annotate its binding, for example
`selected: bool @P = shared`. An annotation on a literal, name, tuple, service
query or oracle view is not silently discarded.

A protocol loop without `roles(...)` uses its active enclosing roster, including
a surrounding loop's subset. All selected roles must know the count. A missing
`max` is inferred only from a literal upper bound in `0..N`; a runtime count still
requires an explicit static maximum. The bound and count checks remain at the
same occurrence. No inferred participant or maximum is inserted into written AST
fields.

An ordered action with a single named result defaults its site to that binding
name. A protocol loop defaults its site to its index binder. A `site` attribute
overrides the default and must select one outer message, query, protocol call or
loop. Local computation does not acquire a protocol site. Explicit and inferred
sites must be unique in the protocol, including nested loops; use an explicit
attribute if bindings repeat in separate scopes. Renaming a default binder
renames its site and invalidates the corresponding occurrence identity. Explicit
returns and implicit result expressions cannot carry a site label.

`ghost` actual arguments refuse at projection. Holder/receiver arrows on
ordinary data ports refuse during signature checking. Neither can silently become ordinary runtime arguments
or shared availability. Oracle custody and actions use the [oracle source profile](oracles.md).

## Scoped callbacks

A scoped parameter uses `fn(A, B) -> C` for Math or
`local fn(A, B) -> C effects(stop)` for Local. The expected parameter signature
fixes a literal's mode; `fn((a, b)) => value` has one tuple argument, while
`fn(a, b) => value` has two arguments. Callback signatures are not ordinary
runtime types: returning one, storing one in a record, or hiding one in a
zero-length array refuses. At an expected callback argument, a named Math or
Local helper selects its exact declaration and complete static signature.
Explicit statics and inference use the ordinary callable solver; imports,
reexports and module members retain their provider and route. Math and Local
modes must match exactly. Data preconditions must follow from the receiving
guarantees, even for unused callbacks. The selection has no capture inputs and
specializes through the ordinary declaration cache. Forwarding a lexical
callback parameter preserves its contract.
Lexical data, domain and callback bindings do not accept bare static arguments;
`x<Missing>` and `body<bool>` refuse with `source.static-argument`. Explicit
statics on a named declaration remain available at an expected callback argument.

Scoped inputs belong to Math and Local callable declarations. Protocol and Host
entry signatures cannot expose them as execution ports. A named input uses
`name: Type`; a value/default form such as `name = Type` is not an alternative
annotation. This applies both to enclosing ports and callback input labels.
External binding modifiers (`statement`, `witness`, `parameter`) have no native
layout projection and refuse wherever they prefix an input or literal binder;
the same words can still be ordinary contextual parameter names. Ghost inputs
require the independent formal projection and cannot silently bind runtime data.

The root expression of an expected Local literal may be pure or ordered.
For example, `fn(x) => checked(x)` is admitted for an appropriate Local callback
contract. `fn(x) => checked(checked(x))` still hides an ordered operand and
refuses. Calling a Local callback parameter itself requires `<-` in a named
body; calling a Math callback parameter is pure. An empty effect summary never
changes a callback's fixed mode. Explicit `<-` still requires an ordered action.

An omitted Local effect ceiling permits `stop` and `opaque`; `effects()` permits
neither. A declared output effect may depend on a callback input, for example
`effects(body)`. A callback's own acceptance ceiling contains only fixed effect
labels, with no duplicates. Optional input labels and
`where item_from(item, rows)` retain the existing
[whole-item callback obligation](definitions.md#finite-computations); the clause
does not grant a runtime value or execute a descriptor. The Math/Local checker
and independent scoped-source replay own captures, origins and specialization.

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
`assurance.status` as `no-claim` when no layout spec exists, otherwise
`open`, with `outcome: unresolved` and the pending specifications. Each declared
postcondition and each request is an open obligation, including unlabeled clauses
and postconditions not mentioned by a security request. Security groups are
flattened in written order for this inventory; their syntax remains grouped in
the authored export. Target acceptance expressions and formal `site` references
are retained but not interpreted as native values or established associations.
The inventory retains its source span and [companion key](companions.md). Native `status: checked` refers
to native checking. Requesting `--source-claims` with a retained layout spec
refuses with `source.assurance-unavailable`; it cannot return an empty claim
export that hides the request. Typed catalogues, generated obligations,
companions and canonical Lean admission remain a separate integration boundary.

The flat `zkc.source-check/0` report requires `assurance` exactly when the
capture format is `zkc-layout`, for both definitions and selected Entry checks.
The SDK retains this diagnostic object without interpreting it as typed formal
terms. Its exact fields are `status`, `outcome` and `specifications`.
`status` is `no-claim` iff the specifications array is empty, otherwise `open`;
`outcome` is always `unresolved`. Each specification requires `module` and
`protocol` strings, nullable string `name`, Boolean `owner` and `public`, unsigned
32-bit `source`, `begin` and `end`, and an `obligations` array. Each obligation
requires `role` (`postcondition` or `request`), nullable strings `label` and
`companion`, unsigned 32-bit `ordinal`, `begin` and `end`, `status: "open"`, and
`reason: "formal elaboration pending"`. Spans have `begin <= end`. Nullable fields
must be present even when null; missing or unknown fields and other values
refuse with `source-check-format` in the SDK. These source indices and spans
remain diagnostic coordinates, not independently authenticated source bindings.
The separate `source_claim_inventory` array remains required in both scopes;
pending formal intent cannot replace native claim inventory.

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
binders, ghost runtime ports, schemes, virtual oracle definitions, ordinary
multiple-recipient sends and local notation declarations. Reduction occurrences
project to existing scoped callbacks and installed finite descriptor parameters.
The [imported computation client](../../../compiler/test/fixtures/layout/computation/client.zkc)
uses all-layout collection and reduction modules, including separate Math and
Local consumers, through [native Host tests](../../../common/tests/protocol/test_language_computation.py).
The maintained library-wide source migration is still separate. Sections
currently group declarations; imports and notation belong to their enclosing
module. A standalone bodyless protocol is rejected.

[Selected control](selected-control.md) retains Math and Protocol if/match
as registered closed regions with exact captures, placements and yields.
Source checking, common-input derivation and independent original comparison
are distinct from installed executable lowering. The native selected-region
implementation is a dependency of emission; a missing registration refuses
explicitly. Total finite loops use admitted finite consumers, while Local
structured control and bounded Protocol repetition retain their existing
operations. Executable Math scope adapters, input binding, selected
oracle/security profiles and independent formal consumers remain separate
production-cutover gates.
