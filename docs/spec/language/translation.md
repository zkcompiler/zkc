# Source translation

This native contract defines source emission, comparison and retained interfaces.

## Translation and retained interface

The source model has Math, Local and Protocol body modes, checked types, explicit
regions and static arguments. Closing an Entry substitutes already checked bodies;
it never reparses templates. Closed instances are memoized by declaration, mode
and exact static type identity. Only closed definitions enter original MLIR.

Math helpers become private `func.func` definitions. A selected formula relation
adds a non-callable `relation.declare` and a private Boolean `func.func`; its exact
link is retained in the interface. Opaque and captured relations emit declarations
only. Predicate helpers have no executable symbol uses. Every selected predicate
undergoes bounded helper expansion and polynomial observation checks on scratch
copies before interface admission, including unused observations. Ordered helpers become
`local.func`. A math helper called inside ordered code retains its mathematical
body and receives a data-only `local.realize` declaration. The local call is an
ordered `local.apply` occurrence; native preparation realizes the helper through
the common polynomial and calculation lowerers before expanding that call.
Formal intermediates never become local runtime values. Inline arithmetic
written directly inside `fn` remains an ordered primitive.
Protocols become `protocol.func`, with explicit `protocol.local_call` for owned calls.
Total operations use their admitted dialect identities; ordered operations use
existing executable bindings. No additional protocol interpreter is introduced.

Products flatten in declaration order. Variants retain a native tagged descriptor
with exact nominal identity and payload layouts. A noncopyable restricted nominal
or associated value has a leading `resource_unit` custody leaf even when its data
is empty. Custody slot identities use the complete SHA-256 digest of canonical source type identity, with collision refusal; traversal order does not affect them. Empty unrestricted products have no leaves, but remain logical values.

Qualified symbol components encode as `s` followed by each component's decimal
byte length, `_`, and spelling. `example::Transfer` becomes `s7_example8_Transfer`.
Specialized symbols use the [framed semantic key](definitions.md#definition-checking-and-entry-closure). Ordered site identities
use a per-function preorder occurrence counter, with bounded leaf suffixes where
one logical operation expands. Whitespace and comments do not affect these sites.

Before simplification, the compiler reparses exact emitted bytes, verifies the
whole native module and independently compares actual SSA with checked source.
It consumes every definition and operation, including unused work, and checks
layouts, operands, bindings, modes, helper targets, roles, sites, captures, carry,
variant arms, custody and returns. The comparison never calls emission. An equivalent
but differently structured rewrite can refuse. Inputs, receives, restrictions,
queries, owned calls and protocol results retain exact role sets. Derived math
and aggregate leaves may have wider native availability than the conservative
source value; comparison requires containment and still matches their complete
operation and operand graph.

`CheckedOriginal` owns immutable source, original bytes, comparison counts,
interface, toolchain identity and a bound diagnostic location map. It exposes no
mutable original IR. The existing compiler receives those bytes and the selected
protocol symbol. Run jobs emit `zkc.run/0`; proof jobs use the native proof policy
and deployment schemas. Both contain ordinary `zkc.program/0` participant programs.
Every protocol in the selected closure passes target preparation.
