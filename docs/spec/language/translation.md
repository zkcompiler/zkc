# Source translation

This native contract defines source emission, comparison and retained interfaces.

## Translation and retained interface

Source names resolve to lexical binding identities. Typed elaboration derives
explicit region inputs, mutable state successors and resource joins, producing
an immutable checked graph with Math, Local and Protocol body modes. Mutable
source bindings become immutable checked values; no runtime variable store or
additional public IR is introduced. A temporary statement constraint solver selects
unique participants and checks original formation obligations; only concrete roles
and owners enter the checked graph. Type and resource uses are checked in source
order without guessing owners. Checks that depend on component sets run after
selection. Closing an Entry substitutes already checked bodies;
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
Source `require` is one checked action: protocol checks emit `protocol.guard`; local checks emit `local.if` with a
continuing true branch and `local.stop` with reason `reject` on false. Comparison
checks both branches, their sites and the rejection reason. Raw bound
`control.require` remains a separate backend operation.

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
variant arms, custody and returns. The comparison never calls emission. Both consume the checked graph; this
comparison does not independently establish lexical elaboration correctness. An equivalent
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
