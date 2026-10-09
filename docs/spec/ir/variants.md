# Finite local variants

This profile gives local algorithms nominal tagged alternatives without adding
protocol branching. It refines the aggregate and ownership contract of
[mathematical source](../language/README.md) and uses
[structured local control](control.md) for isolated execution.

## Type and value

A finite variant has a nominal identity and a nonempty ordered list of uniquely
named alternatives. Each alternative has an ordered list of logical payload
types, possibly empty. The alternatives and payload types participate in type
identity. Equal physical layouts do not identify distinct nominal variants.
Generic instantiation retains every static actual, including a phantom actual
that does not occur in a payload.

A value contains exactly one alternative label and that alternative's payload.
An inactive payload does not exist. Nested variants obey the same rule. Copy and
drop permissions are independently the conjunction of those permissions over
every payload in every alternative. A variant has no implicit wire codec or
disclosure permission, even when each payload is otherwise serializable.

The [program format](../formats/program.md) admits recursively
copyable variants at those ports; affine variants remain local. It also admits
the closed [structured message grammar](../formats/messages.md).
Port, representation and codec availability remain independent judgments.

Local functions retain construction, ordered match, results and captures.
An installed primitive must explicitly accept its complete payload type; local
variant formation never supplies a wildcard signature. Total native data operations include a tag test under
the separate [structured-data contract](iteration.md).
This restriction does not prove that a protocol never discloses information
computed from a private input; ordinary role and disclosure rules still apply.
An intermediate value can remain in one participant's environment between local
calls, including across interaction rounds or as a protocol-loop carried value.
Its ownership does not thereby permit another participant to use it.

Language enforces its declared copy and drop permissions before
lowering. Portable executable admission retains the existing **affine** local
control discipline: it rejects repeated use but permits an unused value to be
abandoned at frame exit, whether wrapped in a variant or not. It does not certify
a source interface's stronger mandatory-use obligation. `discardable` still
controls explicit storage release and transformations; successful portable
admission alone cannot justify removing a required source use. Library checking
and its body-dependent evidence remain the owner of that stronger guarantee.

## Portable representation

Logical type spelling is `variant:H`, where `H` is lowercase hexadecimal of
compact UTF-8 JSON `["zkc.variant/0", nodes]`. This is a self-contained content
graph, not an ambient registry. A node is either a printable ASCII string or an
array of canonical decimal-string references to earlier nodes. The last node
is the root. Nodes are interned by exact content in first-use postorder: repeated
content shares an entry. Reconstructing and re-encoding must reproduce exactly
the supplied bytes; duplicate or unused entries, forward references, alternate
ordering, noncanonical indices, hex or JSON all refuse.

The expanded root is `[nominal, [[label, [payload, ...]], ...]]`. The nominal is
an opaque array/string identity term (an empty string is refused), never a hash
standing in for equality. A payload is an ordinary logical type string or a
nested variant tree of the same shape. It cannot be an already-encoded variant
string or a physical type. Alternative order is declaration order and matters.
Labels obey the artifact-name grammar. Every ordinary leaf independently forms.

The source producer keeps the complete public semantic type structure
in the nominal: declaration identity, ordered static actuals, captured exact
subjects and dependencies, fields and semantic payload types. It preserves
opaque abstract members even when they have equal physical representations.
The content graph shares those exact subjects and subtrees across nested types.
Projection or standalone loading needs no external table to recover equality.
This self-contained form avoids an ambient type registry at every extraction,
link and checker boundary. It shares repetition *within* a type, not between
occurrences or modules; a module-level codec can later share complete canonical
spellings without changing nominal equality. Large captured subjects therefore
remain subject to the artifact byte bound, even when decoding is inexpensive.

The logical spelling is bounded by 256 KiB, the graph by 16,384 entries and
expanded depth 64. Readers bound the sum of materialized nodes by 8 MiB of
compact JSON bytes and 200,000 expanded nodes **before copying** referenced
subtrees. Each sum is additionally at most 512 times the logical spelling byte
length. This bounds expansion work proportionally to input size, including
modules with many distinct small graphs; it is not a wall-clock guarantee. A string counts as one node and its compact JSON byte length; an array
counts as one plus its children's node counts, and two bracket bytes plus child
byte lengths and separating commas. Variant nesting remains at most eight,
alternatives 32, and immediate payload entries 128. Bounds are simultaneous;
none promises every combination fits. The containing artifact retains its
existing byte and structural limits. Ordinary nontype fields retain their own
limits; a `variant:` prefix in a literal attribute does not enlarge them.

The Rust runtime additionally limits installed type metadata as an operational
loading policy. One admission charges at most 64 MiB across distinct physical
spellings and every resolved binding signature, including unused signatures.
A variant uses the descriptor charge below; a structural application adds
`512 + 256 * argumentCount` plus descriptor charges of its type arguments.
Repeated physical spellings share one installed descriptor charge; binding
signature positions are charged independently. A single logical parse also
precharges newly allocated descriptors against 64 MiB before construction.
Exhaustion reports `ErrorCode::Limit` with `type descriptor byte ceiling`.

Sharing spans graph subtrees and structural type arguments at the same logical
depth. Cache hits still charge all expanded logical nodes; they cannot bypass
depth or node admission. An inline graph subtree can satisfy a later text lookup
only after that spelling passes its own expansion bound; the containing graph's
bound alone is insufficient. This loading policy is separate from portable formation
and live-value accounting: C++ formation can accept a program that the Rust Host refuses for loading
capacity; the independent Lean descriptor model has its own admission scope.
Executable values incur the charges below. Bounded unpack scratch is additional
to installed metadata; concurrent
loads and allocator overhead are not a process memory guarantee.

The physical spelling appends `@logical.variant/0`; those 18 suffix bytes are
additional to the logical bound. Payloads still use logical types, whose admitted
default representations determine their physical values. This profile supplies
no arbitrary alternative representation. Unknown descriptor tags and malformed
records refuse.

The portable instructions are:

```text
["variant", site, type, alternative, [payload_values, ...], result]
["match", site, scrutinee, [captures, ...],
  [[alternative, [payload_names, ...], body], ...], [results, ...]]
```

Construction checks the exact chosen alternative's payload types and arity.
Matching lists every alternative exactly once, in descriptor order. There is no
default arm, guard or hidden fallback. Each arm sees its active payload names
followed by the named captures; other enclosing bindings are unavailable.
Payload argument names and captures must not collide. All continuing arms yield
the same ordered types. The scrutinee and affine captures are transferred once
at the match boundary; checks within each alternative remain independent.

## Execution, resources and observations

Construction does not invoke a cryptographic primitive. Matching dispatches to
one admitted arm and creates only that arm's frame. Nested resources retain
their original issuance identity, generation and authorized view. Packing,
unpacking or cloning a trusted implementation handle cannot issue a fresh
resource. The implementation counts the complete retained active payload;
sharing does not justify undercharging the storage bound.

The executable physical reference charges each variant descriptor by
`512 + 4 * logicalSpellingBytes + 256 * alternativeCount + 256 * payloadEntryCount`,
plus the same recursive charge for nested descriptors. An active variant value
adds `256 + 512 * activePayloadCount` and each active value's retained-byte charge.
These are conservative profile charges, not allocator measurements. The native
representation retains canonical nominal bytes, not an additional expanded
nominal tree, and uses bounded immutable descriptor storage and compile-time size
checks. The independent Lean model uses the same declared charge without
establishing native execution correspondence. Descriptor sharing does not discount
a live value's budget. Changing this accounting changes the executable profile
and requires corresponding updates to its actual consumers.

The selected arm's local origin appends `["match", site, alternative]`. This
origin participates in actual local observations and domain separation in the
same way as other local control. It is not automatically sent to another role
or added to a transcript. Construction and matching preserve reached terminal
outcomes, residual resource state and ordered effects. In particular, resource
exhaustion is not an ordinary `Err` alternative or cryptographic rejection.

Source/candidate correspondence checks every alternative, including dormant
ones. Optimizations preserve the active-only value, conservative ownership and
complete stopped behavior. Fiat–Shamir and static-schedule consumers apply
their local-control restrictions recursively through match arms; they cannot
ignore a nested draw or an unsupported resource just because the outer
instruction is a match.
The executable match profile refuses transcript observations and challenges,
including the installed external duplex observation/sample operations and Monero
update, directly or through a local helper. This is a lexical operation restriction, including transitive helper bodies;
it is not a general information-flow or implicit-flow analysis. A local match
can return ordinary data that influences later local control. Public transcript
schedule safety is owned by the selected construction/profile checker, which
also checks resource-bearing control and replay; static-schedule consumers
refuse local control. Portable variant admission alone does not establish that
stronger construction judgment.

Every consumer admits this carrier independently of its producer.
