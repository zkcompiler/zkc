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
written directly inside `fn` remains an ordered primitive. A `map` emits one
`algebra.map_realize` per helper instance and row mask, named from both, and an
ordered `local.apply`; comparison checks the helper, mask, signature and site and
accounts for every declaration.
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

## Source and native names

Source names follow the [Unicode profile](lexical.md); native identities retain
their existing ASCII grammars. Language owns the conversion through
[Names.h](../../../compiler/include/zkc/Language/Names.h), with an independent
implementation in Rust Entry tooling. No source/native mapping supplied by an
application is accepted.

A declaration symbol is `s` followed by one frame for each qualified source
segment: its original UTF-8 byte length in decimal without leading zeros, `h`,
then lowercase hex of its exact bytes. `m::α` becomes `s1h6d2hceb1`;
`m::A` becomes `s1h6d1h41`. The same encoding applies to every ASCII and Unicode
segment. Expansion is checked against `symbolBytes` before allocation.
Specialized symbols and long native names retain the
[framed semantic key and collision checks](definitions.md#definition-checking-and-entry-closure).

Each admitted ordered roster determines native labels by zero-based ordinal:

| Source roster | Native spelling |
|---|---|
| Protocol participants | `role` plus eight lowercase hexadecimal digits |
| Entry setup slots | `setup` plus eight lowercase hexadecimal digits |
| Variant alternatives | `case` plus eight lowercase hexadecimal digits |

The first two participants are `role00000000` and `role00000001`. ASCII source
names use these labels too; a source name that looks like a native label gains
no special treatment. Roster count and uniqueness are checked before derivation.
The authenticated order alone establishes correspondence, never a spelling guess
or a separately supplied mapping.

Emission and independent comparison translate every role use, including call
substitutions, selectors and proof choices. Source interfaces retain source role,
setup and alternative names. Their readers compare those ordered rosters against
the derived native labels. Variant constructors, matches and value codecs use
`case` ordinals, while logical layouts keep original alternative names. Entry
admission translates both setup authority keys and setup material keys, as well
as role inputs and results. Native Runner and PIR consumers use native labels;
Entry commands expose source names.

A native variant's nominal identity is the pair
`["zkc.language", lowercase_hex(full_preimage)]`. The preimage is the complete
original UTF-8 canonical source type key, including statics. It is not replaced
by a chosen label or just a digest. Both interface readers require canonical
lowercase even-length hex, bound encoded and decoded sizes before allocation,
decode valid UTF-8 and hash those exact bytes to check the logical identity.
Custody continues to use the full source type-key digest.

Ordered site identities use a per-function preorder occurrence counter, with
bounded leaf suffixes where one logical operation expands. Whitespace and comments
do not affect those sites. Operation/domain IDs, backend service strings, asset
keys and hashes retain their existing grammars.

This encoding changes generated labels and compiled artifact/transcript bytes
for ASCII source as well as Unicode source. Source evaluation and public Entry
keys retain their meanings; cross-build byte equality is not promised. Producers,
readers and fixtures use one current version-0 schema, without legacy readers.

## Independent source comparison

Before simplification, the compiler reparses exact emitted bytes, verifies the
whole native module and independently compares actual SSA with checked source.
It consumes every definition and operation, including unused work, and checks
layouts, operands, bindings, modes, helper targets, roles, sites, captures, carry,
variant arms, custody and returns. The comparison never calls emission. Both consume the checked graph; this
comparison does not independently establish lexical elaboration correctness.
Before translation, callable operators and delimiter notation also pass the separate
[binding witness check](definitions.md#library-defined-operators). It validates
resolution evidence against the lexical family and native action; it does not
prove the parser, name resolver or complete source semantics. An equivalent
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
