# Runtime-count nested data

This profile extends [structured mathematics](mathematics.md) and
[structured proof messages](../formats/messages.md). It uses the existing
`protocol → participant → exec → physical` stages and general local interpreter.

## Type and ownership

`!data.sequence<T>` denotes a finite ordered immutable sequence with a runtime
length and one exact element type. Its canonical logical spelling is
`sequence<T>`, where `T` is a canonical logical type spelling. The selected
default physical spelling is `sequence<T>@logical.sequence/0`. A selected layout
retains one complete physical element type, separately from logical `T`; for
example, `sequence<field:bls12-381.fr>@logical.sequence/0[blst/fr]`. Brackets are
omitted exactly for the default child layout. Every element must match the stored
selected layout. Length is a value property, not a type
parameter. Type formation uses the existing structural depth, expansion and
spelling bounds.

The element type must be both copyable and discardable, recursively through
every variant alternative and nested sequence. This requirement applies even
to empty sequences. Affine capabilities and resource units are refused at type
formation. Local immutable keys and opening state can be elements; that grants
neither wire permission nor total mathematical operations. Element identity is
exact: a matching layout or field width is insufficient.

Whole-value role availability remains conservative. A sequence does not assign
owners to individual elements. No packing operation changes disclosure or
resource authority. Existing local loops carry or capture sequences as ordinary
immutable data; they do not introduce per-element resource origins.

## Operations and failure

| Mathematical operation | Meaning | Checked local contract |
|---|---|---|
| `data.sequence_empty` | Empty ordered sequence | `sequence.empty<T>` |
| `data.sequence_append` | Original elements followed by one element | `sequence.append<T>` |
| `data.sequence_length` | Number of elements as `index` | `sequence.length<T>` |
| None | Element at runtime index | `sequence.at<T>` |

Mathematical operations require the existing total-data policy for their complete
types. Checked local `data.exec.sequence_*` operations also handle immutable
non-total payloads, including PCS records. Closed contracts carry the complete
logical element type as a static argument and select `native/sequence.*`.
Their physical specialization selects one complete sequence type: empty returns
that type, append consumes it and its selected element, length returns `index`,
and access returns the selected element unchanged. No operation implicitly
converts or relabels a container.
Source use additionally requires an admitted Language operation binding.

`sequence.at` succeeds exactly when `index < length`. It returns the element
without changing the sequence. Otherwise it stops with `refused:sequence-index`;
there is no default value, padding or undefined result. It is an ordered local
operation without a purity or speculation grant. An unused result does not
permit removing a possible failure. Append leaves its input unchanged.

Use the [scoped control profile](control.md) for bounded iteration and
`exec.match` for variant elimination. No separate sequence map, fold, iterator resource or protocol action
is introduced. Scoped checked execution retains ordinary instruction, output,
live-value and cleanup rules.

## Storage and work

The native representation is an immutable reference-counted tree. Leaves contain
up to four ordered elements and branches contain up to sixteen children. All
levels are packed from the left, and the shape depends only on length. Bulk
construction, decoding and repeated append therefore have the same full charge.
Append copies only the right edge. It never mutates shared storage or tests Arc
reference counts. Index lookup follows the tree; iteration visits leaves in order.

Each sequence caches its expanded value-node count and full retained-byte charge.
Count the sequence root, every nested variant/sequence occurrence and each leaf
value; sharing does not reduce this per-value bound. The full charge includes:

- 256 root bytes and the complete physical descriptor estimate;
- 256 bytes per tree node;
- 32 bytes per branch child slot;
- 128 bytes per CPU element slot and each element's full retained charge.

Runner [retained-value ledgers](../runtime/capacity.md#retained-values-and-logical-work)
count each live root, tree node and nested element allocation once. Inline
storage held by a leaf belongs to that leaf's allocation charge. Construction
checks exact element types, expanded counts and temporary storage before
allocation. Append checks the full result against the per-value ceiling and the
new right edge, root and temporary slots against the invocation allowance.

Expanded value nodes use `Policy.max_table_elements`; bytes use the existing
value-byte policy. A zero node budget cannot hold an empty sequence. Native
sequence kernels additionally have a cumulative work allowance, defaulting to
16,777,216 units. Before operand validation, charge three times one plus the
examined node bound of each input. An immutable sequence root already admitted
by this Runner's backend and still retained counts as one; other sequences keep
their full expanded node bound. Variants include their active payloads and other
leaves count as one. A failed call keeps its charge. Cleanup, a new frame or
changing the configured limit does not refund it. Exhaustion gives
`exhausted:sequence-work`.

The runtime can lend a backend a view of its live retained allocations. Native
sequence validation can skip an intrinsically typed immutable tree node present
in that view. Policy and setup authorization remain backend-owned; the view
cannot validate capabilities, a different backend's values, or type-dependent
numeric views. New nodes and substituted operands absent from the view are
checked. Standalone backend calls and codecs have no such evidence and validate
in full. Local return/yield handoffs keep shared allocations in the ledger until
the receiving binding is installed, with cleanup on every failure path.

Logical work charges the selected element path for `sequence.at`, the stored
length for `sequence.length`, and a conservative copied-edge bound for append.
Other operations retain their full-operand charge. These are deterministic
storage/traversal units, not elapsed time or cryptographic primitive work.
Per-value, instruction, frame, wire and other primitive limits remain separate.

## Native framing and setup

The native proof profile and `zkc.program/0` admit sequences recursively over the
closed native message grammar. Keys, private state, affine data and unsupported
provider leaves stay outside that grammar, including inactive alternatives and
empty sequences. Host programmatic values and proof `wire` inputs use the
same exact physical types and codec.

The sequence frame is:

```text
"ZKCV" || 0x00 || 0x45 || u32le(count)
  || for each element: u32le(child_bytes) || canonical_typed_child_frame
```

The expected type supplies the descriptor; bytes cannot select another type.
Every child frame and the complete frame must be consumed exactly. Lengths,
order, variant tags and matrix dimensions are part of the bytes observed by the
transcript. Empty sequences contain six header bytes and four count bytes.

BLS matrices use their existing canonical sparse COO frame, tag `0x17`:
`u32le(rows), u32le(columns), u32le(nonzeros)`, followed by sorted unique entries
`u32le(row), u32le(column), scalar32le`. Coordinates must be in bounds and stored
scalars canonical and nonzero. Shapes `0 × n` and `n × 0` remain distinct. Both
axes obey the existing matrix dimension limit of 65,536; stored nonzeros cannot
exceed 1,048,576. A sequence of matrices
can have different element shapes without changing its element type.
Native frames apply structured aggregate and peak limits to standalone matrices
too. The typed COO codec has its own accounting.

Decode scans the entire expected frame before allocating payload values or
performing expensive PCS decoding. Expanded container nodes, numeric entries,
group work, descriptor/slot storage and existing conservative peak bytes are
bounded cumulatively across children. Declared excessive counts refuse before
allocation. Arithmetic is checked and reservations are fallible. Malformed
frames, exhausted limits and setup failures retain distinct outcome classes.
The [structured proof profile](../formats/messages.md) owns exact shared
peak accounting and setup rules. Complete types containing PCS data require the
independently authorized deployment key even when empty; active leaves also
check actual key/setup metadata.

Native Lean semantics and external protocol byte compatibility remain separate
obligations; the message grammar alone establishes neither.
