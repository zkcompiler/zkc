# Runtime-count nested data

This profile extends [structured mathematics](structured-mathematics.md) and
[structured proof messages](structured-proof-messages.md). It uses the existing
`protocol → participant → exec → physical` stages and general local interpreter.

## Type and ownership

`!data.sequence<T>` denotes a finite ordered immutable sequence with a runtime
length and one exact element type. Its canonical logical spelling is
`sequence<T>`, where `T` is a canonical logical type spelling. The selected
physical spelling is `sequence<T>@logical.sequence/0`; every element uses its
installed default representation. Length is a value property, not a type
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
Source use additionally requires an admitted Language operation binding.

`sequence.at` succeeds exactly when `index < length`. It returns the element
without changing the sequence. Otherwise it stops with `refused:sequence-index`;
there is no default value, padding or undefined result. It is an ordered local
operation without a purity or speculation grant. An unused result does not
permit removing a possible failure. Append leaves its input unchanged.

Use existing `local.for` for bounded iteration and `local.match` for variant
elimination. No separate sequence map, fold, iterator resource or protocol action
is introduced. Local checked execution retains ordinary instruction, output,
live-value and cleanup rules.

## Storage and work

The native representation stores an immutable reference-counted element slice.
Cloning a sequence shares storage; append allocates a new slice. Append therefore
has linear element-copy cost; repeatedly appending has quadratic cumulative cost.
This representation is a bounded initial implementation, not a throughput claim.

Each sequence caches its expanded node count and conservative retained-byte
charge. Count the sequence root, every nested variant/sequence occurrence and each leaf;
sharing does not reduce either charge. The current storage estimate is 256
wrapper bytes, the complete logical descriptor estimate, 512 bytes per element
slot, and each element's retained charge. Formation checks exact element physical
types. Construction checks counts before inspecting elements, then checks peak
storage before copying into the immutable slice. Append also charges coexistence
of its old input, new vector and new slice before allocation.

Expanded nodes use `Policy.max_table_elements`; bytes use the existing value-byte
policy. A zero node budget cannot hold an empty sequence. A backend additionally
limits cumulative sequence-kernel work, defaulting to 16,777,216 units. At native
kernel dispatch, before the backend recursively validates operands,
charge `3 * (1 + sum(expanded_nodes(input)))`.
A non-container leaf counts as one. This is a conservative container-traversal
metric, not elapsed time or cryptographic primitive work. Work consumed by a
failed call remains spent. Cleanup, a new frame or changing the configured limit
does not refund it. Exceeding the allowance gives `exhausted:sequence-work`.
Other kernels and codecs retain their own bounds.
The generic runner validates call operands before dispatch; frame entry and exit
also validate sequence elements under the backend's policy. These traversals use
existing frame/instruction and value limits, independently of the sequence-kernel
work allowance. Exhausting that allowance therefore does not avoid the runner's
preceding bounded validation. Each native proof invocation creates a
backend; attempts within that invocation retain its consumed work.

## Native framing and setup

The native proof profile and `zkc.program/0` admit sequences recursively over the
closed native message grammar. Keys, private state, affine data and unsupported
provider leaves stay outside that grammar, including inactive alternatives and
empty sequences. Host programmatic values and proof `wire` inputs use the
same exact physical types and codec.

The sequence frame is:

```text
"ZKCV" || 0x01 || 0x45 || u32le(count)
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
The [structured proof profile](structured-proof-messages.md) owns exact shared
peak accounting and setup rules. Complete types containing PCS data require the
independently authorized deployment key even when empty; active leaves also
check actual key/setup metadata.

Native Lean semantics and external protocol byte compatibility remain separate
obligations; the message grammar alone establishes neither.
