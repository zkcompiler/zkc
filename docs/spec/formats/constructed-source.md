# Constructed participant export

`zkc-compile protocol-constructed-lean SOURCE.mlir POLICY.json CANDIDATE.mlir`
exports the actual unsimplified verifier from a supplied candidate. The command
first calls `checkNativeProof`, including independent construction/codec checks
and comparison of the entire candidate against retained source. It does not
export a replacement verifier or infer a cryptographic experiment.

The versioned exact array carrier is `zkc.constructed-source/0`:

```text
[format, source-sha256, candidate-sha256, entry, role, participant,
 policy-json, handlers, inputs, outputs, instructions, returned]
```

The source identity hashes the original supplied MLIR bytes. The candidate
identity hashes its generic MLIR printing, without locations. The policy string
is the existing canonical native policy serialization. Each handler entry is
`[symbol, generic-body-sha256, generic-body]`. Selected Local calls recursively
expand their actual bodies; call results refer to the actual returned operands.
Primitive provenance includes the selected invocation chain. Binding declarations
are retained in full. Source, handler and candidate hashes are evidence identities;
a consumer authenticates them by fresh native re-extraction and exact comparison.

Inputs and outputs are ordered nominal MLIR type strings. Instructions use
current-context positions, with inputs initially in declaration order. Each
primitive application prepends its complete result product. A one-result product
is also a scalar; a multi-result product is followed by explicit projections,
each prepending one scalar. Zero-result applications still execute. Guards do not
extend the context. All final results, including transcript state, are returned.

| Instruction | Exact shape |
|---|---|
| Primitive | `["apply", primitive, operand-references]` |
| Result projection | `["project", result-types, component-index, product-reference]` |
| Rejecting guard | `["guard", condition-reference, retained-attributes]` |
| Explicit terminal stop | `["stop", reason, retained-attributes]` |

A primitive is `[operation-name, attributes, binding-declaration, invocation-origin,
argument-types, result-types]`. Empty binding text means no native binding.
The attributes include native properties, source sites, provider parameters and
occurrence encodings. A primitive is a regionless native operation; selected Local
bodies cannot be supplied as opaque primitive substitutes. The supported leaves
are algebra, arithmetic, crypto and data operations, send/receive, local literals,
and registered bound operations. Consumers must independently admit the exact
primitive vocabulary and provide its meaning.

The bounded profile supports straight-line selected Local bodies, actual receives,
guards, explicit terminal stops and record codecs whose handlers use those forms.
The exact zero-result Local conditional with empty successful yield and rejecting
alternative is a guard. Runtime by-value `protocol.loop` uses the structured carrier described below.
Other control and unsupported leaves refuse, including control in selected
handler bodies, general native branches and parameter-selected loop counts. Import retains unused ordered provider work,
post-final-message observations, decode guards and codec finalization. Stops from
primitive interpretation bypass subsequent work. Host-created initial transcript
state and raw proof buffers remain explicit participant inputs.

The structured sibling carrier is `zkc.constructed-control/0`:

```text
[format, source-sha256, candidate-sha256, entry, role, participant,
 policy-json, handlers, inputs, outputs, body]
```

Headers and primitive instructions have the same meaning as the flat carrier.
A body is one of:

| Body | Exact shape |
|---|---|
| Flat fragment | `["flat", instructions, returned]` |
| Sequence | `["sequence", intermediate-types, first, next]` |
| Conditional | `["branch", condition-reference, yes, no]` |
| Runtime loop | `["loop", maximum, count-reference, carried-types, initial-references, capture-types, captured-references, body, next]` |

Sequence replaces the input context with the first body's complete returned
values. A loop reads a `ui64` count, refuses a count above the declared maximum
before entering its body, and iterates from index zero. Each iteration receives
`[index, carried-values..., captured-values...]` and returns exactly the carried
values. Its suffix receives `[final-carried-values..., original-context...]`.
Stops propagate without running the suffix. Zero iterations run the suffix with
the initial carried values. The exporter retains a single body and actual
captures; it does not unroll based on a test execution. Before a loop it packs
actual scalar references in context order, retaining all prefix effects. This
removes dead tuple containers and duplicate aliases, not primitive calls.
Conditional bodies are admitted by the formal reader; the current native exporter
does not emit general native conditional control.

Limits are 16 MiB native input per CLI file, 1 MiB exported JSON, 64 nested body/Local-call levels, 4096 inspected operations and 2048 exported instructions. The
formal executable runs a separate text-capacity preflight (128 JSON levels,
262144 bytes per text) before structural decoding. Structural decoding bounds references to 8192,
input/output ports to 512 and selected handlers to 256. Structured bodies have
64 decoder levels and a conservative expanded-control bound of 65536: flat work
is instruction count plus one, sequence adds both children plus one, branch takes
the larger child plus one, and loop uses one plus maximum times (body bound plus
one) plus suffix bound. This is executable admission policy, not native cost or
cryptographic adversary complexity. It rejects malformed
constructor shapes, unknown instructions, invalid result projections and mistyped
operands. See the [formal admission contract](../../../lean/docs/spec/constructed-source.md).

Native checker/exporter correctness, Local-body expansion, primitive conformance,
record-byte decoding and subsequent lowering/runtime execution remain native
trusted or tested boundaries. The primitive descriptor continues to name its
actual suite. Interpreting a selected transcript primitive as an ideal oracle in
a separate experiment does not identify deployed Merlin with that oracle.
