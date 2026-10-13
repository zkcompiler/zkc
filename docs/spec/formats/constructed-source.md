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
alternative is a guard. Other control and unsupported leaves refuse, including
control in selected handler bodies. Import retains unused ordered provider work,
post-final-message observations, decode guards and codec finalization. Stops from
primitive interpretation bypass subsequent work. Host-created initial transcript
state and raw proof buffers remain explicit participant inputs.

Limits are 16 MiB native input per CLI file, 1 MiB exported JSON, 64 Local call
nesting levels, 4096 inspected operations and 2048 exported instructions. The
formal reader additionally bounds each text to 262144 bytes, references to 8192,
input/output ports to 512 and selected handlers to 256. It rejects malformed
constructor shapes, unknown instructions, invalid result projections and mistyped
operands. See the [formal admission contract](../../../lean/docs/spec/constructed-source.md).

Native checker/exporter correctness, Local-body expansion, primitive conformance,
record-byte decoding and subsequent lowering/runtime execution remain native
trusted or tested boundaries. The primitive descriptor continues to name its
actual suite. Interpreting a selected transcript primitive as an ideal oracle in
a separate experiment does not identify deployed Merlin with that oracle.
