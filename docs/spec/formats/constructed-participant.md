# Constructed validator export

`zkc-compile protocol-constructed-participant SOURCE.mlir POLICY CANDIDATE.mlir`
exports the validator participant of a supplied native proof candidate. It first
runs the same check as `protocol-check-proof`: the candidate must equal the
[construction](../ir/construction.md) of the original source under the
[deployment policy](proof.md#deployment-policy-and-descriptor), including every
inserted transcript helper. A refused candidate produces no export. The command
accepts the same mathematical-selection options as `protocol-check-proof`.

The export is the input of the formal
[transcript-construction rule](../../../lean/docs/spec/fiat-shamir.md). It neither
constructs a validator nor assigns a meaning to any operation.

## Envelope

The format is an exact tagged array, `zkc.constructed-participant/0`:

```text
[format, source-sha256, candidate-sha256, policy, participant,
 inputs, outputs, instructions, returned]
```

`source-sha256` hashes the exact supplied source bytes. `candidate-sha256` hashes
the candidate module's generic operation print, without locations. Both are
`sha256:` followed by 64 lowercase hexadecimal digits; they identify bytes and
are not authority. `policy` is the canonical policy array. `participant` is the
symbol of the participant whose instance is the policy entry and whose role is
the policy validator; exactly one must exist. `inputs` and `outputs` are the
printed MLIR types of its signature, in order.

## Instructions

References are absolute positions: the participant's inputs first, then every
operation result in execution order. Each instruction is:

```text
[operation, attributes, binding, operands, result-types]
```

`operation` is the MLIR operation name. `attributes` lists the operation's
attribute dictionary in its sorted order as `[name, value]` pairs; a value is
`["string", text]`, `["symbol", name]`, `["bool", value]`, `["integer",
decimal]` (unsigned for unsigned integer types, otherwise signed),
`["strings", [text, ...]]`, or `["text", printed]` for any other attribute kind.
`binding` is `[]` without an operation binding, otherwise the referenced
`local.binding` declaration as `[contract, [argument, ...], implementation]`.
`operands` are references and `result-types` are printed MLIR types.

Exported operations are regionless operations of the `algebra`, `arith`,
`crypto` and `data` dialects, `protocol.receive`, `protocol.send`,
`protocol.service_query` and `local.bool_constant`. A `local.call` to a
single-block `local.func` is expanded in place: its formals denote the actual
operands and its results denote the operands of the helper's final
`local.return`, so a helper appears only through the operations it executes. The
participant's final `protocol.finish` operands become `returned`. Any other
operation, any region, a successor or a missing reference refuses the export
with a `constructed-participant-*` diagnostic.

Limits: 512 inputs and results, 64 nested helper levels, 4096 inspected
operations, 2048 exported instructions and 1 MiB of printed JSON.

## Boundary

The exporter is reviewed native code. It reads the checked candidate; it does
not prove that the printed record denotes that candidate. Its refusals are
defensive: a candidate that passes the native check uses only exported forms. A
consumer interprets operation names, bindings and attributes explicitly, and
refuses what it does not recognize. The [formal
bridge](../../../lean/bridges/construction/README.md) regenerates its retained
data from this export and checks the exact bytes.
