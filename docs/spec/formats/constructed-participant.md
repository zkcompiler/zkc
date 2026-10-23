# Constructed participant and pair exports

`zkc-compile protocol-constructed-participant SOURCE.mlir POLICY CANDIDATE.mlir`
exports the validator participant of a supplied native proof candidate. It first
runs the same check as `protocol-check-proof`: the candidate must equal the
[construction](../ir/construction.md) of the original source under the
[deployment policy](proof.md#deployment-policy-and-descriptor), including every
inserted transcript helper. A refused candidate produces no export. The command
accepts the same mathematical-selection options as `protocol-check-proof`.
The optional `--role=producer` selects the policy producer instead;
`--role=validator` selects the default explicitly. Roles are policy selections,
not arbitrary source participants. Conflicting or repeated role options refuse.

`zkc-compile protocol-constructed-pair SOURCE.mlir POLICY CANDIDATE.mlir` checks
the candidate once and exports both actual participants in the exact array:

```text
["zkc.constructed-pair/0", producer-record, validator-record]
```

Each child uses the participant envelope below, with identical source identity,
candidate identity and full policy. Neither command reconstructs an interactive
source producer as the exported producer. The pair command accepts mathematical
selection options, and refuses a role option because both roles are required.

The export is the input of the formal
[transcript-construction](../../../lean/docs/spec/fiat-shamir.md) and
[participant projection](../../../lean/docs/spec/participant-projection.md) rules.
It neither constructs a validator nor assigns a meaning to any operation.

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
the selected policy producer or validator; exactly one must exist. `inputs` and `outputs` are the
printed MLIR types of its signature, in order.

## Instructions

References are absolute positions in a scoped environment: the participant's
inputs first, then every operation result in execution order. A loop body sees
the environment at the loop, then its block arguments and then its own results;
after the loop, the loop's results take consecutive positions starting at the
position the induction index had in the body: one position fewer than the block
arguments, since the induction index has no result. Each instruction is:

```text
[operation, attributes, binding, operands, result-types, regions]
```

`operation` is the MLIR operation name. `attributes` lists the operation's
attribute dictionary in its sorted order as `[name, value]` pairs; a value is
`["string", text]`, `["symbol", name]`, `["bool", value]`, `["integer",
decimal]` (unsigned for unsigned integer types, otherwise signed),
`["strings", [text, ...]]`, or `["text", printed]` for any other attribute kind.
`binding` is `[]` without an operation binding, otherwise the referenced
`local.binding` declaration as `[contract, [argument, ...], implementation]`.
`operands` are references and `result-types` are printed MLIR types. `regions`
is empty except for `protocol.loop`, whose single region is
`[argument-types, instructions, yielded]`: the printed types of its block
arguments (the induction index, the carried values, then the captured values),
its body, and the references its `protocol.yield` returns. A loop's operands are
its count, the initial carried values and the captured values, whose block
arguments denote those operands unchanged in every iteration; its `carried`
attribute counts the carried values. The captured values are the original
repeat's captures followed, for a loop that carries the transcript, by the
induction indices of its enclosing loops.

Exported operations are regionless operations of the `algebra`, `arith`,
`crypto` and `data` dialects, `protocol.receive`, `protocol.send`,
`protocol.service_query`, `local.bool_constant`, `local.guard`,
`protocol.loop` and `local.call`. A `local.call` to a helper of the original
source module remains a call; its callee names that helper. A `local.call` to a
helper the construction inserted is expanded in place: its formals denote the
actual operands and its results denote the operands of the helper's final
`local.return`, so such a helper appears only through the operations it
executes. The participant's final `protocol.finish` operands become `returned`.
Any other operation, any other region, a successor or a missing reference
refuses the export with a `constructed-participant-*` diagnostic.

Limits: 512 inputs and results, 64 nested blocks, 4096 inspected operations,
2048 exported instructions in total and 1 MiB of printed JSON per participant.
The pair container applies these limits independently to its two children.

## Boundary

The export reads the checked candidate; it does not establish that the printed
record denotes that candidate. Its refusals are
defensive: a candidate that passes the native check uses only exported forms. A
consumer interprets operation names, bindings and attributes explicitly, and
refuses what it does not recognize. A retained call is interpreted by the
original source's helper of the same name and checked signature. That the
candidate's helper of that name computes the same function belongs to the
native construction, whose check reconstructs the whole candidate from the
source; the export does not establish it. The [formal
bridge](../../../lean/bridges/construction/README.md) regenerates its retained
data from this export and checks the exact bytes.

The independent pair reader in `lean/bridges/construction/pair.py` also checks
the exact paired envelope and shared identities/policy. The formal
`Zkc.Construction.AuthoredPair` selection fixes the complete participant trees,
source helper dependencies, input contract, role maps and retained target before
admission. Its producer structural check and whole-artifact equality do not
establish original-source-to-constructed-producer correspondence. That theorem,
export/read-back correspondence and domain interpretation remain separate
obligations; a native check or a matching digest is not their proof.
