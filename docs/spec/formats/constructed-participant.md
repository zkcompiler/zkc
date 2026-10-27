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
 inputs, outputs, instructions, returned, service-ports]
```

`source-sha256` hashes the exact supplied source bytes. `candidate-sha256` hashes
the candidate module's generic operation print, without locations. Both are
`sha256:` followed by 64 lowercase hexadecimal digits; they identify bytes and
are not authority. `policy` is the canonical policy array. `participant` is the
symbol of the participant whose instance is the policy entry and whose role is
the selected policy producer or validator; exactly one must exist. `inputs` and `outputs` are the
printed MLIR types of its signature, in order.

The installed empty-suite policy has no replaced service or draw pair. It exports
the actual projected plain participants without transcript construction: all
input and output types are the real data ABI, including products and sequences.
The single-service Fiat–Shamir policy exports its final transcript capability
as before. Readers must not infer or append a capability for an empty suite,
and must not drop a plain participant's last real data output.

The independent formal reader maps recursive `!data.sequence` and one-constructor
`!local.variant` products to the shared structured type. It checks canonical
variant DAG spelling and retains the exact nominal identity, constructor and
ordered component types. Recursive service types are not message data. This
logical admission does not select a native wire codec or prove its realization.

`service-ports` is the complete retained native service interface, separate
from those data and transcript inputs, including ports with no queries. Each
row is `[name, owner, root-input, role-input, contract]`. The two indices are
canonical decimal strings: `root-input` is the original entry's global input
index; `role-input` is the native port position in the role's complete input
interface after construction removes the selected validator services. The
port's state identity is the original entry and root input, not its name or a
query site. Borrowed aliases of one root therefore share state.

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

Only `protocol.service_query` has a seventh field:

```text
[operation, attributes, binding, operands, result-types, [],
 [origin-template-hex, repeat-coordinate-references]]
```

Its native attributes remain exactly `port`, `method` and `site`; source
annotations are separate from that dictionary. The origin uses the canonical
`zkc.native-origin-template/0` encoding and retains its source application and
repeat path and the source query event, including local service input,
contract, method and transported owner. Coordinate references name enclosing
loop induction values, outermost first. They are occurrence metadata, not
ordinary request operands. A field draw has no data operands and one nominal
field result. Local draws neither consume nor produce transcript state.

`operation` is the MLIR operation name. `attributes` lists the operation's
attribute dictionary in its sorted order as `[name, value]` pairs; a value is
`["string", text]`, `["symbol", name]`, `["bool", value]`, `["integer",
decimal]` (unsigned for unsigned integer types, otherwise signed),
`["strings", [text, ...]]`, or `["text", printed]` for any other attribute kind.
`binding` is `[]` without an operation binding, otherwise the referenced
`runtime.binding` declaration as `[contract, [argument, ...], implementation]`.
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

Participant operations retain the regionless mathematical operations of the
`algebra`, `arith`, `crypto` and `data` dialects, `protocol.receive`,
`protocol.send`, `protocol.service_query`, `protocol.guard`
and `protocol.loop`. A guard has exactly `site` and `owner` string attributes;
the native participant profile requires that owner to match the enclosing
participant role. The renderer checks its Boolean input and emits the guard
observation. Its body remains subject to fixed-artifact admission.
`protocol.local_call` invokes an ordinary scoped
`func.func`. Calls to original source helpers retain their operation name and
callee. Construction-inserted helpers are expanded at their actual operands;
borrowed `func.call` invocations inside them either retain an original helper's
identity or expand another generated helper.

Helper expansion reads the admitted source execution closure. Its data
signature excludes the borrowed scope and unpacks the outcome payload. The
exported `exec.apply` and `exec.boolean` instructions retain their actual name
and attributes, with the data inputs and successful payload results recovered
from the checked CFG. Calls use the same data projection. The scope, outcome
packaging, continuation and stop-propagation edges are checked by native
execution admission; they are not instructions of this logical participant
carrier. A generated helper's `exec.return` payload supplies the call's result
references. A participant's `protocol.finish` supplies `returned`.

This reader does not flatten arbitrary generated control flow. Nested control
inside a generated helper, other unsupported operations, successors outside
the admitted helper view, or missing references refuse with a
`constructed-participant-*` diagnostic. In particular, native admission of a
conditional codec helper does not imply support in this formal export.

Limits: 512 inputs and results, 64 nested blocks, 4096 inspected operations,
2048 exported instructions in total and 1 MiB of printed JSON per participant.
The pair container applies these limits independently to its two children.
Readers require the exact current shapes, including an empty service interface
and the query annotation where applicable, with no compatibility reader.
The format remains `/0` under the
repository's pre-stabilization version policy.

## Boundary

The export reads the checked candidate; it does not establish that the printed
record denotes that candidate. Native admission and the export's supported
profile are separate checks. A consumer interprets operation names, bindings and attributes explicitly, and
refuses what it does not recognize. A retained call is interpreted by the
original source's helper of the same name and checked signature. That the
candidate's helper of that name computes the same function belongs to the
native construction and its independent postcondition; the export does not
establish it. The logical carrier also does not prove preservation of native
scope, resource accounting, failure timing or cleanup. The [formal
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

Local-service admission additionally compares the complete interface with the
original input scopes and contracts, resolves each request through source
applications, restrictions and repeat captures to its original root, and
checks exact owner, request, nominal result and static/dynamic occurrence.
Only the installed field `draw` is admitted. Unsupported methods refuse.
The existing validator construction rule continues to refuse local requests.
