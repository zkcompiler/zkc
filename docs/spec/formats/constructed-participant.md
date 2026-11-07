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
 inputs, outputs, instructions, returned, service-ports, catalogue]
```

`source-sha256` hashes the exact supplied source bytes. `candidate-sha256` hashes
the candidate module's generic operation print, without locations. Both are
`sha256:` followed by 64 lowercase hexadecimal digits; they identify bytes and
are not authority. `policy` is the canonical policy array. `participant` is the
symbol of the participant whose instance is the policy entry and whose role is
the selected policy producer or validator; exactly one must exist. `inputs` and
`outputs` are the complete structured [logical types](logical-types.md) of its
signature, in order. Every type position below uses that same closed vocabulary.

The installed empty-suite policy has no replaced service or draw pair. It exports
the actual projected plain participants without transcript construction: all
input and output types are the real data ABI, including products and sequences.
The single-service Fiat–Shamir policy exports its final transcript capability
as before. Readers must not infer or append a capability for an empty suite,
and must not drop a plain participant's last real data output.

Variant types retain their complete structured nominal identity, all alternatives
in declaration order, and each alternative's ordered payload types. Boolean
selection uses exactly `then`, `else` with empty payloads. The independent formal
reader currently supports sequences and one-constructor products; multi-alternative
variants and the selected records below still refuse until coordinated migration.
Recursive service types are not message data. Logical publication does not select
a native wire codec or prove its realization.

`service-ports` is the complete retained native service interface, separate
from those data and transcript inputs, including ports with no queries. Each
row is `[name, owner, root-input, role-input, contract]`. The two indices are
canonical decimal strings: `root-input` is the original entry's global input
index; `role-input` is the native port position in the role's complete input
interface after construction removes the selected validator services. The
port's state identity is the original entry and root input, not its name or a
query site. Borrowed aliases of one root therefore share state.

`catalogue` is `[nominal-rows, service-rows]` in the
[structured-source encoding](structured-source.md#envelope-and-types): the
installed rows of every catalogue identity the participant names, closed under
associated members, in native catalogue order, and the rows of the random
services it names, in registry order. The named identities are the domain
arguments of its input, output, instruction-result and loop-argument types and
of its operation bindings, selected-arm argument/payload types, the policy's
transcript suite, and the contracts of
its service ports with the fields they sample. A reader resolves the associated
members and capability facts of a binding signature through these rows, never
through a table of its own, and admits the rows only when they agree with its
own catalogue. The rows are producer data, not authority.

## Instructions

References are positions in a scoped environment: the participant's
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
repeat and branch path and the source query event, including local service input,
contract, method and transported owner. Coordinate references name enclosing
loop induction values, outermost first. A branch contributes no coordinate.
Inside a selected arm, each enclosing coordinate is rebased through actual
explicit captures of that induction value. Every duplicate Copy capture keeps
its own local slot and its induction lineage, so any such alias can be captured
again through nested closed arms. Invariant loop captures likewise forward
lineage from their actual operands to every corresponding body formal. A loop's
count and initial carried operands do not establish induction lineage for its
body formals: carried values can change on the next iteration. The exported
coordinate names the first available actual alias in the current frame; the
other aliases remain distinct ordinary slots. A missing association refuses with
`constructed-participant-service-origin`; neither an equal sort nor numeric
slot coincidence supplies it. They are occurrence metadata, not
ordinary request operands. A field draw has no data operands and one nominal
field result. Local draws neither consume nor produce transcript state.

`operation` is the MLIR operation name. `attributes` lists the operation's
attribute dictionary in its sorted order as `[name, value]` pairs. Values use
the exact closed [foundation attribute grammar](foundation-interfaces.md#constructed-participants):
string, symbol-component array, Boolean, integer with signedness/width/decimal,
structured type, recursive array/dictionary, or typed invocation parameter.
There is no printed-text escape. Unsupported semantic attributes refuse.
`binding` is `[]` without an operation binding, otherwise
`[contract, arguments, implementation, inputs, outputs]` from the referenced
`runtime.binding`, with kinded arguments and structured signatures checked
against the catalogue. `operands` are references and `result-types` are logical
type trees. `regions` is empty except for loops and selected instructions.
A `protocol.loop` has a single region
`[argument-types, instructions, yielded]`: the types of its block
arguments (the induction index, the carried values, then the captured values),
its body, and the references its `protocol.yield` returns. A loop's operands are
its count, the initial carried values and the captured values, whose block
arguments denote those operands unchanged in every iteration; its `carried`
attribute counts the carried values. The captured values are the original
repeat's captures followed, for a loop that carries the transcript, by the
induction indices of its enclosing loops.

`data.branch` retains every arm in declared label order. Its operands are the
selector followed by explicit captures. Each arm is
`[argument-types, instructions, ["data.yield", yielded], label, payload-types]`.
The arm has a fresh reference frame: payload arguments, captures, then results
allocated in that arm, starting at zero. Its yields have exactly the enclosing
operation's result types. Boolean labels are `then`, `else` with no payload;
variant labels and payloads follow the selector's nominal alternatives. Both
arms must be formed even when the selector is constant. Execution evaluates
only the selected arm. The current independent Lean projection admits Boolean
arms; other selector sorts require their corresponding formal vocabulary and
are refused by that reader rather than reinterpreted as Boolean control.

Participant operations retain `data.branch` and the regionless mathematical operations of the
`algebra`, `arith`, `crypto` and `data` dialects, `protocol.receive`,
`protocol.send`, `protocol.service_query`, `protocol.guard`,
`protocol.loop`, `protocol.participant_branch` and `protocol.finish_if`.
A guard has exactly `site` and `owner` string attributes;
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
exported `exec.apply`, `exec.boolean` and `exec.variant` instructions retain their actual name
and attributes, with the data inputs and successful payload results recovered
from the checked CFG. Calls use the same data projection. The scope, outcome
packaging, continuation and stop-propagation edges are checked by native
execution admission; they are not instructions of this logical participant
carrier. A generated helper's `exec.returned` payload supplies the call's result
references. Induction lineage follows its actual operand/formal and returned
SSA value/result associations while preserving inline slot numbering. An
original helper's opaque result does not acquire lineage from an equal sort or
reference number. A participant's `protocol.finish` supplies `returned`.

Generated helper loops use the checked range-region projection below. Other
unsupported operations, successors outside the admitted helper view, or missing
references refuse with a `constructed-participant-*` diagnostic. Selected
conditional codec helpers use the admitted `exec.test` association below.
Unresolved `exec.fold`/`exec.collect` requests and storage-release steps remain
unsupported. Original source helpers remain calls.

Limits: 512 inputs and results, 64 nested blocks, 4096 inspected operations,
2048 exported instructions in total and 1 MiB of printed JSON per participant,
catalogue included. Selected control has at most 512 arms. Frame setup/copying,
operand/result positions, coordinate-alias storage/copying and actual SSA
forwarding comparisons share a cumulative
100,000-unit allowance. Instruction rows and region headers share a cumulative
1 MiB serialization allowance, charging nested instructions separately and using
empty child lists in their parents (a conservative allowance including those
empty-list delimiters). The complete envelope also satisfies the final byte
limit. Child arms and helpers never reset work, instruction, byte or frame
accounting. Exhaustion refuses with `constructed-participant-limit`.
The pair container applies these limits independently to its two children.
Readers require the exact current shapes, including an empty service interface
and the query annotation where applicable, with no compatibility reader.
The format remains `/0` under the
repository's pre-stabilization version policy.

## Selected regions

Actual candidate `protocol.participant_branch` and `data.branch` instructions
retain their names, attributes, operands and exact ordered result types. The
original source operation names are `protocol.branch` and `data.branch`,
respectively; a source descriptor is not substituted for a candidate instruction.
Operand zero is the selector and the remaining operands are ordered captures.
The `alternatives` attribute is exhaustive and in selector declaration order.
Each region is exactly:

```text
[argument-types, instructions, [terminal-operation, references],
 alternative, payload-types]
```

`alternative` is the exact label for that region; `payload-types` is that
alternative's ordered signature from the selector's full nominal type (empty
for Boolean selection). `argument-types` is exactly payload types followed by
capture types. The redundant fields must agree; they do not create authority.
All declared arms, including dormant arms, are exported and consume the same
cumulative allowances. No selector is evaluated during export.

An arm has its own zero-based reference frame: payloads first, then every
capture row, then its instruction results. It cannot read an uncaptured outer
value or a sibling arm's values. Copyable captures may refer to the same parent
while retaining distinct local positions. At the normal join the enclosing
frame is restored and only the branch's actual results are appended in order.
This changes neither straight-line references nor the existing loop triple and
its numbering. Loop-local values also cease to be visible on leaving the loop.
An actual received selector remains the result of `protocol.receive`, including
when forwarded through loop captures. A same-typed participant input is not a
substitute for that value or for its source message association.

For `protocol.participant_branch`, `terminal-operation` is `protocol.yield`;
for `data.branch`, it is `data.yield`. References must have exactly the declared
result sorts in order. A dynamically stopped or completed execution never
reaches this normal yield. The static yield remains present; an empty yield is
not a stop marker.

## Conditional completion

`protocol.finish_if` is a six-field, regionless instruction. Its operands retain
the actual Boolean condition first and then the complete participant result
tuple, including constructed state. Its `result-types` are exactly the actual
false-edge affine continuation sorts; those results enter the current frame in
the ordinary order. Its actual `site` and `owner` remain attributes. True exits
the participant through its checked completion/finalization path; false binds
the continuation results and proceeds. Completion propagates out of nested arms
and loops; it does not become a guard failure, helper yield or branch result.

## Generated mathematical computations

An admitted `exec.compute` retains its actual callee and site attributes, logical
operands and successful result sorts. Its one region contains that callee's
actual mathematical body:

```text
[argument-types, instructions, ["func.return", references]]
```

This is a closed, zero-based argument frame. Its signature equals the actual
invocation's input and output sorts. Actual argument/formal associations can
forward enclosing protocol coordinates. The body uses the same instruction
encoding and allowances as the participant. Original finite domains and callback
references remain named references to their checked source declarations;
unsupported nested control or helper forms refuse. A computation's return
restores the caller and appends its declared results. The region supplies the
actual implementation to independent readers; it does not itself prove the
computation's relation to the original oracle mathematics.

## Generated range regions

A generated `exec.range` retains its actual name and attributes. Its logical
operands are lower bound, exclusive upper bound, initial carried values, and
invariant captures. Its result sorts are exactly the carried sorts. The single
region is:

```text
[argument-types, instructions, [terminal-operation, references], conditional]
```

`conditional` is a Boolean derived from the admitted execution closure. The
closed region's zero-based arguments are the unsigned 64-bit induction value,
carried values, and captures. A normal `exec.complete` returns the carried values;
a conditional region returns a Boolean continuation decision first, followed by
the carried values. False retains the newly returned carry and ends the loop.
A helper completion returns to its range; it is not participant completion.
`exec.reject` retains the stop reason and supplies no synthetic carried tuple.
Bounds, iteration, scope exit and failure
propagation are the admitted range semantics. This carrier does not authorize
reordering iterations or erasing a stop.

Only invariant captures forward enclosing protocol-coordinate aliases into this
closed frame. The local induction value and mutable carry do not establish a new
protocol coordinate. All nested instructions, frames and bytes consume the same
export allowances as selected regions. On leaving the range, the enclosing frame
is restored and the actual carried result tuple is appended.

## Selected generated helpers

Selected generated helper steps retain their actual `exec.test` or `exec.match`
name. Their logical operands are the admitted selector followed by actual
captures; their results are the checked CFG join payload sorts. Their regions
use the same exact five-field arm record and isolated reference frames above.
Boolean arms are `then`, `else`; a match retains its nominal variant's labels
and payloads. Only `exec.match`'s administrative `successor_operand_segments`
is omitted from its attribute dictionary: the admitted execution reader has
already checked those actual CFG edges, capture forwarding and joins. Scope,
outcome and successor operands are not logical data operands.

A helper arm's terminal is `["exec.complete", references]` for a normal scoped
yield. This completes the helper region, not the participant. A rejecting arm
ends with `["exec.reject", []]`, and its instructions include the actual
`exec.reject` with its reason and site, no logical operands and no results.
Stops from any reached primitive or retained original helper propagate unchanged;
they do not produce join values or execute the suffix. Static suffix instructions
remain published even when a preceding helper always stops. Expanding a generated
helper that unconditionally rejects with a nonempty result ABI still refuses
with `constructed-participant-return`; references are never fabricated for it.

The current production transcript adapters use regionless steps and original
handler calls. Production codec conditional write/finish wrappers create
`exec.test` with `exec.complete` in both outlined arms. They do not synthesize
`exec.match` or an outlined arm terminating in `exec.reject`. A match or rejecting
arm emitted from an authored handler belongs to the original source closure and
remains behind its retained call. The generated match/reject record shapes above
do not establish production coverage for those currently unconstructed shapes.

## Boundary

Existing Lean constructed readers still refuse selected instructions and these
selected region records. Source sum types, selected evaluation, completion/stop
propagation, strict reading and actual source/candidate correspondence require
coordinated formal migration. Native export and checking do not close those
obligations. No relaxed acceptance or compatibility interpretation is defined.

Received-selector fixtures for that migration must retain the actual original
source, its authored target/acceptance and selected construction, the typed
service contracts and both checked participants. Native acceptance of those
artifacts supplies neither a source execution theorem nor the service laws
required by a formal consumer; those premises require independent source-owned
connections.

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
applications, restrictions, repeat captures and selected captures to its original
root, and checks exact owner, request, nominal result and static/dynamic occurrence.
Only the installed field `draw` is admitted. Unsupported methods refuse.
The existing validator construction rule continues to refuse local requests.

### Formal checkpoint frames for closed Math arms

A Math arm indexes only its explicit capture frame. The independent formal
execution retains the immutable caller frame as a prefix of each checkpoint
emitted while that arm executes. Nested closed frames add their parents in
lexical order. This prefix is diagnostic state, not an additional operand scope.
Successful results extend the caller frame using the declared yield row; a stop
retains the checkpoint reached before the failure. Both arms remain statically
admitted even though only the selected arm executes.
