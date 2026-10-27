# Program byte language

This page defines the record grammar of `zkc.program/0` for independent readers.
The [program contract](program.md) supplies admission and execution rules. This
is the physical executable carrier; it is neither MLIR bytecode nor the
[structured source export](structured-source.md).

## Bytes and primitive values

The input is one UTF-8 JSON value with no trailing non-whitespace data. Only
arrays, strings and Boolean literals occur. Objects, JSON numbers and `null`
have no production. JSON whitespace and valid alternate string escapes are
accepted; invalid UTF-8 and unpaired surrogate escapes are refused. Booleans
occur only in the Boolean-literal instruction. Empty arrays are significant
fields, not omitted defaults.

All records below have exactly the displayed number of fields. A reader must
reject unknown tags, wrong arities and values of the wrong JSON kind. It must
then apply admission, including to unused definitions and dormant branches.
Recognizing these record shapes alone does not admit a program.

In the grammar, `list(X)` means an ordered JSON array of zero or more `X`
values. Names and sites are strings matching `[A-Za-z_][A-Za-z0-9_.-]*`, with
at most 128 ASCII bytes. A natural is a string matching `0|[1-9][0-9]*`, within
the field's bound; signs, leading zeros and numeric JSON tokens are refused.
Types are complete canonical physical type spellings admitted by the trusted
contract context, including all ordered children and variant alternatives.
See [representations](../realization/representations.md). Contract identities,
static arguments and operation attributes use their owning contract's string
grammar, not necessarily the identifier grammar.

The compiler writes compact JSON, preserving record and list order. This does
not make every admitted byte string a unique encoding: whitespace and JSON
escapes can differ. A consumer must use the identity construction specified by
its enclosing artifact, rather than substituting a hash of reprinted JSON.
The [proof format](proof.md) separately defines source, descriptor, candidate
and invocation binding. This grammar adds no new digest or authority.

## Declarations

```text
Program = ["zkc.program/0", list(Binding), list(Function),
           list(Participant), list(Entry)]
Binding = [name, contract, list(static_argument), implementation,
           list(physical_type)]
Port = [name, physical_type]
Origin = [logical_definition, list([parameter_name, static_argument])]
Function = ["function", name, list(Port), list(physical_type), LocalBody, Origin]
Service = [name, service_contract, input_index]
Participant = ["participant", name, instance, role, list(Port),
               list(physical_type), ParticipantBody, list(Service)]
Entry = ["entry", name, list([role, participant_name])]
```

The origin is mandatory on every serialized function. It is not `null` and
cannot be omitted even when its assignment list is empty. An internal compiler
model with an unresolved origin is not a different public record shape.
Results are ordered type strings, while inputs are ordered named ports.
`input_index` is a canonical natural identifying an actual participant input.
Entry role maps are nonempty and reference declared participants. Duplicate
declarations, parameters, roles and service names are checked in their owning
namespaces; a decoder must not silently overwrite them.

Bindings select installed logical contracts and physical implementations;
their declarations cannot register a new implementation or grant a codec.
Definition order does not replace symbol resolution. Port, result, argument,
capture, carried-value and instruction order is meaningful and must be kept.

An executable has either participants and nonempty entries, or at least one
function with empty participant and entry lists. An entirely empty program is
invalid. The [program contract](program.md#ir-stages-and-interchange) defines
function-only root selection.

## Local function bodies

`LocalBody = list(LocalInstruction)`. The complete instruction alternatives are:

```text
["op", site, binding_name, list(attribute), list(input), list(output)]
["bool_constant", site, output, boolean]
["variant", site, physical_type, alternative, list(payload), output]
["match", site, input, list(capture), list(MatchArm), list(output)]
["if", site, condition, list(capture), LocalBody, LocalBody, list(output)]
["for", site, induction, lower, upper, list(Carried), list(capture),
 LocalBody, list(output)]
["for_while", site, induction, lower, upper, list(Carried), list(capture),
 LocalBody, list(output)]
["release", list(value)]
["yield", list(value)]
["return", list(value)]
["stop", site, reason]

MatchArm = [alternative, list(payload_binding), LocalBody]
Carried = [region_binding, incoming_value]
```

All value fields are SSA names. In particular, `lower` and `upper` name values;
they are not decimal bounds or inclusive/exclusive flags. `if` lists the true
body before the false body. Match payload names are bindings in that arm, not
pre-existing values. Captures and carried values explicitly establish nested
environments; a reader must not infer captures from names in the body.

`release`, `yield` and `return` have **no site field**. `reason` is one of
`reject`, `abort`, `exhausted`, `incomplete` or `refused`. A source stop is an
explicit stopped outcome, not a successful return. The control, custody,
zero-trip and `for_while` yield rules are in
[structured iteration](../ir/iteration.md) and the [VM contract](../runtime/vm.md).

There is no serialized local-to-local call instruction. Compiler-local
mathematical application records, source helpers and scoped region functions
must be resolved before this carrier is emitted. An `op` may have a callback
under its admitted contract; that does not introduce another instruction tag.

## Participant bodies

`ParticipantBody = list(ParticipantInstruction)`, with these alternatives:

```text
["local", site, function_name, list(input), list(output)]
["send", site, schema, peer, input]
["receive", site, schema, peer, output, physical_type]
["query", site, service_name, method, list(input), list(output)]
["loop", site, Count, list(Carried), list(capture),
 ParticipantBody, list(output)]
["return_if", site, condition, list(value), list(continuation)]
["yield", list(value)]
["return", list(value)]

Count = ["value", count_value, maximum, induction]
```

`count_value`, `induction` and every continuation are value names. `maximum` is
a canonical natural at most 1,048,576. The actual count remains an input value,
checked against that maximum; the maximum is not the trip count. `Carried` has
the same ordered binding/incoming-value shape as above. The
[completion contract](../ir/completion.md) defines `return_if`, including the
continuations retained on its nonreturning path.

Local and participant instruction alternatives are distinct even when they
share `yield` or `return` shapes. Participant bodies cannot contain `op`,
Boolean literals, `if`, `for`, `match`, `release` or direct `stop`. Local bodies
cannot contain `send`, `receive`, `query`, `loop` or `return_if`. Composition,
parameter and family-selector records are absent from both closed grammars.

## Bounds and admission

The carrier bounds apply cumulatively, including unused definitions, all arms
and zero-trip bodies. In particular:

| Quantity | Bound |
| --- | --- |
| Raw bytes and compact program encoding | 4 MiB each |
| JSON nodes, counting arrays, strings and Booleans | 400,000 |
| Elements of any array | 32,768 |
| JSON array nesting | 64 |
| Functions and participants combined | 4,096 |
| Operation bindings | 4,096 |
| Ports, captures and carried/output name lists | 1,024 |
| Operation attributes | 16,384 |
| Static instructions across all definitions and nested bodies | 65,536 |
| Match alternatives | 32 |

JSON nesting counts the record and list arrays, not just control constructs.
Consequently the 64-level body bound does not authorize 64 nested `if` records.
Type spelling, descriptor-work, static-argument, message, entry and runtime
resource limits also apply through their owning contracts. This table does not
replace those checks or raise a runtime execution allowance.

Decoding, static admission, installation and invocation are separate steps.
Static admission resolves types and bindings, validates SSA and control,
checks effects and affine custody, and checks the complete retained closure.
Installation checks available implementations; execution applies reached
resource and value checks. No JSON record supplies an installation grant,
source correspondence theorem or cryptographic security claim.

## Independent readers

The native implementations are
[`Program/Decode.cpp`](../../../compiler/lib/Program/Decode.cpp) together with
[`Program/Admission.cpp`](../../../compiler/lib/Program/Admission.cpp), and
[`vm/decode.rs`](../../../crates/zkc-runtime/src/vm/decode.rs) together with the
Rust model checks. The compiler producer is
[`Program/Encode.cpp`](../../../compiler/lib/Program/Encode.cpp).

A formal reader should separate byte parsing, these exact record shapes,
typed admission and its denotation. A successful parser establishes only
the layer it checks. Independent format controls should include missing origins,
wrong arities, misplaced instruction tags, noncanonical naturals, duplicate
declarations, malformed strings, extra trailing input, unknown bindings and
mutations in dormant bodies. Existing native boundary tests exercise these
classes; agreement does not prove a source-to-execution theorem.
