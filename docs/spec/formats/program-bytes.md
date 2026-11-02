# Program byte language

This page defines the record grammar of `zkc.program/0` for independent readers.
The [program contract](program.md) supplies admission and execution rules. This
is the physical executable carrier; it is neither MLIR bytecode nor the
[structured source export](structured-source.md). Its
[logical oracle vocabulary](structured-source.md#logical-oracle-vocabulary)
belongs before semantic realization. Logical anchors, virtual definitions and
oracle sequences must lower away before physical participant serialization;
recognizing a source oracle type grants no executable codec. The realization
record must determine the generated program for a separate correspondence
check.

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
["loop", site, Count, list(Carried), list(Capture),
 ParticipantBody, list(output)]
["return_if", site, condition, list(value), list(continuation)]
["if", site, condition, list(Capture), ParticipantBody, ParticipantBody, list(output)]
["match", site, input, list(Capture), list(ParticipantArm), list(output)]
["yield", list(value)]
["return", list(value)]

Count = ["value", count_value, maximum, induction]
ParticipantArm = [alternative, list(payload_binding), ParticipantBody]
```

`count_value`, `induction` and every continuation are value names. `maximum` is
a canonical natural at most 1,048,576. The actual count remains an input value,
checked against that maximum; the maximum is not the trip count. `Carried` has
the same ordered binding/incoming-value shape as above. The
[completion contract](../ir/completion.md) defines `return_if`, including the
continuations retained on its nonreturning path. Only affine returned values
have continuation bindings; ordinary copyable results do not.

Local and participant instruction alternatives are distinct even when they
share `yield` or `return` shapes. Participant bodies cannot contain `op`,
Boolean literals, `for`, `release` or direct `stop`. Local bodies
cannot contain `send`, `receive`, `query`, `loop` or `return_if`. Composition,
parameter and family-selector records are absent from both closed grammars.

Participant `if` and `match` use the exhaustive alternative, active payload and
typed join rules of Local control, with the explicit capture bindings below.
Every arm must admit under participant permissions. Only the selected arm creates a frame, executes actions,
charges execution work or yields. Immutable service roots remain participant
interface metadata and cannot be manufactured, returned or selected as data.
An explicit participant branch occurrence uses `["branch", site, alternative]`
in the runtime origin, distinct from Local control and loop iteration frames.
Generic Program admission establishes no source common-input provenance. The
[joint Host](../runtime/joint.md) compares reached selectors before arm work;
independent execution establishes no agreement with peers.
Every participant control record (`loop`, `if` and `match`) binds its captures
explicitly:

```text
Capture := [local_name, parent_name]
```

Each local name is a distinct formal of the loop body or of every arm, disjoint
from the induction, carried formals and arm payload bindings. Parent names
resolve in the enclosing environment and may repeat only for Copy types. Every
row retains one formal and its owned-storage charge; two aliases are not
deduplicated. A body uses the local name. Capture order remains significant.
Expanding protocol applications into participant bodies can make two formals
share one parent, so the binding cannot be recovered from parent names.

A participant `loop` body and every arm of a participant `if` or `match` is a
nested lexical environment. Its visible names are its formals (the loop
induction, carried formals and capture locals, or the arm's payload bindings and
capture locals) and the participant's service ports. Nothing else from the
enclosing body is visible; there is no ambient capture. A body's bindings are
not visible after it, and a body may bind a name that is also bound outside it,
including in a sibling body. Within one body every formal and binding is
distinct, and none equals a service port name. Discarding a body's environment
discards only value names: sites, message schemas and service ports stay unique
or consistent across the whole participant, as they are for the participant's
own body.

Local structured instructions keep their name lists. Scoped local regions
canonicalize aliased captures before emission, so a local capture list is
exact. `if` and `match` therefore have different capture fields in the two
body grammars; a reader decodes them by body kind and never guesses the shape.

The version remains `zkc.program/0`. Producers, independent readers and fixtures
change together. A participant string capture list is refused; there is no
compatibility decoder. Empty capture lists remain empty.

## Bounds and admission

Every bound is inclusive: a quantity equal to its bound is admitted, and one
more is refused with the `capacity` class. Static admission counts every
definition, including unused ones, every arm, including unselected ones, and
zero-trip bodies.

| Measure | What is counted | Scope | Bound |
| --- | --- | --- | --- |
| Raw bytes | UTF-8 input bytes, including whitespace | Input | 4 MiB |
| Compact encoding | Bytes of the compact encoding a producer writes | Program | 4 MiB |
| JSON nodes | Arrays, strings and Boolean literals | Input | 400,000 |
| JSON nesting | Arrays on one path; the root array is level 1 | Input | 64 |
| Array elements | Elements of one array | Each array | 32,768 |
| String bytes | Decoded bytes of a string other than an operation attribute, including type spellings, contract identities and static arguments | Each string | 4,096 |
| Attribute bytes | Decoded bytes of one operation attribute | Each attribute | 16,384 |
| Identifier bytes | Bytes of a name or site | Each identifier | 128 |
| Operation bindings | Binding declarations | Program | 4,096 |
| Binding arguments | Static arguments; separately, physical arguments | Each binding | 128 |
| Origin assignments | Assignment rows | Each function origin | 128 |
| Definitions | Functions plus participants | Program, combined | 4,096 |
| Entries | Entry records | Program | 4,096 |
| Lists | Entries of one name or row list, listed below | Each list | 1,024 |
| Participant interface | Inputs plus service ports | Each participant | 1,024 |
| Operation attributes | Attributes | Each `op` | 16,384 |
| Static instructions | Instruction records of every body | Program | 65,536 |
| Body nesting | Bodies below a definition body, which is level 0 | Each definition | 64 |
| Match arms | Arms | Each `match` | 64 |
| Loop maximum | The static `maximum` | Each `loop` | 1,048,576 |
| Descriptor charge | Units of the charge below | Program, cumulative | 64 Mi (67,108,864) |

The list bound applies to ports, results and service ports; capture lists and
capture rows; carried rows; outputs; the inputs and outputs of `op`, `local` and
`query`; `variant` payload values and `match` payload bindings; `release`,
`yield` and `return` values; `return_if` values and continuations; and entry
role maps. A `for_while` yield lists its condition before the carried values and
counts it, so a `for_while` carries at most 1,023 values.

A reader counts a list, array or string before it decodes or allocates the
counted elements, and counts JSON nodes and nesting before it allocates any JSON
value. A producer checks the same bounds before it emits a program. The measures
stay distinct: raw bytes, compact producer output, JSON nesting, body nesting,
descriptor charge and execution work each have their own bound, and none stands
in for another. JSON nesting counts the record and list arrays, not just control
constructs, so for serialized input it binds before body nesting: the 64 body
levels do not authorize 64 nested `if` records. Body nesting also bounds programs
that a producer builds directly.

A `match` has one arm per alternative of a variant whose type the program spells
in a 4,096-byte type string, which bounds it at 64 arms. A longer arm list
refuses with `local-match-shape` or `interactive-match-shape`. MLIR
[formation](../ir/variants.md#type-and-value) admits wider variants; they have no
Program `match`. A type spelling is admitted by its own type language, whose
structural limits are type formation, not carrier bounds. Message, entry and
runtime resource limits apply through their owning contracts; this table does
not raise a runtime execution allowance.

### Descriptor charge

The descriptor charge accounts for the type metadata a reader retains. Each
distinct physical type spelling of a port, a result, a `receive` type or a
`variant` type is charged once. Every resolved signature input and output of
every binding, including bindings that no instruction uses, and every declared
physical argument is charged separately. A reader charges a type before it
retains its descriptor. The charge of a type, in units, is the sum of:

- for a variant: 512, plus 4 per byte of its canonical logical spelling
  (`variant:` and the hexadecimal descriptor), plus 256 per alternative, plus 256
  per payload entry, plus the charge of every payload type;
- for a structural application `constructor<...>`: 512, plus 256 per argument,
  plus the charge of every type argument;
- for a resource unit: 256;
- for an aggregate physical layout (a sequence, field array, fixed vector or
  variant): 256, plus 88 per stored child, plus each child's charge.

Every other type charges 0. A nested type is charged at every occurrence,
including inactive alternatives, even where a reader shares its storage. A reader
may also bound the work of parsing one spelling, as part of type formation.

Decoding, static admission, installation and invocation are separate steps.
Static admission resolves types and bindings, validates SSA and control,
checks effects and affine custody, and checks the complete retained closure.
Installation checks available implementations; execution applies reached
resource and value checks. No JSON record supplies an installation grant,
source correspondence theorem or cryptographic security claim.

## Refusal classes

An independent reader reports every refusal in one of these classes. Diagnostic
codes and prose remain reader-specific. A program with several violations may be
refused in the class of any of them; conformance cases isolate one violation.

| Class | Refusal |
| --- | --- |
| `syntax` | The input is not one value of this grammar: invalid JSON or UTF-8, trailing input, a value other than an array, string or Boolean literal, an unknown tag, a wrong arity, an instruction of the other body grammar, a malformed identifier or natural, an unknown stop reason, an empty body, `release` or entry role map, a body that does not end at its sole terminator, a `return` or `yield` in the wrong body, or a program with neither entries nor a function-only root. |
| `capacity` | A quantity exceeds its bound in the table above. |
| `names-and-ssa` | A name does not resolve or is not unique: duplicate declarations, symbols, origin parameters, roles, instance and role bodies, sites, formals or bindings in one environment; unresolved bindings, functions, participants, service ports or methods; an operand not visible in the current environment; a name equal to a service port; an entry whose role names another participant's role or that selects different instances; or a message addressed to the sender's own role. |
| `types` | Types or arities disagree: an unadmitted type spelling, operand, result, yield or return types or counts, a selector type, a join, variant alternatives and payloads, arms that do not list every alternative in order, message wire eligibility or schema consistency, a port permission, an origin static identity, or operation attributes outside their contract's parameter rule. |
| `affine-use` | A value is used beyond its custody: a consumed value used again, an affine value captured where only copyable values may be captured, or a value that cannot be dropped released. |
| `unsupported-profile` | A well-formed program outside the admitted profile: a binding that does not select an installed contract application, an uninstalled service contract, or a history-observing operation inside a local `match`. |

Runtime failures and source stops are not admission refusals.

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

The shared [byte fixtures](../../../common/tests/fixtures/program/bytes.json)
provide exact UTF-8 inputs, with repeat segments for large ones, and the expected
normalized result of static admission: the static instruction count and
descriptor charge of an admitted program, or the class of a refusal. Both the
compiler codec test and Rust reader consume this same corpus. It includes
alternate JSON whitespace/escapes, explicit stops, local and participant loops,
conditional completion, malformed or unresolved records in dormant work, a case
at every bound of the table and one past it, each reaching its own bound first,
and lexical cases for sibling and nested participant bodies, duplicates within
one body, untaken arms and zero-trip loops.
An independent formal reader can consume these fixtures without invoking the
compiler. Their agreement is bounded evidence, not a proof of either reader.
