# Executable programs

This profile is the executable output of
[closed mathematical protocols](mathematical-protocols.md). It uses the local
control, binding, representation and affine-custody contracts of the existing
participant machine, together with [service ports](native-services.md).
The single current format, `zkc.program/0`, includes Boolean literals,
[structured values and iteration](structured-iteration.md), and
[structured message admission](structured-proof-messages.md).
[Joint execution](run.md) supplies a bounded synchronous
host policy over these participants. Source correspondence, network transport
and security certificates remain separate.

## IR stages and interchange

The four profiles `protocol`, `participant`, `exec` and `physical`, with their
mandatory formation checks, select the IR semantics. Flat bodies, loops,
copyable aggregates, empty arrays and dynamic messages share one executable
contract. Physical selection produces the `physical` profile; no separate
execution-contract property selects a second interpretation.

The external tag is `zkc.program/0`, with the five-field root
`[tag, bindings, functions, participants, entries]`. Each participant has exactly
eight fields:

```text
["participant", name, instance, role, arguments, results, body, services]
```

`arguments` contains the actual ordered `[name, physical_type]` ports. Function
records retain their logical-origin definition and argument assignments. The
`services` field contains `[name, contract, input_index]` rows, including an empty
list for participants without services. Indices are canonical nonnegative
decimal strings. Entry maps and instruction records retain their positional
shapes.

Only physical programs have an interchange encoding. A compiler may
reconstruct a logical execution model internally to validate and select
representations. That internal check is not public serialization admission:
`program::checkStructure`, program JSON decoding and JSON export refuse a
logical program root. Public checked export runs full MLIR verification, including
projection metadata and native type policy, before reconstructing the model.

Only the exact `zkc.program/0` tag and specified record shapes are admitted.
Unknown tags and wrong record arities refuse independently. See the
[public interface overview](../../../status.md#current-public-interfaces).

## Local domain binding

Local operation domain bytes are the compact UTF-8 JSON encoding of:

```text
["zkc.local-domain/0", origin, role, local_call_site_or_null,
 [logical_definition, logical_arguments], operation_site,
 [operation_contract, operation_arguments], attributes]
```

Logical argument assignments, operation arguments, attributes and the complete
execution origin remain meaningful inputs. Physical implementation names are
absent. This backend extension helper encodes admitted execution state; it does
not issue resources or authorize a transition. Installed native kernels currently
do not consume it. It has no external input reader and is separate from the
native proof invocation binding.

## Data boundaries

The program contract admits copyable variants at participant ports, recursively
checking all payloads; affine variants remain local. Common and participant IR
use the same type policy. One-owner RNG and
resource ports remain admitted. Port permission implies neither a codec nor an
installed representation. Programs admit variant messages under the complete closed grammar in
[structured messages](structured-proof-messages.md). They retain the
participant machine's control and custody rules.

## Boolean literal

The Boolean literal instruction is:

```json
["bool_constant", "site", "output", true]
```

The record has exactly four fields. Its value is a JSON Boolean, never a string,
number, null or aggregate. It defines one fresh `bool@native.bool/0` value in a
local function body, including an admitted nested local control region. It is
not a participant-level instruction. Ordinary local site, identifier, SSA,
control, return-type and resource checks apply. Program identifiers are bounded
to 128 bytes. Missing, duplicate or malformed sites and duplicate outputs fail
admission, including in retained unused functions and dormant branches.

The logical MLIR operation is `local.bool_constant`; its physical form is
`plan.bool_constant` with exactly the selected native Boolean representation.
These operations have no `Pure`, `ConstantLike` or speculative-execution grant.
Their placement and accounting belong to executable local semantics. Total
`arith.constant` remains a different operation before lowering.

A literal has no input, installed kernel binding, randomness or service effect.
It consumes one ordinary local instruction step. Calls, control and returns
retain their own accounting. The runner constructs a Boolean through the trusted
`Value::from_control_bool` adapter, checks its physical type and backend value
contract, and applies ordinary retained-value and byte limits. A literal failure
reports that instruction's site. Completed prefixes remain completed; failure
and cleanup obey the local machine's existing stop and custody rules. Terminal
values remain retained for stable repeated polling.

`Backend::supports_boolean_literals` is a stable installation fact, false by
default. Admission checks it when any retained local body contains a literal;
runner initialization checks it again before installing entry frames. This
query must not execute work or construct a sample value. A backend advertising
support must implement the constructor consistently. The runner still validates
the constructed value; a dishonest or failing adapter causes a backend stop,
not an unchecked value entering the environment. Literal support is reported
separately from installed bound-kernel roles.

## Closed participant behavior

Programs admit compact value-count loops and nested service queries. They refuse
composition calls, parameters and family selectors, recursively inside loop
bodies. Participant programs contain ordered local invocations, typed sends
and receives, declared service queries, and a final return. Direct participant
`stop` and `incomplete` records are refused; stopping work belongs to a local call.
Closed local bodies retain their existing admitted conditional, loop, variant,
bound-kernel, release and explicit-stop grammar. Installed bound-kernel contracts
remain extensible through their existing admission and backend obligations. Closed native types do not grant new total
mathematical operations. Total mathematical operations and managed service
queries do not execute inside those bodies.

The native type-use policy also applies to `exec` and `physical` MLIR. Physical
wrappers are checked independently and their logical components must satisfy
the same policy. A type's presence in an installed catalog is insufficient to
extend the native profile. The [structured profile](structured-mathematics.md#native-array-boundary)
adds native wire permission for complete static BLS field-array types,
under its own complete-type codec contract. Other nonserializable private data and
affine capabilities cannot cross a message edge. Copies of capability handles do not copy authority.

A generated guard branches locally: true yields; false stops with explicit
reason `reject` at the source guard site. The existing `control.require` kernel
retains its distinct backend failure behavior. No local stop broadcasts a peer
stop or rolls back earlier sends, draws or consumed resources.

Runtime stops retain the role, origin, site, primary cause and ordered cleanup
errors. Optional local context identifies the enclosing call and function plus
an inner instruction when recorded. A matching local and participant site name
therefore does not conflate their namespaces. This diagnostic adds no protocol
or transcript event. Iteration-budget exhaustion reports the attempted next
iteration and loop site before body entry; instruction exhaustion at a yield
reports the iteration whose yield was attempted. Earlier effects remain installed.

## Consumers and assurance boundary

The Rust runner admits supplied physical programs through
`admit_supplied`; the native backend supplies Boolean construction and the
existing kernels/codecs. Structural admission does not establish correspondence
to a mathematical source. A generic role runner can expose a message to a named
external peer; its host must authorize the peer roster and route/envelope. Joint
bundle and proof admission enforce their own closed roster policies.
The [proof host](native-proofs.md) and joint host consume
this same program format with distinct Host responsibilities. The single proof
policy independently constrains actual messages, loops, keys and transcript
transitions; the program format alone grants no proof authority.
Independent Lean participant models do not interpret this format. Native checking
support requires its own interpretation and correspondence evidence.

## Conditional completion extension

The native mathematical path also supports [conditional entry completion and
bounded local termination](entry-completion.md). Its records belong to this executable contract; independent formal models
require their own explicit interpretation.
