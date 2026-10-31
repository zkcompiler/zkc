# Proof deployment and transport

This is a native contract. [Construction](../ir/construction.md),
[transport](proof.md), [execution](../runtime/proofs.md)
and [attempts](../runtime/attempts.md) define separate boundaries.
[Proof usage](../../runtime/proofs.md) explains their application.

## Program, construction and deployment

A proof deployment consists of:

- The immutable source, selected entry and original role/input/result interface.
- A construction selection: `authored`, or a named challenge derivation with
  explicit source draw/delivery selectors, public bindings and transcript suite.
- The actual participant candidate and its source-to-candidate correspondence.
- Selected logical message codecs, physical bindings and resource policies.
- Producer/validator entry maps and the validator's Boolean acceptance result.

`authored` preserves the source's explicit transcript and proof algorithm. It
inserts no challenge derivation. A protocol such as Groth16 can therefore use
proof deployment without a Fiat–Shamir transformation.

A challenge construction replaces a selected source experiment. It is distinct
from role projection, local execution refinement and cryptographic property
transport. Its structural correspondence does not establish soundness, zero
knowledge, independent randomness or honest delivery.

The compiler retains the admitted common mathematical source, derives challenge
dependencies and ordered occurrences from it, projects without simplification,
and constructs the participant mathematical candidate before math lowering.
There is one mutable candidate. Derived occurrence/dependency information is
revision-bound checking data, not another editable program.

The original projection interface remains immutable. Constructed participants
have a separate checked interface map: each actual input maps to an original
role/port, an explicitly bound public port, or a generated transcript; each
result maps to an original role/result or a generated transcript successor.
Removed service ports have no candidate ingress position. Original action
records remain source facts; a construction map identifies retained, replaced
and inserted candidate occurrences. The selected native extension stores a
checked construction section alongside the original interface in
`protocol.projection`. It does not overwrite source facts to make a changed
signature appear to be ordinary projection.

Formation checks both interfaces and their type/role/index relationships against
the actual candidate. Construction checking separately establishes the mapping
from the retained source and policy. Lowering and physical selection preserve
both interfaces/maps, extending only their permitted realization metadata.
Unconstructed programs keep the ordinary projection rules; an unchecked mapping
cannot waive those rules.

The source and candidate are different mathematical subjects. The candidate's
actual per-role operands, received values, guards and state transitions remain
available for analysis. Original selected entropy draws remain identifiable in
the source; a mapping to a candidate transcript challenge does not turn that
challenge into an independent random draw.

## Authorized public context

Public bindings are an explicit author/application-supplied deployment policy.
The compiler does not automatically publish all verifier inputs. Missing
bindings refuse the profile. Public bindings name exact original role/port
pairs, their nominal types and canonical values. Every validator data input is
bound, including unused inputs and inputs used only by checks. Application
context, relation identity, verifier key material and selected configuration are
also bound where present. A key fingerprint is checked against the application's
expected key, not against a key chosen by the proof. Duplicate bindings at an
invocation must agree.

The profile adds no participant data inputs. Its producer host takes
labelled `(role, port)` public values and uses them in the initial transcript
root. The generated participant data-input map is empty; only the internal
transcript input/result is added. For a port shared by producer and validator,
the producer host binds its actual input component or checks that component
against the supplied public binding before execution. Validator ingress is
checked against the same binding policy. Later public computation recipes may
need additional participant data inputs through an explicit checked map. A
construction cannot obtain a validator-private value by relabelling it public. A
witness-dependent verifier input must either be deliberately published and
bound, be fixed by a separately specified commitment protocol, or make this
deployment inapplicable. The profile refuses a relation operand with
purpose `witness` when its original input port is available to the validator,
even if the statement selects the producer component. This includes shared
witness ports and the current composed R1CS assignment. Admitting a deliberately public assignment or committed replacement
requires a separate selected extension. Absence of that purpose is not a secrecy
proof; the explicit public-input authorization remains necessary.

For every retained relation statement in this two-role deployment, its original
acceptance result must equal the policy's selected acceptance result. A different
result refuses with `native-proof-statement-acceptance`; an unrelated constant
Boolean cannot stand in for the relation's designated decision. Every operand
with purpose `parameter` or `statement` must be available to the validator and
therefore covered by the exact public bindings, or admission refuses with
`native-proof-statement-public-input`. Selecting the producer component of a
shared port is admitted because invocation admission checks it against the same
public value. These restrictions belong to this deployment profile, not general
mathematical formation. Multiple relation statements can share its selected
result; a deployment selecting another aggregation needs an explicit extension.

These checks run against the source before construction. Retained metadata is
also checked against the actual candidate by source-relative correspondence.
The executable carrier does not acquire a second relation-schema language: the
source digest authenticates declaration identity and purposes, while its port
maps and canonical public values bind the actual invocation. An application
must pin the deployment and authorize configuration values independently.
No satisfaction, setup law or secrecy claim follows from declaration admission. Sending a witness as an explicit
message remains distinct from supplying it as a validator entry input.

The two invocation hosts bind their own actual inputs. Cross-role equality is
not established by availability. The proof carries a checked digest of its
binding; validation compares it with the independently supplied expected
binding. This comparison does not authorize the context or prove a hash law. For
authored protocols without a context-binding transcript or relation, the header
supplies a consistency check only: an attacker can rewrap proof bytes.
Cryptographic binding to application context must come from the authored
protocol or a separately justified construction.

Program identity, candidate identity and invocation binding have different uses:

| Identity | Meaning |
|---|---|
| Program | Immutable source plus selected entry, construction, origin policy, logical codecs and logical contract identities |
| Candidate | Exact participant/physical output plus implementation selections and checked compilation settings |
| Invocation | Program identity plus canonical actual public values, application context, relation/key/configuration bindings |

Candidate checking binds the actual source, policy and emitted candidate.
Generated helper names, process/session identifiers, backend addresses and
physical implementation names do not become cryptographic occurrence labels. The
native policy identifies the exact source bytes; it does not promise
identity under source reformatting. This profile provides no normalized
source identity policy.

## Proof transport and admission

Proof transport implements participant sends and receives. It does not evaluate
protocol equations or choose challenges. Message types, occurrences, peer roles
and decoding policies come from the admitted deployment. A candidate proof
cannot choose a different program, codec or verifier configuration.

The framed proof starts with the eight bytes `ZKCPRF00`, followed by the 32-byte
SHA-256 digest of the canonical invocation binding. Each expected message is a
u64 little-endian payload length followed by that payload. Expected type and
occurrence come from the admitted deployment. The header is checked context, not
authority to choose configuration. Expected context is supplied independently.

The proof ceiling is 16 MiB, including header and message lengths; a Host may
lower it. Length arithmetic and payload bounds are checked before allocation or
consumption. Reading a length remains a consumed prefix if its payload is
truncated; a later decode failure likewise retains consumed message bytes.
Validation requires complete proof consumption, so trailing bytes refuse.
Transport does not absorb transcript data a second time: explicit program
operations perform observations.

The internal profile admits canonical-only codecs: successful decoding satisfies
`encode(decode(bytes)) = bytes` for the exact admitted type/domain/shape. Transcript
observations use that canonical value encoding. This permits the producer to
encode its value and the validator to encode the value it actually received
without a second retained byte representation. A codec that accepts multiple
representations or an external transcript that observes original bytes must
preserve those bytes under an explicit different contract.

Bounds on proof length, each frame, decoded depth/count/shape, integer
conversion, retained values, work and resource transitions are checked before
the relevant allocation or consumption. Decode invalidity, limit refusal and
backend failure remain distinct outcomes. Unknown tags, domains and
codecs refuse. A wrong header/context binding is a profile refusal, distinct
from a verifier Boolean false result and from malformed payload decoding.
Capabilities and service references never cross the wire.

The native proof driver advances one admitted runner through its local actions,
queries and structured control. Producer sends append proof payloads; validator
receives consume proof payloads. A reverse communication action that remains
after construction is inadmissible for this two-role deployment. The
mathematical IR continues to support other role rosters and interactive
deployments.

Validator external inputs are public data/configuration. Host-created transcript
state is an internal invocation resource. The proof deployment envelope
exports the checked constructed input/result/resource maps and binds them to the
exact participant artifact. Rust proof admission checks their indices, types,
roles, suites and creation/disposal policies against that artifact. The native
participant instruction grammar need not contain these maps; generic supplied
carrier admission alone does not establish source correspondence. Original
source service-port and draw-selector references are checked by the compiler;
the host checks the constructed maps and event order in the pinned deployment.
An affine external transcript value or unmapped resource input refuses. Copyable
external construction state uses the ordinary proof data-input contract and
[authored transition rules](../realization/external-constructions.md#authored-native-deployment).
Authored execution
has no generated transcripts and refuses authored validator transcript inputs.
Other validator resources require a separate explicit policy; a witness or
ambient oracle cannot enter through this exception.

## Deployment policy and descriptor

The compiler's policy is an exact array (JSON spelling carries no identity):

```text
["zkc.native-proof-policy/0", entry, producer, validator, acceptance,
 suite, services, public_inputs, [[query_site, delivery_site], ...], format,
 construction, [[query_site, difficulty], ...]]
```

`construction` is empty for the installed native or authored path. Otherwise it
names the exact `protocol.construction` symbol in the original module. Its
target, provider suite and replacement authority must match this policy.

Indices are canonical decimal strings less than 1024. Public input indices are
strictly increasing and enumerate every validator data input, including unused
inputs. All are explicitly authorized for public invocation binding. `services`
is a strictly increasing array of original validator service input indices.
With no construction selector, an empty suite, service set and draw list select
authored execution; native selection requires a supported suite, one selected
service and 1–64 draws. A programmable selection requires a nonempty service set
and permits 0–64 draws. Local factories use an empty suite. A managed root
absorbs the canonical invocation at issuance; this does not establish that
custom handlers use it correctly. Each draw pair selects a `draw`, `index` or `indices`
query on one selected authority, preserving that query's actual contract.
The final array selects gated `indices` occurrences. Its sites are unique,
must occur in the selected draw list, and have canonical decimal difficulty
from 0 through 64. An absent site uses the ungated block equation; an explicit
zero still carries a zero witness. Scalar queries, unknown sites and custom
handlers cannot acquire gates through this array. The
[index-block contract](native-index-block.md) defines the exact request,
witness and failure behavior. This required field is empty for other policies.
Selectors use prepared static occurrence sites; native labels retain original
authored paths. No timing or security premise follows from this policy.

`format` is `zkc.framed/0` or `raw.bytes/0`. Native framing uses the header and
message frames below. Raw Bytes uses no header, length prefix or implicit
observation. Without a programmable record codec, its admitted authored program
has exactly one nonrepeated `bytes` message from producer to validator. One receive consumes the entire bounded
input, including an empty byte string; the authored parser owns record decoding
and inner EOF. Returning without that receive, or sending no message, refuses.
A programmable [record codec](../ir/construction.md#record-transport) instead
uses one internal verifier Bytes input and one internal prover Bytes result,
with no executable Send or Receive. Its ordinary functions own record parsing,
encoding and EOF. The application authenticates the deployment independently.
Raw bytes carry no framing-level statement or context binding; a managed root
still absorbs the canonical invocation, while local state owns its binding
algorithm.

The immutable compiler descriptor is:

```text
["zkc.native-proof-descriptor/0", policy, "zkc.native-origin/0",
 [event, ...],
 [[validator, original_port, logical_type, codec], ...],
 [[message_origin_hex, logical_type, codec], ...], construction_plan,
 [[query_origin_hex, witness_site, "index", "native.index/0"], ...]]
event = ["query", origin_hex] | ["index", origin_hex, bound] | ["message", origin_hex]
      | ["indices", origin_hex, bound, count]
      | ["gated-indices", origin_hex, bound, count, difficulty]
      | ["start", origin_hex, [logical_input_type, ...]]
```

`query` is a field challenge and `index` a UniformIndex transition; their origins
name the service methods `draw` and `index` respectively. Both block events name
the method `indices`. They preserve the complete bound and count; gated events
also bind difficulty. `bound` is the canonical
positive u64 domain fixed by the query. Native adapters additionally require a
power of two from 1 through 2^63 and absorb that bound. Explicit handlers receive
the bound and own its observation and sampling algorithm. A reader
refuses any other row width, a noncanonical or invalid bound, and a kind whose
origin method differs. Witness rows follow gated event order. Each names a real
producer Emit and validator Await at `gate.<query_site>` immediately around its
role-specific search or check call. The transport map binds that slot to the
query origin. Witnesses are construction-owned transport, not source message
observations, and are excluded from the message rows. Repeated occurrences use
the same static slot and retain actual repeat coordinates in the request.
Events and messages follow original source order. Public ports follow original
input order. The descriptor includes the complete selected logical policy,
origin tag, event labels and nominal wire codecs. Candidate implementation
names and generated helper symbols are absent from the native baseline, whose
`construction_plan` is `[]`. A programmable selection carries its executable
association:

```text
["zkc.construction-plan/0", selected_symbol, root,
 [logical_state_type, ...], initializer_or_empty,
 [start_or_empty, [original_input, ...]],
 [[adapter_symbol, "local" | "native", [origin_hex, ...]], ...], record_codec]
```

The selected symbol must equal the policy selector. Adapters cover every event
exactly once in descriptor order. A message adapter receives all leaves of its
ordered group; a query adapter returns one sample. Each group has one direction
and loop path. State inputs come first, then message values, then loop
coordinates; outputs are the query sample, if any, followed by state slots.
Child-start adapters instead receive state, their actual shared call arguments
and loop coordinates, and return state. A start event always has its own adapter,
including when its input list is empty. Only programmable plans admit starts.

A Local root calls its zero-argument initializer once per participant, then its
start handler with state and the selected original inputs. Each start input must
exist at both participants. No managed transcript is created. A Host root uses
one managed transcript input. State results follow original participant results;
loop-carried state, yields and early-completion results use the same trailing
slot order. Zero-slot state still has ordered handler occurrences. The Runtime
checks these positions and operands, including actual received message values.

`record_codec` is `[]` without a codec, otherwise:

```text
[provider_identity, [logical_record_type, ...], initialize, write, finish,
 [original_layout_input, ...],
 [[encode, receive, decode, wire_or_empty, slice, [message_origin, ...]], ...],
 conditional_write_or_empty, conditional_finish_or_empty]
```

Record slots require Copy and Drop. The three component methods retain their
ordinary identities; use on unrelated data remains legal. Message rows cover
all prover-to-verifier message origins once in order. Slice adapters consume the
original Bytes input and offset/length pairs, returning only those exact slices.
Conditional helpers wrap the selected method in the original completion
condition, with an empty Bytes or unit untaken result. Both names are empty when
there is no conditional completion. The verifier proof input and prover proof
output follow any hidden transcript ports. Ordinary output maps exclude them.

A custom bounded-index adapter checks `sample < bound` before returning. Its
ordinary handler body owns the sampling algorithm; range checks do not establish
uniformity. The Runtime independently checks the range guard and static bound.

The descriptor is encoded with the bounded logical tree encoding when hashing
or constructing an invocation root. The caller authenticates the deployment;
structural admission does not authenticate handler source or prove its security.

A constructed projection interface adds a `construction` dictionary with
`format = "zkc.native-construction/0"`, `state` types, `root`, selected `plan`
(or empty for native), `helpers`, `removed_services` (the original service
indices in strictly increasing order), and the complete actual `actions` map. Original interface fields, port
lists and action records remain unchanged. Host roots append state inputs;
both root kinds append state results. Original data and output positions stay
unchanged. Formation checks the new
signatures, remaining services and every actual action. It retains original
producer queries, messages, local calls and guards exactly and in order. Only
queries whose original service index is selected, and their paired outgoing
challenge messages, can disappear. Retained private queries stay in order. Inserted actions call the [indexed helpers](../ir/construction.md#ordered-construction).
A record construction additionally carries a `codec` dictionary with exactly
`producer`, `validator` and `helpers`. The action map removes typed proof
transport and records the actual codec calls. Its helper list names precisely
the used codec methods and generated adapters.
Complete state and coordinate checks apply recursively through participant loops. Retained authored
actions cannot call inserted helpers. These formation checks do not establish
source correspondence. Source-relative checking reconstructs the admitted
transformation and compares the whole candidate, including operands, local
definitions and metadata, ignoring locations.

## Deployment and invocation records

The owned `compileNativeProof` API and `protocol-proof` command return:

```text
["zkc.native-proof/0", source_sha256,
 descriptor, descriptor_sha256,
 candidate_json, candidate_sha256,
 [[role, participant_symbol,
   [[original_input, logical_type], ...],
   [[original_result, logical_type], ...],
   [[original_service, service_name, service_contract, ingress_index], ...],
   acceptance_index_or_empty], ...],
 [simplify, release_storage, fuse_vector_reductions, finite_bulk, fuse_collect_fold, calculation_batching],
 [[message_origin_hex, wire_site], ...]]
```

The source digest hashes the original UTF-8 bytes once captured by compilation.
The descriptor digest hashes its canonical logical tree; the candidate digest
hashes the exact carried JSON string. Booleans in this record are strings
`"true"` or `"false"`. The compiler-choice array has exactly these six entries
in this order; the mathematical choices are recorded even at their defaults
(both fusion choices false, finite bulk true, calculation batching true). Version `0`
admits one current shape with no shorter compatibility form. A proof Entry's
package options must agree with all six choices during native artifact binding.
All indices use canonical decimal strings below 1024.
Role data/result maps are in original port order. A shared original data port
must have the same nominal logical type at both roles; deployment admission
checks this before invocation inputs. A service ingress index counts
both data and retained service inputs at that role, after selected services
are removed. Service names remain tied to their original ingress positions. Acceptance is the validator's
actual result index, mapped to the selected original Boolean result; the
producer's acceptance field is empty. Generated transcript ports are appended
and excluded from these original port maps. The final wire map lists original
producer-to-validator message origins in source order with their prepared wire
sites. It is checked against both actual participant layouts, including schema
and nominal payload type, and is excluded from the cryptographic root. A
same-type message-site permutation cannot inherit another occurrence's label.
The inner descriptor/candidate digests are consistency checks; only the
independently authenticated exact-file digest authorizes the deployment.

`NativeProofOptions.mathematicalSelection` carries the same policy as draw
selection, proof construction and source/candidate checking. Its `finiteBulk`
choice defaults to true, `vectorReductionFusion` and `collectFoldFusion` to false and
`calculationBatching` to true.
`selectNativeProofDraws`, `constructNativeProof` and `checkNativeProof` receive
this shared policy. The `protocol-proof`, `protocol-construct-proof`,
`protocol-check-proof` and `protocol-constructed-participant` commands forward
`--no-finite-bulk`, `--fuse-vector-reductions` and `--fuse-collect-fold`; `protocol-proof` also forwards
`--no-calculation-batching`, which schedules the program's calculations and does
not change construction. Source proof Entries forward the same choices.
They change local preparation while preserving protocol event origins, and
add no cryptographic construction or security claim.

The deployment and complete proof are each at most 16 MiB; the participant
candidate is at most 4 MiB, under the [program carrier ceiling](program.md#carrier-size).

The `zkc bundle prove` and `bundle verify` file adapters require bounded regular
inputs, including deployment, invocation, authority, capacity, attempt-policy and
verification proof files. An authored deployment without a derived transcript
requires `--allow-authored` on either command, matching named Entry calls.
Its authenticated policy and reported `binding_scope` are checked before loading
invocation values or proof bytes. This acknowledgement adds no cryptographic
binding guarantee. Input symlinks may resolve to regular files. Producer output must differ from every configured input and referenced prover-key file,
including parent-directory aliases and existing hardlinks on Unix. Symlink and nonregular
output destinations refuse. The complete proof is encoded and staged before
atomic replacement (mode `0600` on Unix); publication errors retain execution and publication details.
These path checks protect configuration without isolating concurrent filesystem
mutation. The byte-oriented Rust APIs remain independent of file transport.

Structural limits such as event count and array width are independent ceilings;
satisfying them does not guarantee that the candidate fits its encoded byte
limit or that a particular invocation fits the host's wire, allocation and work
budgets. Candidate byte limits apply to the encoded lowered candidate; invocation
budgets apply before the corresponding allocation or work.

A role invocation is:

```text
["zkc.native-proof-inputs/0",
 [[validator, original_port, canonical_wire_hex], ...],
 [[original_port, [input_kind, value]], ...],
 context_hex,
 [[original_service_port, budget], ...],
 transcript_budget]
```

Public rows enumerate every validator data input in source order. Role input
rows enumerate that role's mapped data ports in source order. `input_kind` is
`wire` with lowercase canonical wire hex, producer-only `nonce`/`rng` with a
canonical decimal transition budget, or an authorized key constructor described
[below](#setup-authority-and-input-ownership). Issued resources use their exact
admitted physical type and the role's host domain. Service rows select retained
random services at the executing role, including validator-local services.
Replaced authorities have no service row. Budgets are at most 1,000,000. Context decodes to at most
4096 bytes. An authored no-transcript invocation requires transcript budget zero.
Input trees obey the common logical-tree limits, including through the direct
Rust API. Shared public ports must equal the role's supplied value bytes.
All input rows, canonical decodes and budgets are admitted before resource
issuance. Setup failure and execution failure use the same retirement path;
completed issuance or transitions are never hidden by a later input error.
Budgets are explicit application caps and may be lower than the required work.

The exact invocation root tree is:

```text
["zkc.native-proof-binding/0", "sha256", "zkc.native-origin/0", source_sha256,
 entry, producer, validator, descriptor,
 [[validator, original_port, logical_type, canonical_wire_hex], ...],
 context_hex]
```

The root has exactly ten fields. A managed transcript absorbs the full encoded
root at initialization. Native transitions derive challenges from that state.
Its SHA-256 digest is the expected
`ZKCPRF00` header. Physical candidates and lowering options are absent, allowing
proof exchange between independently authenticated compilations of the same
source/policy. Distinct source bytes, policies, public values or context change
the root. An authored protocol without transcript operations only checks the
header's context: changing the header can preserve its mathematical acceptance.
The authored control is not a cryptographic binding or proof-of-knowledge claim.
Execution reports use `binding_scope = "transcript"` for managed construction,
`"header"` for native-framed local/authored execution, and `"authored"` for raw
bytes with local/authored state. Raw codecs with a managed root keep
`"transcript"` binding. This reports Host absorption into the managed root;
custom handlers can ignore that state or return constant challenges. Neither
this report nor absence of an `--allow-authored` requirement establishes that
custom rules bind the proof or preserve a security argument. With local/authored raw bytes, Host context contributes
to the reported invocation identity but is not transmitted or authenticated. It is not visible to source code. Context
that an authored algorithm must bind needs an explicit public protocol input.

Final proof admission checks both roles' exact ordered native transitions,
unique origins and complete affine state chain. It also checks matching wire
layouts and that each message observation consumes the actual sent/received
value (or the freshly derived erased delivery). Private replies and unpublished
inputs obey the [construction dependency rules](../language/entries.md#construction-bodies),
which do not assert termination independence. An extra unreachable transition,
a dropped final observation, duplicate static helper use or an unlisted transcript operation
refuses. Ordinary supplied-carrier admission grants none of these proof-specific
properties.


## Message and public-input types

The [complete message grammar and codecs](messages.md) cover
scalar, numeric and structured payloads, including PCS values. Public inputs
also admit standalone BLS12-381 multilinear tables in `arkworks.mle-lsb/0` and
authorized verifier keys. Tables and keys are not proof-message payloads.

A BLS field-array frame is `ZKCV`, byte `0`, tag `64`, then the exact
type-declared number of canonical 32-byte scalars. Index uses tag `31` (`0x1f`) and a u64
little-endian value. A public table uses tag `2`, u32 little-endian arity, then
exactly `2^arity` canonical scalars in logical MSB order. Arity, allocation and
exact frame length are checked before allocation or scalar decoding. The root
binds the complete canonical public bytes under invocation limits.

Ordinary validator local functions may use admitted copyable data, polynomial
arithmetic and immutable verifier keys. They cannot consume or produce live
resources. Generated transcript helpers obey the [complete-state rule](../ir/construction.md#compact-state-and-independent-admission).
This supports a Sumcheck verifier that checks every round and evaluates the
original public polynomial at its final point. A committed terminal additionally
needs the explicit PCS check below.

## Setup authority and input ownership

The [setup registry contract](messages.md#application-authorized-setups)
defines exact public-key and input-port authorization, including multiple setups.
For `multilinear.kzg.bls12-381/0`, a verifier key is immutable
host input data with descriptor codec `zkc.native-verifier-key/0` and canonical
`ZKCAR000` bytes; keys and opening states never cross the proof wire.

A role input `[original_port, ["verifier_key", public_port]]` selects its
authorized public key. A producer-only prover-key input is:

```text
[original_port, ["prover_key_file", [path, expected_material_fingerprint_hex]]]
```

The application supplies the full-material fingerprint independently. The loader
checks it, the selected verifier projection and setup identity. Paths resolve
relative to the Host working directory. Imports capture one bounded regular
file; symlinks may resolve to regular files. Descriptor validation and nonblocking
open on Unix refuse devices, directories and FIFOs without waiting for a writer.
Input byte, value and work budgets apply before key loading and resource issuance.
No proof byte requests a key file. Local paths are trusted Host configuration;
an external request does not itself authorize a filesystem read.

All tables committed under a key must have exactly its positive arity;
`pcs.commit` checks this before invoking the upstream routine. Opening states
are created by local commitment work, not imported. Every mapped input, including
unused inputs and inactive PCS alternatives, needs its installed constructor and
setup association. Authorizing material does not prove honest setup generation
or an SRS law.

### PCS message bytes

Default representations use `ZKCV`, byte `0`, tag `6` (commitment) or `7`
(opening proof), followed by:

```text
"ZKCAR000" | kind:u8 | arity:u64le | setup_id:32 | key_id:32 | group_payload
```

Inner kind is `2` for a commitment and `3` for an opening proof. A commitment
contains one 48-byte compressed G1 point (135 native bytes total); an opening
proof contains exactly `arity` compressed 96-byte G2 points (`87 + 96*arity`
bytes total). Registry selection and complete metadata checks follow the setup
contract. Decoding checks bounds, subgroup membership and canonical re-encoding;
canonical infinity is valid. Malformed receives stop before observation.

The constructor observes PCS data through the same complete-type
`transcript.native.indexed.observe.data` contract. A value under another authorized
key can decode and be observed before the explicit `pcs.check` rejects it against
the verifier-key operand. There is no per-receive expected-key selector.
