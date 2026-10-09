# Native proof execution

This profile defines independent proof production and verification for
[mathematical protocols](mathematical-protocols.md). A deployment selects a
producer and a validator from declared roles. Each executes its own participant
program. The validator receives an authorized public context and a candidate
proof; it does not require the producer, its witness, or its live resources.
[Status](../../../status.md) records implementation coverage;
[native proof compilation](../../../compiler/native-proofs.md) records the
implementation and executable examples. Policy, deployment, descriptor,
construction map and binding each have one current schema; occurrences use
`zkc.native-origin`.
Flat programs, loops, PCS and structured messages share this contract and
`zkc.program`. Unknown tags and malformed records refuse independently.

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

## Ordered construction

A selected challenge construction declares which owner-local entropy operations
it replaces and which validator-to-producer deliveries it removes. The selector
is checked against the source operation, service/resource provenance and actual
use, not only a site string or result type.

For each selected source occurrence:

1. Retain every original validator computation, guard and possible stop in its
   original order, except for the explicitly replaced entropy operation and
   delivery. Keep unused ordered work.
2. At a producer-to-validator message, retain the producer's sent component and
   the validator's actual decoded receive component. Each role observes its own
   component at that message occurrence after its local send/receive completes.
3. Replace the selected validator draw with a transcript transition at that
   draw occurrence. Derive the producer's value at the corresponding removed
   receive using the declared same prefix and challenge occurrence. A prefix
   mismatch refuses construction; projection is not an equality argument.
4. Observe an erased validator-to-producer message on both roles at its original
   message occurrence. The challenge transition and this message observation
   are separate events. No proof payload is emitted for that delivery.
5. Preserve the remaining source/result mapping, including the actual acceptance
   index after removed resource ports. Public replay recipes, when admitted by
   a selected extension, require total interpreted bodies and available actual
   operands; a validator's successful guard is not a producer recipe.

The selected policy fixes observations through the final message, even after the
last challenge. An unused observation is still a transition with failure/work
behavior. A host never performs an implicit second absorption. Observing an
erased challenge delivery or a post-final-challenge message retains the selected
ordered transition policy; no extra entropy or security benefit is claimed. A
different observation policy is a distinct construction, not an optimization
justified by an unused digest alone.

A source-selected service port is removed only when every reachable query on
that selected authority is accounted for, including unused replies and nested
occurrences. Other service roots and aliases keep their original meaning.
Construction does not issue a dummy zero-budget RNG to stand in for a
transcript. Resource mappings describe correspondence; transcript generations
need not equal source RNG generations.

The construction has one validator random service port. A direct
query takes exactly that service reference, no data arguments, and returns one
field. Its sole delivery uses that exact SSA result: derived values and
`protocol.restrict_roles` wrappers refuse. Pairing is checked in the same source
block after unsimplified static expansion, retaining the authored call path.
There is no intervening query or producer-to-validator message. Two outstanding
draws, batched/derived delivery and undelivered private coins refuse this profile.
It refuses other validator service ports, unselected queries, unused selected
draws, nonchallenge reverse messages, existing transcript inputs, and selected
draws hidden in local programs. Those restrictions bound the constructor, not
the common IR or every authored deployment.

The selected authority includes every alias of its root. The construction's
single validator port and native service owner contract exclude another
validator alias and cross-owner binding respectively. A deployment attempting to
share the validator challenge root with producer entropy refuses at registry
admission. That owner check does not prove independently distributed randomness
across distinct roots. Broader selectors must account for all reachable aliases.

## Transcript state and occurrence identity

Each internally constructed role owns a distinct affine transcript capability.
The host initializes it from the authorized invocation binding and selected
suite; it is not a user-supplied token. Initialization absorbs the full
canonical root bytes under the installed suite's fixed `binding` label. The
proof header contains their SHA-256 digest; it does not replace those bytes in
initialization. Local transcript kernels consume the current state and return
its successor. Loops carry successors explicitly. A capability cannot be
serialized, copied, reset or restored from public bytes. The constructor
appends the final transcript as an internal participant result, mapped
separately from source results. The host disposes it after normal return;
stop/cancellation follows the ordinary cleanup contract. It never becomes proof
data or an application result. No generated terminal consume operation is
inserted. Acceptance waits for normal return, successful cleanup and proof
exhaustion.

The application supplies the SHA-256 digest of the exact deployment file bytes
independently of the candidate and proof, from trusted compilation or deployment
configuration. The host hashes the buffer it will parse before interpreting it.
Source and descriptor hashes inside an untrusted file are claims, not authority;
pinning only those claims would permit candidate substitution. The trusted
compiler constructs and checks the actual candidate and carries its regenerated
descriptor. This authenticates that compilation result; lowering correctness is
still the compiler's stated evidence level, not a theorem supplied by a hash.

A selected occurrence identifies the original entry, authored call/repeat path,
operation and owner. The indexed contract carries a bounded static template and
explicit induction operands; its dynamic-coordinate vector is empty for flat
programs. The [occurrence encoding](#native-occurrence-encoding) fixes those
bytes and bounds. Generated helper names and runtime diagnostic frames do not
determine transcript identity. Occurrence resolution precedes optimization.

Each inserted transition is top-level in a straight-line local helper containing
only its coordinate construction, transition, complete return and admitted
storage releases. The helper executes at one static participant site per role;
an enclosing participant loop may reach that site repeatedly. Local conditional
or repeated execution of the transition inside the helper refuses.

The checked deployment includes the role-independent ordered occurrence list.
Each role's statically planned inserted sequence must match that list exactly;
stops may execute only a prefix. An occurrence is unique within each role's list,
while corresponding producer/validator occurrences carry identical bytes. In
particular, the producer's challenge names the original validator query and its
source owner, not the executing producer. These structural checks are repeated
at proof admission against the actual final artifact, after optimization.

Proof admission also closes the generated state chain: each role has exactly one
chain from its mapped internal transcript input to its mapped internal result,
and every transition is a listed native-origin operation. Only those operations
and their explicit helper entry/return wiring may consume or produce that suite
state. No extra transition, alternate state root, dropped successor,
or native-origin operation elsewhere is admitted. An occurrence-list match
alone is insufficient to establish the actual transcript sequence.

The indexed-origin attribute rule checks lowercase, even-length hex and its
bound before decoding the exact static template grammar, empty coordinate array
and absence of trailing bytes. Installed primitive admission alone grants
neither source correspondence nor occurrence uniqueness. A generic supplied
runner can execute the indexed kernel but cannot authorize a proof deployment
or construction claim without its separately checked envelope.

The suite fixes framing, absorb grouping, domain labels, challenge mapping and
failure behavior. Equal output fields do not make two suites interchangeable. A
reduced wide-byte sample is not an exactly uniform field draw. A nonzero
challenge policy requires an explicit reject/retry rule; zero is not silently
resampled.

For iterated construction, dynamic coordinates are explicit semantic inputs to
the observation/challenge operation. Optimization preserves those inputs;
a future transformation that peels a loop must substitute the induction value
and supply the required correspondence, rather than infer an origin from a changed
runtime frame. The current iterated admission retains the original loop structure.

Explicit [external construction data](../../realization/external-constructions.md)
keeps its separate contract. Its copyable Monero/OpenVM states are checked data,
not live affine capability snapshots. Its exact upstream inputs do not acquire
zkc transcript prefixes. Trial copies consume actual work; their reachability,
publication and live witness check remain obligations of the authored program
and host.

## Proof transport and admission

Proof transport implements participant sends and receives. It does not evaluate
protocol equations or choose challenges. Message types, occurrences, peer roles
and decoding policies come from the admitted deployment. A candidate proof
cannot choose a different program, codec or verifier configuration.

The framed proof starts with the eight bytes `ZKCPRF01`, followed by the 32-byte
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
[authored transition rules](../../realization/external-constructions.md#authored-native-deployment).
Authored execution
has no generated transcripts and refuses authored validator transcript inputs.
Other validator resources require a separate explicit policy; a witness or
ambient oracle cannot enter through this exception.

## Completion and failure

Validation accepts only after the selected Boolean result is true, the role has
returned normally, and the proof reader is exhausted. A true result with
trailing bytes is not acceptance. Stop reasons retain their distinctions; host
failures are not coerced into an ordinary false result. A partial proof is never
a completed producer result. File publication is atomic after successful
completion. A runner already stopped during entry initialization retains that
stop and its cleanup diagnostics; the driver does not open a proof reader or
writer after that stop. Every proof operation otherwise requires a runner still
at entry. Successful ingress is part of loading; polling that merely exposes the
first action is allowed. A completed or partly consumed runner refuses with
`artifact-runner-started`, before consuming proof bytes. A live partly consumed
runner is cancelled and retains its cleanup observations. A pre-existing terminal
stop is returned unchanged, even on a subsequent call; it is not a new proof
failure. The host always constructs a fresh runner for each proof or attempt.

One-shot reports retain the actual stop, including local call/function/instruction
coordinates, independently of their short failure code. Attempt reports retain
per-attempt stops. Ingress keeps its `ingress.<parameter>` outer site and stores
the inner instruction separately. These are diagnostics and do not alter origins,
transcript history or proof framing.

Session cleanup requires no active frames or residual logical resource units.
The proof host does not export returned logical units to a caller. Deployment
admission refuses affine entry outputs other than RNG, nonce or transcript
successors with `native-proof-output-kind`, before invocation loading or issuance.
The attempt policy further restricts successors to its persistent RNG and
transcript kinds. Internal units remain legal when consumed or retired at frame
exit. Unreturned units retire on return, stop or cancellation. The final residual
unit check is a defense against a broken backend or host custody contract:
`native-proof-live-resource-units` prevents publication, including for single-shot
execution. Admitted completed executions do not normally reach this refusal.

Completed draws, transcript transitions, consumed bytes and work remain consumed
on rejection, stop, cancellation and failed attempts. Decoding finishes before
the receive is accepted and before its subsequent transcript observation. A
length consumed before truncation remains consumed in the reported prefix.

Bounded whole-proof retries use a fresh invocation transcript and unpublished
output buffer for each attempt, while retaining provider state and cumulative
work across attempts. Only an explicit retryable result permits another attempt.
For retries to produce new challenges, the protocol needs fresh prover entropy
or another changed attempt input. Repeating identical inputs under an identical
transcript root does not produce new challenges. The host enforces a finite
attempt bound; it does not infer freshness or progress. Fatal stops and resource
exhaustion do not become retry signals. An external suite may intentionally
restart the same public transcript root per attempt; dynamic diagnostic attempt
identity does not add cryptographic bytes unless its suite says so. The constructor preserves a
finite attempt body; the native host can repeat it under the application policy
below.

Independent loop execution uses the role's actual count under declared bounds.
Any required shared count is derived from bound public context or an admitted
proof value and checked by the validator; a joint driver's agreement check is
unavailable in independent proof execution. Zero trips execute no body draws or
absorptions. Program and metadata size remain independent of runtime trip count.

### Typed invocation inputs

`NativeDeployment::execute_typed(&ProofInputs, proof)` and
`execute_attempts_typed(&ProofInputs, policy)` share preparation, issuance,
execution and cleanup with positional invocation records. The adapter checks
explicit original port selectors before constructing the typed request. Typed
vectors follow the admitted public, role-input and service order exactly.
Context is a byte vector of at most 4096 bytes; provider/transcript budgets retain
the one-million-transition ceiling. Attempt policy admission precedes request
parsing, material loading and entropy issuance.

Public values are independently authorized by the caller. Ordinary public and
private data use shared `InputValue::Native`, `Wire` or `Variant` constructors.
Native values retain upstream library invariants and undergo the same complete
physical type, installed profile, setup and entry checks as decoded data.
Public verifier keys require canonical wire bytes and independently installed
pins. A role's unit `VerifierKey` declaration selects its admitted public key;
a prover key uses its separate authenticated material constructor. Foreign
capabilities or key handles cannot enter through ordinary native data.

`ProverMaterial::from_bytes` imports immutable proving material against a complete
material fingerprint and the supplied verifier key. Import alone grants no
invocation authority: each call selects its own independently pinned setup.
`from_file` captures
one bounded regular file and delegates to the same import. The handle has private
storage and supports shared ownership; requests use `InputValue::ProverKey`.
Each invocation rechecks the actual selected setup, complete physical type and
current backend limits before loading files or issuing resources. Retained data,
loading work and every runtime/retry operand remain charged. Reuse avoids file
reads and key parsing; it shares no live capability or mutable session. Import
checks per-object wire/retention limits; execution budgets belong to each call.
A material fingerprint authenticates identity, not the honesty of setup bases.

Constructor shapes, complete native types, wire lengths and the statically known
binding-root size are checked before importing verifier keys. The whole
invocation reserves loading capacity before data decoding, key-file
reads or entropy issuance. Public verifier-key import scans consume cumulative
work and registry material consumes retention, including receive-only keys.
Immutable values are validated before loading other wire/file inputs. Public
native values are canonically encoded for the binding; private native values
need no serialization unless they also occupy a public port. Every shared role
operand must have the same canonical bytes as its independently supplied public
value. Mismatch returns `native-proof-shared-public-input` before execution.
Wire requests retain exact-byte agreement and reuse the matching admitted public
value. Additional native encoding work is reserved before loading, and binding
hex expansion is bounded before allocating its strings. Invocation loading
capacity and per-attempt execution budgets are distinct: a valid request may
load successfully and then report an execution limit at its first attempt.

### Typed participant results

`NativeProofReport::outputs` contains successful copyable results keyed by their
original common-program output indices. Producer and validator results use their
own role maps. It is `None` on rejection, body failure, attempt exhaustion or
cleanup failure, and `Some` with an empty map when success has no copyable
original results. Generated transcript results and private RNG/nonce successors
remain lifecycle state and are retired; they are not exported as data. Result
selection follows the admitted output map and physical duplicability.

A bounded attempt run retains results only from the final successful attempt.
Earlier attempts retain their existing decision/usage/stop records. The Host
uses the same controller and actual provider state across attempts. Adding SDK
result access neither serializes those values into CLI diagnostics nor places
them in proof bytes; proof framing and binding remain unchanged.

## Native attempt policy

The native host accepts this application-owned record alongside a pinned native
deployment. It is not supplied by a candidate proof or inferred from its header:

```text
["zkc.native-attempt-policy", completion_original_result,
 [[rng_original_input, rng_original_result], ...],
 [attempt_limit, proof_byte_limit],
 [instruction_limit, iteration_limit],
 [live_payload_limit, total_payload_limit]]
```

Every number is a canonical unsigned decimal string. Parsing is bounded to
64 KiB and the existing logical JSON tree limits. Port indices are below 1024;
attempts are 1 through 1024. Proof bytes cannot exceed 16 MiB; instruction,
iteration and payload limits cannot exceed the corresponding interpreter
hard ceilings. Zero work, payload or proof budgets are deliberate execution
refusals, not unbounded values. The proof cap includes the framing header.

The completion port must name a producer Boolean result. True completes; false
requests retry. RNG pairs are a bijection over producer RNG input/result ports,
with equal physical types. Port maps resolve original indices, excluding the
internal transcript ports. Every returned RNG, on retry and completion alike,
must authenticate as the current generation of the mapped original root.
Wrong roots, stale/foreign handles and other affine output types refuse.
One-shot nonce inputs refuse; only installed wire/key constructors and persistent
RNG inputs are admitted by this adapter. Services retain their issued references
and actual provider state across entry leases.

Each attempt issues a fresh selected-suite transcript with the same invocation
root, then retires it after runner cleanup. The host does not reset RNG/service
state or external primitive-work charge. Remaining interpreter instruction/call/
iteration and total payload allowances are passed into each runner; initialization
failure retains reached charges. Live payload and transcript-transition limits
are per attempt. Transcript initialization reabsorbs the bounded invocation root
once per attempt, outside interpreter and external-work charges. The proof
writer enforces the per-attempt byte cap before extending its buffer. Terminal
execution and cleanup failures prevent retry and publication. Cleanup diagnostics
do not replace a prior execution failure.

Only normal completion followed by successful session cleanup returns proof bytes
to the publisher. Failed/retried bytes and producer outputs never enter CLI
proof diagnostics. The typed SDK returns copyable original outputs only from the
selected successful final attempt. Per-attempt decisions, stop coordinates, counters and a policy digest are
private host diagnostics. The digest is SHA-256 of compact UTF-8 JSON for the
record above, with no whitespace and the supplied pair order. It is not inserted
into the transcript or proof. The application must authorize the policy itself;
verifier acceptance does not certify which retry policy the producer used. A
retry attempt may itself contain an accepting proof; discarding its bytes is a
host publication property, not an additional verifier predicate.

The native host supports the registered native transcript suites
and deployments with authored copyable external state. This policy does not expand the
constructor's rejection of authored transcript inputs, hidden selected draws or
unsupported message types.

## Checking and analysis inputs

The construction checker checks the actual candidate: original verifier actions,
removed draws/deliveries, actual absorb operands, codecs, prefixes, public entry
maps, state succession, result maps and selection completeness. Compilation then
checks the actual lowering/physical candidate under its declared evidence level.
Hashes bind these subjects but do not prove either transformation.

The retained mathematical subjects and mappings expose typed algebra, actual
role-specific receives, reached source draws and candidate transitions,
root/alias bindings, dynamic paths, guards/stops and later disclosure. A private
guard is not automatically public observation. Distribution laws, root
initialization assumptions, honest delivery and observers are separate premises.
See the [observation requirements](../../../compiler/ir-foundation.md#information-retained-for-observation-analyses).
Their preservation does not require implementing the future affine analyzer.

Readers admit only this proof contract. Native structural checking does not
inherit an independent Lean source interpreter, a proof about another carrier,
or a Fiat–Shamir security theorem.

## Native occurrence encoding

An indexed native kernel carries the bounded static template:

```text
["zkc.native-origin-template", entry, [step, ...], [], event]
event = ["query", protocol, site, service_port, service_contract, method, owner]
      | ["message", protocol, site, schema, sender, receiver]
step = ["apply", original_caller_protocol, original_apply_site]
     | ["repeat", original_protocol, original_repeat_site]
```

The tree uses the canonical logical encoding: tag 0 followed by a u64
little-endian UTF-8 byte count and string bytes, or tag 1 followed by a u64
little-endian element count and recursively encoded elements. An application
step precedes its callee's steps; a repeat step precedes every event in its body.
The path excludes the final event. Roles reflect static application substitution.
Service ports are `input_N`, with the original input index as a canonical u64
decimal. A message schema is its original source site. The checked wire map
connects it to the prepared site without using generated names in the origin.

Names are nonempty printable ASCII (bytes 33 through 126), at most 128 bytes.
Paths have at most 64 steps. The encoded template is at most 2048 bytes and is
carried as exactly one lowercase, even-length hex attribute, at most 4096
characters. Its coordinate array must be empty. Unknown tags, alternate shapes,
noncanonical hex and trailing bytes refuse. Challenges require query events;
observations require message events. These checks establish syntax, not source
correspondence or unique execution.

The dynamic operation takes an explicit `indices` value. Its entries are the
actual induction values of the enclosing repeats, outermost first, with one
entry per `repeat` step. The final absorbed bytes encode:

```text
["zkc.native-origin", entry, [step, ...], [iteration_decimal, ...], event]
```

Each iteration is a canonical unsigned 64-bit decimal string. The vector has
at most 64 entries; the final encoding is bounded by 4096 bytes. A length
mismatch refuses. The operation neither reads runtime frame names nor infers
coordinates from dispatch order. Query labels still name the source validator's
draw when executed by the producer. Zero trips perform no body transition.
The existing suite framing absorbs the dynamic bytes under its static `origin`
label, so dynamic instances introduce no dynamically interned Merlin labels.

The generated contracts are `transcript.native.indexed.challenge` and
`transcript.native.indexed.observe.data`. They retain the affine transcript,
sampling/observation/history facets and
resource transitions. The final kernel operand is `indices`. A generated local
helper instead receives one scalar index argument per enclosing loop, constructs
that vector with exactly one `indices.empty` followed by ordered
`indices.append` operations, performs one transition and returns its complete
results. Each append must use the next helper argument directly. Other
computation or local control in that helper refuses. Physical releases follow
the ordinary last-use rules: intermediate index vectors may be released between
appends, and the observed payload may be released after the transition.
Transcript capabilities and returned values cannot be released.

## Compact state and independent admission

The descriptor keeps a flat static event list in source depth-first order. It
stores each source template once, regardless of runtime count. It does not
repeat a second control tree already present in the participant programs.

Construction appends the transcript as the last carried value of every
participant loop whose subtree contains selected transcript events. The body
receives that state, consumes/produces its successors and yields the final
successor last. The loop result feeds subsequent events. Outer induction values
are explicit captures in nested loops. Event-free loops retain their original
state and may belong to one role. They cannot contain hidden transcript events
or unobserved proof messages.

Final Rust admission checks every role recursively. Each inserted helper is
used at exactly one static site per role; a loop may execute that site repeatedly.
Helper coordinate arguments must be exactly the enclosing induction operands in
order. For each origin path prefix ending in `repeat`, admission derives a
bijection to the actual participant loop site and maximum. Both roles must have
the same mapping. Every listed event must appear, and every helper must be used.
Observation operands must be the actual sent/received value or the newly derived
challenge delivery. The state must flow from the internal entry port through
every transition and loop to the final internal result. Capturing, dropping,
substituting or bypassing that state refuses.

Draw/delivery pairs remain within one source block. A selected draw cannot remain
pending at a loop boundary. Original guards, local work, producer service draws,
nonselected messages and action order are retained. The source-relative checker
reconstructs the transformation and compares the complete unsimplified candidate,
including count operands, loop bounds, state wiring and metadata. Physical
admission does not independently prove equivalence of two count expressions.
Current provenance admission requires preserved loop structure; peeling,
unrolling or fusion needs a separate correspondence rule before admission.

The independent driver advances each reached loop through the runner's explicit
local-control API, using that role's count and bound. It establishes no peer
count agreement. An authored verifier must validate any semantic count condition
needed by its protocol. Proof exhaustion and ordinary stops retain their existing
meaning. The joint driver continues to use its separate count-agreement policy.

## Deployment policy and descriptor

The compiler's policy is an exact array (JSON spelling carries no identity):

```text
["zkc.native-proof-policy", entry, producer, validator, acceptance,
 suite, service, public_inputs, [[query_site, delivery_site], ...]]
```

Indices are canonical decimal strings less than 1024. Public input indices are
strictly increasing and enumerate every validator data input, including unused
inputs. All are explicitly authorized for public invocation binding. `service`
is the original validator service input index. An empty suite and service with
an empty draw list selects authored execution without a transcript. Otherwise
both a supported suite and the selected service are required, with one through
64 draws. Selectors use prepared static occurrence sites; native labels retain
original authored paths. No timing or security premise follows from selecting
this policy.

The immutable compiler descriptor is:

```text
["zkc.native-proof-descriptor", policy, "zkc.native-origin",
 [[event_kind, origin_hex], ...],
 [[validator, original_port, logical_type, codec], ...],
 [[message_origin_hex, logical_type, codec], ...]]
```

Events and messages follow original source order. Public ports follow original
input order. The descriptor includes the complete selected logical policy,
origin tag, event labels and nominal wire codecs. Candidate implementation
names and generated helper symbols are absent. The descriptor is encoded with
the bounded logical tree encoding when hashing or constructing an invocation
root.

A constructed projection interface adds a `construction` dictionary with
`format = "zkc.native-construction"`, the logical `transcript` type,
`removed_services` (the original service index), and a complete actual `actions`
map. All original interface fields, port lists and action records remain
unchanged. Each participant appends exactly one transcript input and result;
original data and output positions remain unchanged. Formation checks the new
signatures, remaining services and every actual action. It retains original
producer queries, messages, local calls and guards exactly and in order. Only
queries at the removed service owner and that owner's outgoing challenge
messages can disappear. Inserted actions call the indexed helpers defined above.
Complete state and coordinate checks apply recursively through participant loops. Retained authored
actions cannot call inserted helpers. These formation checks do not establish
source correspondence. Source-relative checking reconstructs the admitted
transformation and compares the whole candidate, including operands, local
definitions and metadata, ignoring locations.

## Deployment and invocation records

The owned `compileNativeProof` API and `protocol-proof` command return:

```text
["zkc.native-proof", source_sha256,
 descriptor, descriptor_sha256,
 candidate_json, candidate_sha256,
 [[role, participant_symbol,
   [[original_input, logical_type], ...],
   [[original_result, logical_type], ...],
   [[original_service, service_name, service_contract, ingress_index], ...],
   acceptance_index_or_empty], ...],
 [simplify, release_storage],
 [[message_origin_hex, wire_site], ...]]
```

The source digest hashes the original UTF-8 bytes once captured by compilation.
The descriptor digest hashes its canonical logical tree; the candidate digest
hashes the exact carried JSON string. Booleans in this record are strings
`"true"` or `"false"`. All indices use canonical decimal strings below 1024.
Role data/result maps are in original port order. A shared original data port
must have the same nominal logical type at both roles; deployment admission
checks this before invocation inputs. A service ingress index counts
both original data and service inputs at that role. Acceptance is the validator's
actual result index, mapped to the selected original Boolean result; the
producer's acceptance field is empty. Generated transcript ports are appended
and excluded from these original port maps. The final wire map lists original
producer-to-validator message origins in source order with their prepared wire
sites. It is checked against both actual participant layouts, including schema
and nominal payload type, and is excluded from the cryptographic root. A
same-type message-site permutation cannot inherit another occurrence's label.
The inner descriptor/candidate digests are consistency checks; only the
independently authenticated exact-file digest authorizes the deployment.
The deployment and complete proof are each at most 16 MiB; the participant
candidate is at most 1 MiB.

The `zkc prove-bundle` and `verify-bundle` file adapters require bounded regular
inputs, including deployment, invocation, authority, capacity, attempt-policy and
verification proof files. An authored deployment without a derived transcript
requires `--allow-header-only` on either command, matching named Entry calls.
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
["zkc.native-proof-inputs",
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
admitted physical type and the role's host domain. Service rows select mapped producer random services;
the validator has none. Budgets are at most 1,000,000. Context decodes to at most
4096 bytes. An authored no-transcript invocation requires transcript budget zero.
Input trees obey the common logical-tree limits, including through the direct
Rust API. Shared public ports must equal the role's supplied value bytes.
All input rows, canonical decodes and budgets are admitted before resource
issuance. Setup failure and execution failure use the same retirement path;
completed issuance or transitions are never hidden by a later input error.
Budgets are explicit application caps and may be lower than the required work.

The exact invocation root tree is:

```text
["zkc.native-proof-binding", "sha256", "zkc.native-origin", source_sha256,
 entry, producer, validator, descriptor,
 [[validator, original_port, logical_type, canonical_wire_hex], ...],
 context_hex]
```

The root has exactly ten fields. The full encoded root is absorbed at transcript
initialization; changing these
bytes changes the derived challenges. Its SHA-256 digest is the expected
`ZKCPRF01` header. Physical candidates and lowering options are absent, allowing
proof exchange between independently authenticated compilations of the same
source/policy. Distinct source bytes, policies, public values or context change
the root. An authored protocol without transcript operations only checks the
header's context: changing the header can preserve its mathematical acceptance.
The authored control is not a cryptographic binding or proof-of-knowledge claim.
Execution reports distinguish `binding_scope = "header"` from `"transcript"`.

Final proof admission checks both roles' exact ordered native transitions,
unique origins and complete affine state chain. It also checks matching wire
layouts and that each message observation consumes the actual sent/received
value (or the freshly derived erased delivery). An extra unreachable transition,
a dropped final observation, duplicate static helper use or an unlisted transcript operation
refuses. Ordinary supplied-carrier admission grants none of these proof-specific
properties.


## Message and public-input types

The [complete message grammar and codecs](structured-proof-messages.md) cover
scalar, numeric and structured payloads, including PCS values. Public inputs
also admit standalone BLS12-381 multilinear tables in `arkworks.mle-lsb/1` and
authorized verifier keys. Tables and keys are not proof-message payloads.

A BLS field-array frame is `ZKCV`, byte `1`, tag `64`, then the exact
type-declared number of canonical 32-byte scalars. Index uses tag `0x31` and a u64
little-endian value. A public table uses tag `2`, u32 little-endian arity, then
exactly `2^arity` canonical scalars in logical MSB order. Arity, allocation and
exact frame length are checked before allocation or scalar decoding. The root
binds the complete canonical public bytes under invocation limits.

Ordinary validator local functions may use admitted copyable data, polynomial
arithmetic and immutable verifier keys. They cannot consume or produce live
resources. Generated transcript helpers obey the complete-state rule above.
This supports a Sumcheck verifier that checks every round and evaluates the
original public polynomial at its final point. A committed terminal additionally
needs the explicit PCS check below.

## Setup authority and input ownership

The [setup registry contract](structured-proof-messages.md#application-authorized-setups)
defines exact public-key and input-port authorization, including multiple setups.
The installed PCS is `multilinear.kzg.bls12-381/1`. A verifier key is immutable
host input data with descriptor codec `zkc.native-verifier-key` and canonical
`ZKCAR006` bytes; keys and opening states never cross the proof wire.

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

Default representations use `ZKCV`, byte `1`, tag `6` (commitment) or `7`
(opening proof), followed by:

```text
"ZKCAR006" | kind:u8 | arity:u64le | setup_id:32 | key_id:32 | group_payload
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

## Terminal composition

The protocol author is responsible for naming the original commitment, actual
verifier point, claimed value, opening proof and authorized verifier key, and for
making the `pcs.check` result necessary for acceptance. An ordered guard is one
way to do this. A final Sumcheck residual by itself does not verify a committed
polynomial evaluation. The committed Sumcheck examples open each factor at the
verifier's accumulated point and combine those checked evaluations with the
final claim.

The compiler preserves the authored operands, guards and result flow; it does
not prove that these choices establish the intended relation. Omitting an
opening guard in the source can therefore produce a well-formed deployment
with an unsound acceptance predicate. Source-relative checking rejects changing
or removing a guard or its operand relative to the captured source. These are
distinct checks: preserving a protocol does not prove its soundness.

`pcs.commit` retains an immutable original table in its local opening state.
Sumcheck restrictions produce separate scratch tables. Opening the original
state through aliases, including repeated openings, cannot replace its backing
with a restricted table. The installed PCS requires positive arity; a
zero-variable committed invocation refuses instead of silently padding. Public
zero-variable Sumcheck remains available without this PCS terminal.

These contracts establish representation and execution boundaries. They do not
establish PCS or Fiat–Shamir security, hiding, a zero-knowledge protocol or native
Lean correspondence. For authored proofs, unrelated application context remains
only header-bound unless the authored algorithm binds it cryptographically.
