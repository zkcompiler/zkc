# Transcript construction

This is a native contract. [Compilation](../../compiler/construction.md),
[transport](../formats/proof.md), [execution](../runtime/proofs.md)
and [attempts](../runtime/attempts.md) define separate boundaries.
[Proof usage](../../runtime/proofs.md) explains their application.

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
justified by an unused digest alone. The
[construction obligations](construction-obligations.md) define the admissible
observation classes, the binding obligations and the obligations of other
transcript providers.

A source-selected service port is removed only when every reachable query on
that selected authority is accounted for, including unused replies and nested
occurrences. Other service roots and aliases keep their original meaning.
Construction does not issue a dummy zero-budget RNG to stand in for a
transcript. Resource mappings describe correspondence; transcript generations
need not equal source RNG generations.

Native shorthand selects one validator random service port. A programmable
construction selects a nonempty finite set of ports owned by that validator.
Each direct query takes its actual selected service reference: `draw` returns
that contract's field; `index` takes its constant UniformIndex bound and returns
one index. Query result domains need not match the provider's state domain.
Native fallback rules still require the installed suite's query domain.

Each selected query has one delivery using its exact SSA result: derived values
and `protocol.restrict_roles` wrappers refuse. Pairing is checked in the same
source block after unsimplified static expansion, retaining the authored call
path. There is no intervening query or producer-to-validator message. Two
outstanding draws, batched/derived delivery, unused selected draws,
nonchallenge reverse messages, existing transcript inputs and selected draws
hidden in local programs refuse this profile. These restrictions bound the
constructor, not the common IR.

Unselected verifier queries remain explicit private service actions. Their
replies may affect local guards and acceptance, but cannot flow into shared
construction state, child-start arguments or counts of shared-event loops.
Runtime admission checks actual Local bodies, control dependence and loop fixed
points. It conservatively retains dependencies even when ordinary arithmetic
would cancel them. Construction does not turn private entropy into a public
challenge or prove independence of distinct randomness roots.

A child's selected ports must be the exact preimage of the parent's selected
set through the call's service mapping. Every alias of a selected parent root
is selected; every selected child port maps to a selected parent root. Parent
roots not passed to that call need no child counterpart. The mapped verifier
owner is checked separately. Registry admission refuses cross-owner sharing of
a randomness root; this owner check does not establish independent randomness.

## Programmable state and handlers

A selected `protocol.construction` symbol binds a protocol, provider, replaced
services, state slots, root factory and typed scoped functions. Preparation preserves
that record exactly. Construction admits its event coverage and authority before
consuming the record and projecting participant programs.

Construction checks sequencing, selected operands and authority. An authored
handler can ignore or reset copyable state through ordinary computation; these
checks do not establish an absorption law or security of the chosen transcript.

Records retain child associations as `applications = [{site, construction},
...]`; `root_only` records an explicit/inherited format or native-root
requirement that prevents child reuse. The independent resolver checks original
call targets, role and service mappings, closed provider identity and complete
child coverage before producing an execution selection. The emitted module
contains exactly the selected construction closure.

Preparation inserts an ordered `protocol.construction_start` at each selected
application. Its operands are the actual selected callee inputs, available at
both participants; its `roles` and `site` identify the owners and occurrence.
Inside a repeat, both roles must participate in that repeat, even for a start
with no inputs or with only body-local constants.
Correspondence checks its position against the original call. Projection
preserves it at both roles. Construction consumes it into `protocol.local_call` operations
on the current state, actual arguments and enclosing loop coordinates. It is
neither a runtime opcode nor a second state initializer. Starts of empty
children remain ordered; zero-trip loops execute no starts.

A local root calls its zero-argument factory once per participant, followed by
the start handler on that role's actual selected original inputs. Local state
requires `Copy` and `Drop`; it may contain several native slots or none. State
slots are internal results, not application outputs. A host root instead uses
the selected managed transcript capability described below. Only the selected
handler closure can consume it; original protocol ports and unrelated scoped
functions cannot introduce another transcript root. Checked `ManagedHistory`
operations expose byte observation, field sampling and supported index sampling
to ordinary source functions. This facet permits advancing existing state and
does not authorize acquisition, copying or reset.

One message handler receives the ordered native leaves of its source payload
after the last send or receive. Total calculations may separate those leaves;
another ordered effect may not. Each role uses its actual local values. A query
handler receives the current state and, for an index request, its admitted static
bound. Its returned sample replaces the original query or corresponding receive;
its returned state feeds the next handler. Handler bodies retain their scoped
control, effects and failure behavior.

The construction pass carries the complete state vector through affected loops,
completion and final return, including zero-slot state with ordered handler calls.
Custom adapters call the selected prepared function through ordinary `func.call`,
borrowing the current runtime scope and retaining its returned or stopped outcome.
They reorder only the query result ABI. Checked helper substitution subsequently
expands those calls without creating a frame or charging a helper return.
Dynamic occurrence coordinates remain explicit adapter operands;
custom bodies absorb only what they explicitly compute and observe.

Construction and codec signatures expose only logical data ports: the first
function argument is the borrowed scope and its sole result is an outcome carrying
the data results. Mathematical functions and outlined control bodies are not
ordinary handler targets. Conditional codec finalization uses `exec.test` with
closed child scopes; only the taken arm calls the selected method. Each arm
retains charged completion, including an empty untaken arm. The untaken write
arm produces empty bytes. Independent checking compares the actual decision,
captures, handler call, arm completion and return, as well as byte-slice offsets.

Projection metadata records the selected plan, root kind, ordered state types,
helper symbols, the sorted removed-service set and resulting action map.
Every original query action retains its original service input index; only
queries selected by those indices may disappear. Retained service names keep
their original identities while ingress positions account for removed ports. The source-relative
checker independently checks those records, factory/start operands, handler
bodies, message grouping and every state successor. A same-typed value cannot
replace the selected successor. Construction also bounds repeated handler
expansion before generating adapters.

## Record transport

A selected record codec transforms typed prover-to-verifier transport after
transcript construction. It preserves the ordered mathematical message and
query evidence. Each source message has matching encode, receive and decode
rules, plus an optional wire rule. Challenge deliveries have no record payload.
Rules operate on the full logical payload, whose native leaves remain ordered.
Only total mathematical calculations may separate leaves when grouping them.

The verifier executes receive on its current Record and original proof, slices
the returned ranges from that same proof, observes those chunks through the wire
rule if selected, decodes them, then invokes the mathematical handlers on the
actual decoded values. The prover encodes its actual message and executes the
same selected wire and mathematical handlers in order. These handlers form a
contiguous sequence; unrelated local calls and service queries cannot interrupt
it. Verifier calculations that lay between the original leaves follow the
observations; only total calculations may be crossed. Range selection may be
noncontiguous: a round's two chunks can come from separate `L[]` and `R[]`
regions. Future messages are decoded only at their own occurrences.

Record initialization follows root state initialization and start, once per
participant even with no messages or zero loop trips. It receives only its
selected actual shared original inputs. Every protocol loop carries Record
separately after transcript state. The verifier also captures the original proof
through isolated loop regions. Record versions, proof ingress, ranges, chunks
and final encoded bytes are internal codec values. Ordinary calculations,
loop bounds, guards and public outputs cannot consume them. Decoded payloads
and the checked transcript-state successors cross that boundary.

Before each successful return, the prover calls write on the current Record;
the verifier calls finish on the current Record and original proof. Conditional
completion invokes its finalizer only on the taken branch. Its untaken prover
branch returns an unused empty Bytes placeholder. Copyable state and bytes do
not acquire affine continuation slots. Earlier stops skip finalization. Finish
runs even when the mathematical result is false; its framing failure precedes
the Host's Boolean rejection. Finalization can precede pure data calculations
outlined for the return, but no later record or transcript step is allowed.
The Host publishes the prover's internal Bytes result only after successful
return and cleanup. Record never becomes an application result.

The compiler independently compares the transport transformation with its
transcript-constructed input, including retained calculations, helper bodies,
SSA operands, metadata and exits. Runtime admission checks the actual executable
codec sequence and internal-value boundary, then exposes its checked logical
messages to the transcript checker. That temporary admission view is not an
executable program. Both roles execute ordinary Local functions through the
same Runner; the Host dispatches neither protocol names nor codec names.

Record selection emits raw proof bytes without native headers or message frames.
The codec's finish method owns EOF and record coverage. Admission checks wiring
and authority, not injectivity, complete byte coverage, agreement between
encoded chunks and selected ranges, or correctness of an external parser.

## Transcript state and occurrence identity

In the installed native construction, each role owns a distinct affine transcript capability.
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

Each inserted native transition belongs to an ordinary scoped `func.func`.
Its admitted execution steps contain only coordinate construction, the
`exec.apply` transition, exact return payload and admitted storage releases.
Actual CFG branches dispatch each returned or stopped outcome. Source helpers
package their return with `exec.returned`; native lowering introduces the
charged root completion. Projection admission and the independent construction
checker read those actual CFG associations rather than trusting helper names. A UniformIndex helper additionally begins with exactly one
`index.constant` whose parameter is the event's bound and whose result is the
transition's bound operand. The helper executes at one static participant site per role;
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
chain from its mapped internal transcript input to its mapped internal result.
Native adapters use the listed native-origin operations. Custom adapters execute
their selected ordinary Local bodies, including explicit managed transitions;
the construction checker compares those bodies and their operands with the
prepared source. No extra adapter, alternate state root, dropped successor or
native-origin operation elsewhere is admitted. An occurrence-list match alone
is insufficient to establish the actual transcript sequence. Invocation binding
records absorption at managed initialization; it does not establish that a
custom body uses the state to sample a challenge or samples uniformly.

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

The additional Merlin suites
`merlin3.baby-bear.ext4-binomial11.rejection31le/0` and
`merlin3.goldilocks.ext2-binomial7.rejection64le/0` use Merlin 3 with domain
`zkc.artifact/0`. Initialization appends `suite` with the complete suite identity
before `binding` with the canonical invocation root. Existing suite bytes are
unchanged. Message and request labels follow the ordinary managed construction.
Each field draw requests 64-byte `challenge` blocks and fills the ascending
extension coordinates using the bounded rejection decoder in
[native services](../runtime/services.md#uniformindex-realization).
The suites also provide the existing power-of-two `UniformIndex` transition.
These are zkc byte constructions; selecting the same field as another system
does not imply transcript or proof-format compatibility.

For iterated construction, dynamic coordinates are explicit semantic inputs to
the observation/challenge operation. Optimization preserves those inputs;
a future transformation that peels a loop must substitute the induction value
and supply the required correspondence, rather than infer an origin from a changed
runtime frame. The current iterated admission retains the original loop structure.

Explicit [external construction data](../realization/external-constructions.md)
keeps its separate contract. Its copyable Monero/OpenVM states are checked data,
not live affine capability snapshots. Its exact upstream inputs do not acquire
zkc transcript prefixes. Trial copies consume actual work; their reachability,
publication and live witness check remain obligations of the authored program
and host.

## UniformIndex transitions

A selected `index` query becomes `transcript.native.indexed.index`:

```text
(Transcript<T>, index bound, indices) -> (index, Transcript<T>)
```

It requires the suite fact `IndexTranscript(T)`; the installed suites with that
fact are `merlin3.koala-bear.ext8-binomial3.rejection31le/0`,
`merlin3.baby-bear.ext4-binomial11.rejection31le/0`,
`merlin3.goldilocks.ext2-binomial7.rejection64le/0`,
`hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0` and
`hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0`. The bound must be
a power of two from 1 through 2^63; otherwise the transition refuses before
consuming the state. Otherwise it consumes the state and, in order:

1. absorbs the dynamic occurrence bytes under the suite's `origin` label;
2. absorbs the bound as eight little-endian bytes under the label `bound`;
3. squeezes 64 bytes under the label `index`;
4. returns the [UniformIndex sample](../runtime/services.md#uniformindex-realization)
   of those bytes and the successor state.

Both roles derive the same sample at the same ordered occurrence: the validator
replaces its query and the producer replaces its receive of that delivery, after
which both observe the erased delivery as an ordinary message occurrence. The
bound is part of the deployment and of the transcript prefix before the squeeze.
Field challenges and index transitions are separated by the occurrence's
service method (`draw` or `index`), which every admission path checks against the
transition contract, and by their distinct static labels. The exact-uniformity
statement is conditional on uniform squeeze bytes; this construction supplies no
random-oracle or Fiat–Shamir theorem.

## Native hash-chain suites

A hash-chain suite is an installed native transcript suite whose state is one
full digest of a byte hash `H` with 32-byte outputs. It realizes the same
operations as the other installed suites: the `binding` initialization, labelled
absorption, and 64-byte requests that the field and UniformIndex samplers
decode. Its name has the form `hash-chain.<hash>.<challenge field>.<decoder>/0`,
so another byte hash, such as SHA-256 or BLAKE2s-256, is a further installed
instance with its own identity rather than a parameter of an existing one.

| Suite | `H` | Challenge field | Field decoder | `IndexTranscript` |
|---|---|---|---|---|
| `hash-chain.keccak256.bls12-381.fr64be/0` | Keccak-256 | `bls12-381.fr` | `fr64be` | no |
| `hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0` | Keccak-256 | `koala-bear.ext4-binomial3` | `rejection31le` | yes |
| `hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0` | Keccak-256 | `koala-bear.ext8-binomial3` | `rejection31le` | yes |

Keccak-256 is the original Keccak submission's 256-bit instance (rate 136 bytes,
padding byte `0x01`), as used by Ethereum, not FIPS 202 SHA3-256.

### Encoding

Every absorbed event and every request is one frame:

```text
frame(kind, label, data) = kind:u8 ‖ |label|:u64be ‖ label ‖ |data|:u64be ‖ data
```

with kind 0 for fixed domain data, 1 for a message and 2 for a request. This is
the framing of the installed Spongefish suite. A frame determines its own length,
so a concatenation of frames parses uniquely, and a message never equals a
request with the same label and data. Each primitive input begins with one of
three role tags:

```text
t_bind    = "zkc.hash-chain.bind/0"    ‖ 0x00
t_absorb  = "zkc.hash-chain.absorb/0"  ‖ 0x00
t_request = "zkc.hash-chain.request/0" ‖ 0x00
```

No tag is a prefix of another. The primitive inputs are:

```text
s_0 = H(t_bind ‖ frame(0, "domain", "zkc.artifact/0") ‖ frame(0, "suite", suite)
           ‖ frame(1, "binding", root))
absorb(label, data):  s_{j+1} = H(t_absorb ‖ s_j ‖ frame(1, label, data))
request(label, n):    r = frame(2, label, n:u64be)
                      answer = (B_0 ‖ B_1 ‖ …)[0, n),  B_k = H(t_request ‖ s_j ‖ r ‖ k:u64be)
                      s_{j+1} = H(t_absorb ‖ s_j ‖ r)
```

`suite` is the suite's UTF-8 name and `root` the full canonical invocation root
of [transcript state](#transcript-state-and-occurrence-identity). A request
answer longer than one digest is the concatenation of counter blocks, truncated
to `n` bytes. A request is also an event: its frame advances the state, so two
consecutive requests with no message between them have different answers.

The native transitions map onto these operations exactly as for the other
suites: an observation absorbs `("origin", occurrence)` and then
`("value", canonical frame)`; a field challenge absorbs `("origin",
occurrence)` and then makes the `("challenge", 64)` requests its decoder needs; a
[UniformIndex transition](#uniformindex-transitions) absorbs `("origin",
occurrence)` and `("bound", bound:u64le)` and makes one `("index", 64)` request.
The managed source methods use the source label in place of the occurrence.

### Decoders

- `fr64be` reads one 64-byte answer as a big-endian integer and reduces it
  modulo the BLS12-381 scalar order `r`. The result is within statistical
  distance `r/2^512` of uniform; it is not an exact draw.
- `rejection31le` reads each 64-byte answer as sixteen little-endian 32-bit
  words, clears the top bit of each and accepts a word below the KoalaBear
  modulus `p` as the next coordinate, in basis order. It stops when the suite's
  extension degree is filled (four coordinates for quartic, eight for octic),
  and stops with `exhausted:challenge-rejection-limit`
  after sixteen answers. Rejected words are never reduced modulo `p`. Given
  uniform answers, an accepted value is exactly uniform on the named extension.
- The UniformIndex sampler is the
  [installed power-of-two sampler](../runtime/services.md#uniformindex-realization)
  applied to the `index` answer.

### Serialization and the history oracle

Each primitive input parses uniquely into its role, the 32-byte state where
present, one frame, and the counter of a request block. The state after a history
is therefore an injective function of the suite, the binding root and the
ordered events, including earlier requests, except where two distinct inputs of
`H` give the same digest. The occurrence of each request is recoverable from the
state: every native or managed request follows the absorption of its
occurrence or label. Distinct reachable transcript queries thus reach distinct
primitive inputs outside a collision of `H`, and no request answer shares an
input with a state, because their tags differ.

Modelling `H` as a random oracle, the suite reduces to the random oracle on
transcript histories up to one bad event in the joint primitive-query trace of
the adversary and the verifier, in call order: a *collision*, where two distinct
chain inputs give the same state, or a *prediction*, where a fresh call that
generates a state returns a value that an earlier call already used as a state
input. With `q` adversary calls and `V` verifier calls, initialization
included, the probability of that event is about `(q + V)^2 / 2^256`. A direct
query at an unreachable state is answered by the simulator of the reduction and
is not a bad event. The reduction is stated per security property, with an
adversary translation and its query-cost relation.

The suite's tags separate its inputs from those of the Keccak-256 row
commitments, whose inputs begin with `zkc.oracle.keccak256.` tags. Explicit
`hash.keccak256` calls on authored bytes share the same primitive; any security
statement covers them in the same joint primitive-query trace.

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
See the [observation requirements](../../compiler/pipeline.md#analysis-boundary).
Their preservation does not require implementing the future affine analyzer.

Readers admit only this proof contract. Native structural checking does not
inherit an independent Lean source interpreter, a proof about another carrier,
or a Fiat–Shamir security theorem.

## Native occurrence encoding

An indexed native kernel carries the bounded static template:

```text
["zkc.native-origin-template/0", entry, [step, ...], [], event]
event = ["query", protocol, site, service_port, service_contract, method, owner]
      | ["message", protocol, site, schema, sender, receiver]
      | ["start", original_caller_protocol, original_apply_site]
step = ["apply", original_caller_protocol, original_apply_site]
     | ["repeat", original_protocol, original_repeat_site]
```

The tree uses the canonical logical encoding: tag 0 followed by a u64
little-endian UTF-8 byte count and string bytes, or tag 1 followed by a u64
little-endian element count and recursively encoded elements. An application
step precedes its callee's steps; a repeat step precedes every event in its body.
The path excludes the final event. Roles reflect static application substitution.
For a child start the path excludes that child's apply step; it records the
caller's enclosing applications and repeats. The following child events include
the apply step. Start origins identify ordinary construction calls and do not
select a transcript kernel or prescribe bytes to absorb.
Service ports are `input_N`, with the original input index as a canonical u64
decimal. A message schema is its original source site. The checked wire map
connects it to the prepared site without using generated names in the origin.

Names are nonempty printable ASCII (bytes 33 through 126), at most 128 bytes.
Paths have at most 64 steps. The encoded template is at most 2048 bytes and is
carried as exactly one lowercase, even-length hex attribute, at most 4096
characters. Its coordinate array must be empty. Unknown tags, alternate shapes,
noncanonical hex and trailing bytes refuse. Field challenges require query events
with method `draw`, UniformIndex transitions require query events with method
`index`, and observations require message events. These checks establish syntax, not source
correspondence or unique execution.

The dynamic operation takes an explicit `indices` value. Its entries are the
actual induction values of the enclosing repeats, outermost first, with one
entry per `repeat` step. The final absorbed bytes encode:

```text
["zkc.native-origin/0", entry, [step, ...], [iteration_decimal, ...], event]
```

Each iteration is a canonical unsigned 64-bit decimal string. The vector has
at most 64 entries; the final encoding is bounded by 4096 bytes. A length
mismatch refuses. The operation neither reads runtime frame names nor infers
coordinates from dispatch order. Query labels still name the source validator's
draw when executed by the producer. Zero trips perform no body transition.
The existing suite framing absorbs the dynamic bytes under its static `origin`
label, so dynamic instances introduce no dynamically interned Merlin labels.

The generated contracts are `transcript.native.indexed.challenge`,
`transcript.native.indexed.index` and `transcript.native.indexed.observe.data`.
They retain the affine transcript, sampling/observation/history facets and
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
substituting or bypassing that state refuses. Copyable state values also cannot
appear in ordinary Local arguments, messages, loop captures or application
outputs. Unrelated values of the same type remain ordinary data.

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

## Native index blocks

`Random<F>.indices(N,Q)` is a source product request with two positive checked
u64 static naturals and one logical `Indices` result. Its source law is
`UniformIndex(N)^Q`, preserving order, exact Q and duplicates. General source
bounds need not be powers of two. `IndexBlockRandomness(F)` is a separate
service fact; a block is not a scalar BoundedIndex. Source and participant
queries carry method `indices`, two constant index inputs N/Q and one indices
output. Generic specialization independently checks positivity.

Native selection restricts N/Q to the domain in the
[native block format](../formats/native-index-block.md). It uses explicit
`draws` pairs to select each source query and the exact value delivered to the
producer, in source order. The required twelfth native policy field, `gates`,
is an array of `[query_site, canonical_decimal_bits]` pairs, unique by site,
with bits in [0,64]. Unknown, unselected or nonblock sites refuse with
`native-proof-gate-selection`; malformed policy rows refuse with
`native-proof-policy`. An absent row selects the ungated block; a row with zero
selects a gated slot with canonical witness zero. There is one current strict
12-field `zkc.native-proof-policy/0`, including an explicit empty gates array;
old-length policies refuse. Difficulty never comes from runtime operands.
Selected native blocks use the direct native construction. Explicit custom
construction plans, including query handlers and record codecs, refuse with
`native-proof-index-block`; source query-handler declarations for blocks refuse
with `source.construction`. They do not gain the block contract from an annotation
or a native base selector.
Source-bound proof declarations currently select ungated blocks. Explicit gate
selection uses an authenticated native deployment policy until the source
interface represents that selection; a source-bound package cannot add gates
absent from its declaration.

The producer replaces the selected delivery receive with a typed bounded-search
helper and an actual `protocol.send` of its returned witness. The verifier
replaces the selected query with an actual `protocol.receive` followed by the
typed check helper. Both roles then perform the ordinary selected delivery
observation. These are ordinary scoped `exec.apply` calls through
`runtime.binding`; there is no special runner. A gate does not change the
source protocol's message list. Witness transport belongs to construction and
is not a transcript observation.

The current strict `zkc.native-proof-descriptor/0` has eight fields: tag, policy,
origin format, sequence, public bindings, messages, construction plan, witnesses.
An ungated sequence record is `["indices", origin, N, Q]`; a gated record is
`["gated-indices", origin, N, Q, b]`, with decimal strings. Each gated static
occurrence has one witness row `[origin, "gate." + query_site, "index",
"native.index/0"]`, in sequence order. Deployment wireSites includes
`[origin, witness_site]` in proof transport order. A source slot collision
refuses. Repeats reuse the static slot and supply their actual repeat
coordinates. Origins use source service, owner and occurrence paths, never
generated helper names.

Independent actual-body correspondence checks both search/check helper
signatures, bindings, parameter carriers, exact SSA use, state successors,
coordinates, witness schema/slot/peer and control order. Full candidate
comparison remains an additional check. The independent Rust deployment reader
must authenticate the descriptor, operation parameters and complete transport
slot coverage against the actual native program; a descriptor hash alone is
not source authority. Lean is an independently maintained pending consumer;
these native checks supply no formal grinding or compound-query theorem.
