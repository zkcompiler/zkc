# Transcript construction

This is a native contract. [Construction](construction.md),
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

Explicit [external construction data](../realization/external-constructions.md)
keeps its separate contract. Its copyable Monero/OpenVM states are checked data,
not live affine capability snapshots. Its exact upstream inputs do not acquire
zkc transcript prefixes. Trial copies consume actual work; their reachability,
publication and live witness check remain obligations of the authored program
and host.

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
["zkc.native-origin/0", entry, [step, ...], [iteration_decimal, ...], event]
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
