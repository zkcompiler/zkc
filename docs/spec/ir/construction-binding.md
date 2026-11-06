# Checked construction binding

A construction binding view is a separate, requested structural judgment over
an original protocol and its actual constructed candidate. Execution admission,
source/candidate correspondence, verifier observation, and binding are different
checks. Refusing binding does not reinterpret an admitted executable program.

The checker first reuses native construction correspondence, including the
selected realization, message order, repeat coordinates, request domains, gate
witnesses and original acceptance result. It then inspects the actual selected
handlers. Provider names, dependency sets and declarations of intended coverage
are not evidence that a value reaches a hash input. In particular, arithmetic
such as `x - x` is not a canonical encoding of `x`.

## Closed profiles

- **Native history.** The ordinary installed native construction has no custom
  transition overrides. The existing independent helper-body checker establishes
  its exact indexed observations and query transitions. Public inputs, setup
  identities, source/configuration and invocation context enter through the
  installed host initialization contract. This last boundary is an explicit
  premise: the compiler does not inspect a host invocation that has not run.
- **Canonical hash history.** Local construction state is one full hash digest.
  Initializers, start handlers, message handlers and query handlers are admitted
  compositions of canonical byte encoders, concatenation and SHA-256 or Keccak.
  Each transition preserves the previous full digest and includes every required
  new input in order. Query transitions return the new digest and decode that
  same digest as the challenge. Exact challenge delivery may leave the state
  unchanged. All other messages, including terminal messages, must be observed.
  A grouped handler may omit an observation only when every selected leaf is
  an exact challenge delivery; a delivery cannot exempt adjacent prover data.
  Nonempty tags separate query transitions from non-query transitions; distinct
  tags may not be prefixes of one another. A fixed tag may be reused within
  either class. The actual program fixes the ordered logical type layout.
- **Explicit inputs.** A local copyable state stores data for a stateless query.
  The checker symbolically executes actual straight-line handlers and checks the
  complete canonical encoding supplied to the selected hash. Every public input
  and preceding prover message must occur in order. Equal encoded requests may
  intentionally share a challenge; no evolving-history judgment is attached.
  Messages after the final query remain outside query coverage. Original
  acceptance correspondence still applies; it does not establish their
  cryptographic authentication.

These are closed profiles, not recognition by library name. Unrecognized
control, arithmetic, lossy encodings, mutable resources, custom codecs, nested
construction resets and unproved omissions refuse the affected profile. The
history profile checks each transition parametrically, so protocol repeats do
not require trace expansion. Explicit-input execution initially requires a
nonrepeated event sequence. Other admitted executions retain no implied binding
judgment.

## Encoding and state interpretation

Use a bounded transient DAG derived from admitted scoped execution SSA. Calls
substitute actual data operands; a helper name alone grants no meaning.
Supported scalar field/group encoders have their installed exact canonical
encoding. Unsigned LEB128 is self-delimiting. Variable byte strings require the
canonical encoding of their actual length before their full bytes; concatenating
two unconstrained byte strings is not an encoding of the pair. Hashing a valid
encoding can replace it with a fixed-size digest only under the separately
reported collision premise. Reducing a digest into a field is a challenge
conversion, never an injective encoder or a full-digest state successor.

Binding reports identify the profile, full policy, checked realization and
source/candidate identities, ordered covered inputs/events, selected hash and
codec contracts, and external premises. Rechecking recomputes the complete view
from source and candidate. All formats remain at version 0. Reports cannot
supply missing evidence or grant execution authority.

No native check here proves collision resistance, a random-oracle theorem,
encoder injectivity, challenge uniformity, or the application's acceptance
predicate. Shared use of Keccak for transcript and Merkle hashing does not
supply independent random oracles. A formal consumer must interpret those
primitive and composition premises separately.

## API and report

`analyzeNativeProofBinding` accepts original IR, the supplied constructed
candidate, native proof policy, the requested profile, and independent math and
oracle realization selections. It checks the candidate before returning a
view. `checkNativeProofBinding` rederives and compares the complete view.
The CLI equivalents are:

```text
zkc-compile protocol-proof-binding SOURCE.mlir POLICY CANDIDATE.mlir --binding-profile=PROFILE
zkc-compile protocol-check-proof-binding SOURCE.mlir POLICY CANDIDATE.mlir REPORT.json --binding-profile=PROFILE
```

Profiles are `native-history`, `canonical-hash-history` and `explicit-input`.
The commands accept the existing independent mathematical and oracle selection
options. The binding view is a separate product, not an extra deployment field
or an execution fallback. A report contains:

- `format`, `profile`, exact `descriptor`, `source_sha256`, `candidate_sha256`;
- `mathematical_policy`, `oracle_policy`, complete checked `realization`;
- ordered `occurrences`, with actual origin, payload type, repeat depth, query
  domain/count/difficulty and reconstructed-request status;
- `primitive_inventory`, including complete installed binding arguments and
  signatures; logical role names do not separate underlying hash instances;
- `coverage` and named `premises`.

Source/candidate and original-acceptance correspondence are checked facts, not
external premises. Native history separately names installed host invocation
initialization among its premises; local profiles do not inherit that binding.

All three profiles report `terminal_outside_query`. For a branch-free entry it
is the ordered non-delivery message templates following the final selected
query template. The native-history and canonical-hash-history analyses derive
the structured generalization directly from the admitted immutable prepared
protocol function:

- Read each block sequentially, adding each non-delivery message to its pending
  set. A selected transcript query clears that set. Its exact draw delivery adds
  nothing. Unselected private service queries are outside the transcript
  inventory and do not clear it.
- Read every branch arm from the same incoming pending set. At the join take
  the union of the arms' outgoing sets, deduplicating shared incoming messages.
  A query clears only its current arm. Emit the result in static source event
  order, including arms in declaration order, never pointer or site-name order.
- Read each repeat body once as a syntactic template, regardless of the runtime
  trip count. Do not enumerate branch combinations or dynamic occurrences.
- A child construction start must match its admitted start event, including its
  input types. It is an invocation boundary, not a message or a query: it neither
  adds to nor clears the pending set. This structural treatment does not admit
  child resets into a binding profile that otherwise refuses them. Root
  initialization is handled by the profile, not as a source message event.

Thus `m0; if {q; delivery} else {m1}; m2` reports `m0,m1,m2`. If both arms query,
neither retains `m0`. A later unconditional query clears the entire joined set.
Branch-free report bytes retain the existing suffix meaning.

The private helper `summarizeConstructionTerminal` borrows the prepared
`protocol.func`, actual admitted events and selected query/delivery pairs.
The caller retains the source owner through analysis, separately from any
replaced or mutated candidate. Source formation and independent event/draw
admission remain prerequisites: a producer report is never a source of control
structure or authority. The helper checks complete one-to-one coverage in
static order of source exchanges, selected queries and starts, with matching
site, event kind, payload or start inputs, and repeat depth. Missing, extra,
duplicate, reordered or mismatched events refuse with
`construction-binding-coverage`. Missing, duplicate or wrong-kind draw endpoints
also refuse. Exact query/delivery value and control association remains part of
independent admission. Unexpanded protocol applications also refuse.

This summary has its own ceiling of 100,000 charged work units and 64 nested
regions. The private budget argument can reduce that ceiling for callers and
capacity controls; it cannot raise it. Work includes event/draw ingestion,
site comparisons, index insertion and movement, operation/region traversal,
pending-set growth and copying, clearing, unions and terminal materialization.
Exhaustion returns `construction-binding-capacity`, with no partial summary or
report. The analysis holds only borrowed native references and transient event
indices; it does not create another AST or execute selectors.

The explicit-input profile still requires a nonrepeated sequence and refuses
prepared Protocol branches with `construction-binding-selected-control`,
including event-free arms. There is no explicit-state encoding join rule.
This internal history-summary support does not enable the public selected-proof
pipeline: its global selected-control refusal guards remain until the other
construction consumers migrate.

Absorption into a final history state is not coverage by a subsequent query or
external authentication of that final state. The report is not path-complete
for early completion, a zero-trip execution theorem, or a statement that all
listed templates execute. A syntactically later query can clear a message even
when runtime completion would prevent reaching that query. Actual repeat
coordinates and the continuing trace determine dynamic occurrences. History
profiles separately check transition templates, including terminal messages;
this report adds no runtime acceptance, formal correspondence or security
theorem.

Local coverage contains `hash`, ordered `transitions`, `encoding_graph` and
`terminal_outside_query`. Transitions identify the actual digest expression,
ordered complete input names, literal domain tag and whether they are queries.
The DAG records typed inputs, literal integers/bytes, canonical encoders,
concatenation, lengths, full hashes and challenge conversions. DAG integers are
local IDs, not source identities; the complete source/candidate digests fix the
subject. Local profiles admit field challenges through big- or
little-endian modular reduction, with its exact distribution as an external
premise. They do not claim that modular reduction is uniform. Native profiles
retain the installed field/scalar-index/product-index law and gate framing.

Work is bounded by one million charged steps/edges/encoding bytes, 65,536 DAG
nodes, 1,024 helper inputs, 64 nested calls or encoding levels, 4,096-byte names
and literals, 16 MiB subject identities and an 8 MiB complete report. Capacity
refusal is not missing coverage. Unknown operations refuse even when their
results are ignored, because their stopping/effect behavior has no selected
encoding rule.

## Research basis

The separation between encoders and challenge decoders follows the
[CFRG Fiat–Shamir draft](https://www.ietf.org/ietf-ftp/internet-drafts/draft-irtf-cfrg-fiat-shamir-03.html):
encoding and distribution-preserving decoding have different obligations.
The [duplex-sponge construction](https://eprint.iacr.org/2025/536) motivates
checking actual state transitions rather than attaching a history theorem to
an arbitrary deterministic hash function. This implementation does not claim
to discharge that paper's assumptions.
