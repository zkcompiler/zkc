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
  Messages after the final query remain outside that query's coverage and are
  reported as such. Original acceptance correspondence still applies; it does
  not establish their cryptographic authentication.

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

Local coverage contains `hash`, ordered `transitions`, `encoding_graph` and
`terminal_outside_query`. Transitions identify the actual digest expression,
ordered complete input names, literal domain tag and whether they are queries.
The DAG records typed inputs, literal integers/bytes, canonical encoders,
concatenation, lengths, full hashes and challenge conversions. DAG integers are
local IDs, not source identities; the complete source/candidate digests fix the
subject. Local profiles currently admit field challenges through big- or
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
