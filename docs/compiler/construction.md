# Transcript construction

Proof compilation analyzes retained common source and applies a selected
construction to unsimplified participant mathematics. It stays within the
existing `participant` profile. [Construction](../spec/ir/construction.md)
owns exact occurrence, observation and state rules; [proof execution](../runtime/proofs.md)
explains the Host boundary.

## Placement and retained source

```text
common source + explicit construction policy
    → admit source occurrences and verifier dependencies
    → project unsimplified participants
    → construct role-local transcripts and check the actual candidate
    → simplify → exec → physical → participant programs
```

A common value denotes role components. Projection already specializes those
components and gives each receive its actual role-local value. Constructing
after projection permits explicit transcript states without introducing a
common disjoint-role assembly operation. Analyzing only optimized participants
would lose source draw selection and ordered work.

Retain the original source and independently recompute its occurrence view when
checking construction. The immutable construction map records original
interfaces and checked input/result/action substitutions. It locates operands
without replacing source-relative comparison. Maps are fixed before participant
simplification. Ordinary projection verification applies when no construction
map exists.

## Admission and checking

Source admission fixes entry, roles, acceptance, public bindings, suite and
selected validator service/draws. `selectNativeProofDraws` can resolve ordered
query/delivery occurrences when that service is explicit and the input draw list
is empty. It preserves original IR and returns a complete strict policy.
`NativeProofSelection` exposes this through the Entry compiler; explicit policy
callers retain exact occurrence selection.

Construction adds internal transcript input/results, removes the selected
validator service, and rewrites the admitted challenge deliveries. It introduces
no participant data ports. Hosts receive authorized public values for root
initialization and compare shared values with participant inputs.

An independent postcondition reads actual observations, challenge delivery,
state flow, loop coordinates, completion and retained declarations.
`checkNativeProof` composes that construction check with comparison of the whole
supplied candidate, including local bodies. [Verification](verification.md)
then checks lowering, executable bytes and deployment maps.

## Encoding and message semantics

The invocation root binds source/policy identity, ordered actual public values,
application context and applicable setup material. The complete canonical root
enters the suite under `binding`; its SHA-256 digest binds the proof header.
[Deployment formats](../spec/formats/proof.md) own exact bytes.

Occurrences encode original entry/call/repeat paths and source sites, with
dynamic induction coordinates. Generated names and diagnostic call paths do not
determine transcript bytes. A flat event descriptor plus retained SSA control
describes loop structure without a second executable graph.

Canonical receive decoding precedes observation. [Structured frames](../spec/formats/messages.md)
bind complete types, tags, lengths and payloads. Records, alternatives, numeric
tensors and sequences use the same typed codec. Copyability alone grants neither
wire permission nor cross-role availability. External byte formats need an
adapter preserving the bytes their construction observes.

## Authored transcripts

Authored hash-chain and duplex calls retain explicit immutable state values,
initialization, trial copies, updates and checks. Their
[external construction contract](../spec/realization/external-constructions.md)
owns primitive meaning. State metadata is validated but never hashed. Copying a
snapshot does not attest its history or reachability; every executed trial still
charges primitive work. Affine RNG and derived-transcript resources keep their
own custody rules.

The Host binds public context into the outer header. Authored code decides what
enters its cryptographic state: automatically hashing the zkc header would
change the authored algorithm. `binding_scope = "header"` states this limited
guarantee, and the CLI requires `--allow-header-only` acknowledgement. Admission
does not require every received message to be observed.

Byte words currently use eight bytes per index plus framing. They preserve
values without claiming upstream proof-wire compatibility. Bounded search and
early participant return use [ordinary control](control.md); retry remains an
explicit returned decision handled by the [attempt Host](../runtime/attempts.md).

## Evidence and extensions

[Public-coin views](public-coin.md) analyze a bounded verifier dependency profile.
Construction checking covers observation/state wiring; neither supplies a
Fiat–Shamir reduction, an entropy law or arbitrary authored-transcript security.
The [native validation map](../../tests/native.md) identifies flat, iterated,
structured, setup-backed and authored clients and their references.

A new delivery recipe or suite needs explicit admission, encoding, sampling and
failure contracts. A domain's presence in the kernel catalog does not extend a
construction's allow-list. See the [roadmap](../roadmap.md) for assurance work.
