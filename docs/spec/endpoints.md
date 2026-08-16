# zkc Endpoints

Status: **canonical OIR endpoint semantics.** Companion to `kernel.md`,
`carrier.md`, and `boundaries.md`. This document owns the admitted endpoint
frames and the reserved endpoint contracts. Backend realization and its
evidence contract are specified separately in `boundaries.md` §6.

## 1. What an endpoint program is

An OIR artifact is the handled endpoint form of one sealed PIR protocol:

```text
OIRArtifact = endpoint program + embedded source provenance + sealed-source id
```

The program is not a backend recipe. Each kernel challenge effect becomes one
typed, counted squeeze, and the spine's semantic events become protected OIR
operations. Projection records those routes and proves `COV_realized`; it does
not run a sponge, manufacture challenge values, or select a deployment target.

The endpoint-kind vocabulary is closed:

| Endpoint kind | Contract | Meaning |
|---|---|---|
| `verifier` | admitted | consumes a statement and proof, then returns accept or a named reject class |
| `prover_skeleton` | admitted | consumes a statement and opaque witness handles, orchestrates digest-authorized holes, and emits proof bytes |
| `verifier_gadget` | reserved | recursive or in-circuit realization of verifier semantics under the contract in §5.1 |

Endpoint names never identify a backend, field library, hash implementation,
deployment environment, or proving-system recipe.

Two rules apply to every endpoint:

1. **Protocol effects are protected.** Transcript, proof-stream,
   public-binding, check, artifact-verification, and terminal events may not be
   deleted, reordered, duplicated, merged, or floated across dependencies
   without explicit equivalence and coverage evidence.
2. **Opaque calls have no hidden protocol effects.** `check_call` and
   `hole_call` are digest-authorized components with declared typed boundaries.
   They may not secretly read or write the proof stream, absorb or squeeze the
   transcript, bind public values, verify artifacts, or alter claim routes.
   Those effects must remain explicit OIR events.

## 2. Identity, ABI, and linear resources

Canonical OIR has identity
`SHA256("zkc/oir\n" || canonical_bytes)`. The stored id is excluded from
its own preimage. Every executor and every attributable derived view must
recompute it and refuse a mismatch with zkc-E170 before reading program
semantics. Raw canonical/id translation only mints an id; it is not artifact
acceptance.

An `oir.program` carries:

- ordered `statement_labels`, identifying its public statement arguments;
- `param_digests`, which pin the construction entries an execution profile
  must supply before the first transcript event;
- a class-to-codec map baked from the sealed construction profile;
- on `prover_skeleton` only, ordered `(label, handle class)`
  `witness_labels` and `counterparty` coverage rows that are exhaustive on
  successful projection; and
- the endpoint body.

`param_digests` are artifact attributes, not caller-provided block arguments.
The verifier block arguments are statement values followed by the proof-stream
cursor. The prover block arguments are statement values, one
`!oir.handle<class>` per `witness_labels` entry, then the write-stream cursor.
Labels are endpoint ABI and enter OIR identity even though author labels do not
enter PIR identity.

The complete entry signature is authenticated by OIR identity. Canonical
encoding MUST either carry that signature or determine it uniquely from the
identified artifact. Validation requires the exact argument count, order,
classes, origins, handle classes, and terminal stream position for the selected
endpoint frame; an extra, missing, unlabelled, or otherwise unreconstructible
argument makes the artifact invalid.

Three resource types are linear:

- `!oir.sponge`: transcript state, created once and closed by `decide` or
  `finish`;
- `!oir.stream`: read or write cursor, closed by `expect_end` or `end_stream`;
- `!oir.handle<class>`: opaque prover-private state, threaded through holes and
  consumed before `finish`.

Every state has exactly one use. Handles are never wire-encoded, absorbed,
statement-bound, or exposed to pure arithmetic.

The container verifier requires exactly one transcript initializer and one
frame-appropriate stream terminator. `decide` or `finish` is final. Every hole
result has at least one use, and every handle chain ends in a consuming hole
before `finish`.

Values have a semantic class and a closed origin:

```text
public | pinned | wire | sampled | derived | hole
```

`hole` occurs only on prover-hole results. Origins preserve channel integrity:
a sampled challenge is not written directly, and a wire value cannot appear in
a prover program.

Canonical OIR has no `oir.project` or challenge-producing `oir.derive` escape
hatch. Projection or derivation of a PIR challenge capability preserves the
source squeeze and its provenance; verifier-local pure algebra may produce a
`derived` value but never creates another transcript query or sampled value.
Imported-challenge composition requires an explicit authenticated route or
artifact-verification effect and fails closed when that authority is absent.

## 3. OIR event families

| Family | Events | Rule |
|---|---|---|
| transcript | `transcript_init`, `absorb`, `squeeze` | one linear sponge chain in sealed-spine order |
| verifier proof stream | `read`, `expect_end` | canonical-or-reject decode and mandatory EOF |
| prover proof stream | `write`, `end_stream` | canonical encoding and mandatory completion |
| pure computation | `constant`, field/group algebra | freely optimizable subject to SSA dependencies |
| verifier checks | `public_bind`, `assert_eq`, `check_call`, `decide` | protected effects; opaque execution is profile-supplied |
| prover computation | `hole_call`, `finish` | digest-authorized fills and no prover verdict |
| artifact verification | reserved `artifact_verify` event | bounded imported-artifact verification under §3.1 |

Every squeeze is self-describing: payload class, exact count (`1` scalar or
`2..2^20` vector), non-empty domain, sampling rule, and exact positive sample
space. A vector is one counted protocol effect and produces one sampled value;
it is not an unrolled sequence of scalar squeezes. These fields declare a
schedule. They do not prove that a construction ran or that its outputs agree
with another implementation.

The canonical spelling requires `uniform` exactly for count `1` and
`uniform_independent` exactly for counts `2..2^20`. Projection emits that form.
Standalone OIR verification rejects every other rule/count pairing.

An opaque `check_call` carries a human-readable contract id for diagnostics
and the exact CheckContract content digest as its sole dispatch authority. The
digest pins proposition identity and ABI, not executable-adapter correctness.

### 3.1 Reserved bounded artifact verification

Future recursion and aggregation require artifact verification to remain a
first-class protected endpoint effect. The first admissible form is bounded
and statically known. It must bind:

```text
known child artifact identity and endpoint kind
known verifier-semantics reference
verifier-key digest or explicit key binding
child protocol digest
child relation-contract digest
child statement/public-IO digest or binding
child artifact-ABI digest when the artifact has a distinct ABI
proof slots consumed by the child verifier
explicit child assumptions and parent-visible claim route
covered parent claim ids
source-event provenance and failure behavior
```

It may eventually be represented by a dedicated operation or by a constrained
`check_call`, but either form must carry artifact-verification coverage and
must reach the endpoint decision. Child assumptions, exports, residuals, and
carried obligations may not disappear at the boundary; they are discharged by
the child-verifier semantics or lifted into the parent-visible route surface.

An artifact-verification event discharges a parent claim only when its verifier
semantics and key binding, child endpoint kind, artifact ABI, protocol,
relation contract, statement/public IO, and assumption set exactly match the
claim descriptor or admitted route policy; the event reaches the endpoint
decision; projection covers the source artifact-verification event; and the
parent route surface names the discharged claim. If any required fact is
missing, the child artifact may enter only through an explicit assumption,
export, or residual route. Conformance evidence may support that route, but it
cannot create the route or supply a missing match.

This contract is reserved: it becomes usable only through a versioned carrier
form, projection rule, execution rule, and conformance surface that preserve all
facts above. An unversioned or incomplete form fails closed. Dynamic child
selection, universal recursion, verifier-key-set policy languages, and
recursive schedule optimization require separate admitted extensions; none is
implied by bounded artifact verification.

## 4. Reference execution and conformance profiles

A verifier execution accepts an authenticated OIR artifact, statement values,
and adversarial proof bytes, then returns `accept` or a named reject class. A
prover execution accepts an authenticated OIR artifact, statement values, and
the declared opaque inputs, then returns proof bytes without an accept verdict.
Before either execution reads endpoint semantics, it authenticates OIR identity
and every profile or supplier digest the artifact pins.

An attributable execution record MUST expose enough deterministic observables
to check the endpoint contract: the ordered event log, transcript log or
semantic digest, proof-ABI log, public-binding log, opaque-call results, and
terminal record. Prover records additionally satisfy §6.3. A reference executor
claimed as Tier-2 authority supplies these observables; a smaller diagnostic API
does not weaken the conformance contract.

Execution is profile-scoped. A conformance profile names exact codec, sponge,
sampling, check, and hole suppliers by the content digests they claim to
realize. Digest agreement authenticates supplier selection and ABI, not the
correctness of supplier code. Missing or mismatched suppliers are profile
incompatibilities rather than proof verdicts.

Normative reject classes, which an implementation may refine but not collapse,
are:

```text
abi_decode_failure
abi_validation_failure
proof_trailing_data
public_binding_failure
transcript_failure
check_failure
artifact_verification_failure       # reserved event category
route_policy_failure                # reserved route surface
internal_invalid_artifact
```

Missing codecs, sponges, sampling rules, check suppliers, or hole suppliers
are profile incompatibilities: “I cannot judge/fill this” is never reported as
“this proof is false.” Stable E400-series diagnostics name the missing or
mismatched supplier and executing profile.

Tier-2 conformance requires positive and negative vectors, identity refusal,
canonical decoding and EOF behavior, deterministic event and transcript
observables, and the independent oracle or implementation named by each parity
claim. Such evidence is scoped to its exact profile and vectors. Challenge
noninterference remains a separate Binding-Lemma conformance target, and
ecosystem wire vectors remain external evidence rather than facts derived by
this specification.

Profiles claiming alignment with a standardized duplex-sponge Fiat-Shamir
track SHOULD replay that ecosystem's test vectors against an external oracle.

## 5. Reserved endpoint and optimization concepts

### 5.1 `verifier_gadget`

A verifier gadget would express the same verifier endpoint as logic suitable
for recursive or in-circuit use. It is not a backend selection; that choice
belongs to `oir-realize`. A future gadget must
preserve the native verifier's proof language, public binding, transcript,
artifact-verification behavior, claim routes, and decision, or expose each
difference as a checked realization-time equivalence obligation.

The spelling is reserved so unknown kinds fail distinctly. No artifact may
claim this endpoint kind until a versioned carrier form and its preservation
judgments are admitted. Reserved does not mean partially supported.

### 5.2 Schedule and fast paths

Scheduling, kernel selection, backend lowering, and fast-path replacement live
below canonical OIR. Their preservation contract, including
`FastPathCoverage`, is in `boundaries.md` §6. They cannot add endpoint semantics
that canonical OIR did not contain.

## 6. The prover endpoint

### 6.1 Projection and duality

An admitted `prover_skeleton` is the second projection of the same sealed spine
as the verifier and is derived by `pir-project`. Standalone OIR may be authored
and structurally validated, but that validation does not establish projector
origin, source-obligation exhaustiveness, or `COV_realized`. Projection
consumes the unchanged `COV_obl` set and proves its own `COV_realized`:

- verifier `read` corresponds to prover `write`, and counted `read_vec` to
  counted `write_vec`, with the same class, count, and source
  position;
- both endpoints absorb the same material and perform the same typed, counted
  squeezes;
- `expect_end` corresponds to `end_stream`, and `decide` to `finish`;
- verifier-local checks are listed exhaustively in prover `counterparty` rows
  emitted by projection.

The closed discharge mapping keeps `const+absorb`, `arg+absorb`, and both
squeeze forms identical; maps `read+absorb` and `read` to `write`; and records
`assert_eq` and `check_call` as counterparty rows. These rows are endpoint
realization data, not seal-time route-class declarations.

The E239 duality check re-reads the emitted program position by position and
refuses a mismatch. This establishes orchestration correspondence, not theorem
security or honest-prover completeness.

A validator with only an OIR artifact MUST check the `counterparty` row schema,
uniqueness, and internal references, but it cannot authenticate coverage against
the source obligation set. Exhaustiveness MUST be checked in a validation
context that has both the sealed source PIR and the OIR artifact; an arbitrary
source-free OIR artifact is not self-authenticating evidence of that property.

### 6.2 Construction routes and holes

PIR construction routes are identity-bearing protocol content. They declare
opaque witness payloads and a named set of hole instances. Each instance binds
one exact HoleContract, its static and semantic parameters, and an ordered
operand list. The closed semantic reference set contains statement bindings,
earlier proof-slot values, sampled challenges, pinned constants, anchored
material identified by a source claim's anchor digest, witness payloads, and
earlier hole value or handle results. Scalar and vector references retain their
declared class and count.

Each routed proof slot is supplied by a hole value result, a route-declared
pure expression over that same closed reference set, a statement binding, or a
pinned constant. Seal checks closed shape, exact parameter and segment
agreement, all classes and counts, anchor and reference resolution,
HoleContract citation, and acyclicity. Prover projection additionally requires
route totality and materializes each dependency before its first consumer.

The admitted hole kinds are `commit`, `extend`, `evaluate`, `fold`, `open`, and
`pow_search`; the typed signature, not the kind label, is authority. A hole has
no hidden protocol effects. Only `pow_search` may inspect the sponge, and then
only as a state-identical read-only peek. Its contract MUST pin the search
predicate to the framing of the corresponding nonce-absorb event and the
derivation of the following proof-of-work squeeze. A conforming fill searches
in canonical order and returns the least valid witness, making the endpoint
deterministic. Hole outputs reach the transcript or wire solely through
explicit spine operations.

These checks establish structural route well-formedness, not algebraic
correctness. A structurally valid but mis-wired route may emit only proofs that
the verifier rejects; route declarations carry no completeness theorem.

HoleContract value segments may be scalar or counted vectors. Handle segments,
anchored-material operands, static parameters, and digest-shaped semantic
parameters are all part of the contract ABI and MUST be supplied exactly. A
supplier receives only the declared operands and parameters and may return only
the declared results.

### 6.3 Execution boundary

Hole suppliers are selected by HoleContract content digest. A missing supplier
is E407; a supplier error or result-arity mismatch is an E408 execution defect,
and later explicit wire operations enforce their own range and canonical
encoding rules. The prover itself returns no accept verdict:
success means only that it emitted these bytes and challenge values. Acceptance
belongs to a verifier.

Every prover codec supplier MUST provide canonical encoding and satisfy
`decodeWire(encodeWire(v)) = v` for every in-range value. Thus a successful
prover run emits a canonical proof stream by construction.

A run record MUST bind the sealed PIR identity, prover OIR identity, execution
profile and supplier digests, and the content digests of every opaque witness
payload and anchored-material input consumed by the run. The record attributes
only the observable boundary behavior; it does not attest the supplier's
internal algebra or establish relation satisfaction.

### 6.4 Equivalence evidence and nonclaims

For every concrete filled skeleton, its conformance record MUST demonstrate:

1. the emitted bytes decode as the verifier endpoint of the same seal expects;
2. prover and verifier transcript schedules correspond;
3. the zkc verifier accepts the assembled spine wire under the recorded inputs;
4. every opaque input and supplier is bound to that exact run as specified in
   §6.3; and
5. when counterpart conformance is claimed, the named counterpart verifier
   accepts, with any serialization adapter exposed as a residual evidence
   boundary.

For every admitted hole kind in a conformance profile, negative evidence MUST
also show that a boundary-conformant but algebraically wrong fill is rejected by
the relevant acceptor. ABI-invalid fills are execution defects rather than
negative protocol proofs.

Every conformance record is scoped to its exact artifact identities, profile,
supplier set, opaque-input digests, and acceptors. One accepted run is never
universal conformance. The prover endpoint carries no soundness, completeness,
relation-satisfaction, or zero-knowledge claim of its own. Hole-internal algebra
is supplier responsibility; zkc checks only the declared boundary and
observable correspondence. Hiding, preprocessing, ambient parameters,
first-class private randomness, and backend realization require their own
explicit contracts and evidence; none follows from endpoint conformance.
