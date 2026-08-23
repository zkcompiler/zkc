# Current Protocol and PIR reconstruction

> **Document kind:** Temporary Stage 3.1 current-model reconstruction
> **Document state:** Complete research input; not a design decision
> **Authority:** None. The cited specifications remain authoritative for current
> intent, and `docs/status.md` remains authoritative for current support.
> **Snapshot:** Repository checkout inspected on 2026-08-22
> **Scope:** Protocol semantics, canonical PIR, relation ingress, committed
> objects, identity, admission, projection obligations, linking, and the current
> Interface-like and Plan-like surfaces
> **Non-goals:** This document does not select a target model, propose migration,
> or reinterpret a test as a proof of the specifications.
> **Disposition:** Route accepted reconstruction facts through the Stage 3
> absorption record to their durable `project/`, `pir/`, or `relations/`
> owners; delete this note with the completed package before authority cutover.

## 1. Method and evidence vocabulary

This reconstruction follows the repository's own authority rule: an individual
normative specification wins over the overview, while implementation status is
reported separately from intended semantics
([`docs/spec/overview.md:3-11`](../../../docs/spec/overview.md#L3-L11)). It traces
five evidence classes without collapsing them:

1. **Normative intent** — statements in `docs/spec/`.
2. **Implemented correspondence** — TableGen and C++ paths that represent or
   judge that intent.
3. **Tested correspondence** — checked-in tests that assert a behavior. Tests
   were inspected but not executed for this reconstruction.
4. **Retained history** — explicit compatibility notes, retired forms, and clean
   breaks still recorded in the current sources.
5. **Conflict, gap, or unknown** — respectively, incompatible current sources;
   an intended/current surface without its full implementation correspondence;
   or an authority question the inspected material does not settle.

The checkout's status page is a research snapshot last verified on 2026-08-19.
It says that its matrix reports tested repository examples, not compatibility
with every implementation of each family
([`docs/status.md:3-9`](../../../docs/status.md#L3-L9)). No command was run here
to refresh that test result.

## 2. Executive reconstruction

The current system is best described as three coupled layers:

```text
language-independent Protocol Kernel intent
  P = ordered transcript spine + linear claim/reduction graph
      + checks + anchors/material bindings + construction profile + policy
                         |
                         | represented and judged
                         v
closed MLIR PIR carrier
  open pir.protocol -> pir.sealed + canonical Protocol id
                         |
                         | decode, recheck against exact environments, admit
                         v
immutable process-local admitted capability
  -> verifier/prover OIR projection
  -> post-seal relation correspondence
  -> post-seal analysis/compiler consumers
```

The semantic center is not MLIR. The carrier specification explicitly calls
MLIR a structural carrier and lists its present benefits as parsing, printing,
local verification, diagnostics, and whole-artifact test discipline
([`docs/spec/carrier.md:13-40`](../../../docs/spec/carrier.md#L13-L40)). The
Protocol itself has two simultaneous geometries:

- a totally ordered event spine with an absorption subset, which supplies the
  transcript and Fiat--Shamir binding facts; and
- a linear claim-flow graph, whose sources, reductions, and sinks account for
  every proof obligation.

The normative tuple and the reason both geometries are load-bearing are stated
at [`docs/spec/kernel.md:59-76`](../../../docs/spec/kernel.md#L59-L76).

The concrete v0 carrier is substantially narrower than the abstract kernel.
It admits a fixed MLIR operation set, fresh challenge occurrences, flat
commitment/proof-slot forms, content-pinned contracts, one total schedule, and
two endpoint kinds. Rich object state, projected/derived/imported challenges,
general non-executable routes, recursion execution, and relation-bound witness
artifacts remain absent, reserved, or only partly represented. The current
status matrix independently labels sealing, policies, linking, relation
interfaces, endpoint generation, witness interfaces, and recursion as partial
([`docs/status.md:93-119`](../../../docs/status.md#L93-L119)).

Two current concepts are distributed rather than first-class:

- there is no `ProtocolInterface` subject or identity in the inspected current
  spec/code/test corpus; its functions are split among author labels, OIR
  statement labels, claim descriptors, terminal routes, and post-seal relation
  correspondence;
- there is no `ProverPlan` subject or identity; its current analogue is the
  optional, embedded, identity-bearing construction-route graph plus cited
  `HoleContract`s.

Those are reconstruction facts, not a conclusion about their future shape.

## 3. Authority and ownership map

| Concern | Normative owner | Current implementation/evidence owner | Reconstructed boundary |
|---|---|---|---|
| Protocol object and judgments | [`kernel.md`](../../../docs/spec/kernel.md) | `SealEngine`, `SealBattery`, closure checkers | Kernel owns meaning; MLIR must correspond. |
| Physical PIR/OIR shape and encoding | [`carrier.md`](../../../docs/spec/carrier.md) | TableGen dialects, `CanonicalEncoder` | Carrier owns bytes, not semantics. |
| Closed extensible content | [`vocabularies.md`](../../../docs/spec/vocabularies.md) | protocol and construction registries/loaders | Human ids locate entries; content digests authorize meaning. |
| Seal/project/link consumer contracts | [`boundaries.md`](../../../docs/spec/boundaries.md) | `SealEngine`, `PirProject`, `LinkEngine` | Each boundary re-establishes only its named judgment. |
| Endpoint ABI and execution meaning | [`endpoints.md`](../../../docs/spec/endpoints.md) | OIR dialect, projector, executors/emitters | OIR is a derived, separately identified artifact. |
| Relation ingress/correspondence | [`relations.md`](../../../docs/spec/relations.md) | relation registry and `zkc-relation` | Post-seal, evidence-only relative to Protocol identity. |
| Stable v0 surfaces | [`versioning.md`](../../../docs/spec/versioning.md) | encoder/bytecode/diagnostic checks | Exact content identity is the sole general v0 stability promise. |
| Current support | [`status.md`](../../../docs/status.md) | cited tests | Status is a bounded evidence claim, not semantic authority. |

The overview gives the compact system contract: sealing checks the closed
Protocol, structural Fiat--Shamir admissibility, reduction/terminal
attachments, and endpoint obligations; projection derives OIR from the same
sealed object
([`docs/spec/overview.md:15-31`](../../../docs/spec/overview.md#L15-L31)). It also
states that relation compilation is external and that neither relation payload
parsing nor general backend realization is a current Protocol surface
([`docs/spec/overview.md:57-67`](../../../docs/spec/overview.md#L57-L67)).

## 4. Normative Protocol object

### 4.1 The semantic tuple

The normative object is

```text
P = (E, <=, A, C, R, chi, K, anchors, B_M)
```

where:

- `E` is a finite set of semantic events;
- `<=` is one total event order;
- `A` is the subset that advances transcript state;
- `C` is the finite set of linear proof-obligation claims;
- `R` is the source/reduction/sink transformer set;
- `chi` assigns challenge capabilities to challenge events;
- `K` is the set of typed checks;
- `anchors` are opaque digest-shaped semantic references in claim
  descriptors; and
- `B_M` is the set of local-value-to-stable-material binding edges.

The spine is denoted either with fresh challenge sampling or through the
construction profile's duplex-sponge runner, while the claim graph is read as
a string diagram. These readings ground the judgments but are not themselves
stored verdicts
([`docs/spec/kernel.md:78-97`](../../../docs/spec/kernel.md#L78-L97)).

### 4.2 Event classes and observable order

The abstract event classes are slot, public binding, challenge, check,
artifact verification, decision, and protocol-object event. Absorption is
class- or vocabulary-dependent; decision and check are non-absorbing, while
the total order still includes them for deterministic identity
([`docs/spec/kernel.md:99-133`](../../../docs/spec/kernel.md#L99-L133)). Partial
orders are explicitly outside the current kernel.

Values are SSA-like handles introduced by events. Protocol objects are intended
to be SSA-versioned values whose state transitions are explicit events. An
opaque check may hide predicate implementation, but may not hide protected
effects such as transcript absorption, challenge introduction, public binding,
artifact verification, or decision
([`docs/spec/kernel.md:135-178`](../../../docs/spec/kernel.md#L135-L178)).

### 4.3 Claims and transformers

A claim is an obligation, not a proof object or runtime boolean. It has a
stable semantic descriptor `(profile, anchors)`; the resolved profile fixes its
coarse kind and exact anchor schema. Claims deliberately have no lifecycle
state field
([`docs/spec/kernel.md:180-207`](../../../docs/spec/kernel.md#L180-L207)).

Transformers have three shapes:

```text
source     : () -> claims
reduction  : claims + values/challenges/objects -> claims + obligations
sink       : one claim -> ()
```

The four sinks are discharge, export, assume, and residual. Reduction bodies
are event sets, not necessarily contiguous intervals; distinct bodies are
disjoint but may interleave. A discharge is justified by a content-pinned
check-backed `TerminalRule`, not by a theorem citation
([`docs/spec/kernel.md:209-258`](../../../docs/spec/kernel.md#L209-L258)).

### 4.4 The seven structural judgments

The current seal is normatively the conjunction

```text
WF(P)
AND LIN(C)
AND BIND(chi)
AND COV_obl(E)
AND ReductionClosureOK(P)
AND TerminalClosureOK(P)
```

and projection separately establishes `COV_realized` for an endpoint. The seal
and its identity-bearing environment/profile/policy inputs are specified at
[`docs/spec/kernel.md:790-828`](../../../docs/spec/kernel.md#L790-L828). The
kernel's larger judgment inventory also separates identity, transformation
legality, projection preservation, composition/descent, and post-seal security
([`docs/spec/kernel.md:24-45`](../../../docs/spec/kernel.md#L24-L45)).

## 5. Concrete canonical PIR grammar

### 5.1 Container and body grammar

The unit is one single-block `pir.protocol` or `pir.sealed`, never a loose
operation list. Both carry a human `protocol_name`, `kappa`, optional stamped
`vocab`, optional `routes`, optional segment starts, and a policy. `pir.sealed`
adds the stored content id. TableGen defines those containers at
[`include/zkc/Dialect/Pir/PirOps.td:508-577`](../../../include/zkc/Dialect/Pir/PirOps.td#L508-L577).

The fixed body layout is:

```text
[pir.instantiate]*
pir.begin
[pir.bind | pir.slot | pir.chal | pir.check | pir.artifact_verify]*
pir.end
[pir.reduce]*
[pir.material_bind]*
[pir.discharge | pir.export | pir.assume | pir.residual]*
```

The carrier gives the same grammar and explains why reductions follow the
spine and the tail is normalized
([`docs/spec/carrier.md:236-263`](../../../docs/spec/carrier.md#L236-L263)).

### 5.2 Types and operations

| Carrier form | Current meaning | Important carried facts |
|---|---|---|
| `!pir.val<class>` / `!pir.val<profile ...>` | Freely readable event value | Bare payload class, or resolved commitment-like value profile. [`PirTypes.td:18-73`](../../../include/zkc/Dialect/Pir/PirTypes.td#L18-L73) |
| `!pir.claim<profile>` | Linear proof obligation | Profile id; exactly one producer and consumer. [`PirTypes.td:75-90`](../../../include/zkc/Dialect/Pir/PirTypes.td#L75-L90) |
| `pir.instantiate` | Neutral claim source | Author label, exact anchor dictionary, result profile. [`PirOps.td:93-113`](../../../include/zkc/Dialect/Pir/PirOps.td#L93-L113) |
| `pir.begin` / `pir.end` | Transcript thread frame | One token chain; end also means proof-stream exhaustion at projection. [`PirOps.td:124-128`](../../../include/zkc/Dialect/Pir/PirOps.td#L124-L128), [`PirOps.td:368-377`](../../../include/zkc/Dialect/Pir/PirOps.td#L368-L377) |
| `pir.bind` | Absorbing public input/context event | Stage, value or runtime argument, class/profile, optional reduction membership. [`PirOps.td:130-174`](../../../include/zkc/Dialect/Pir/PirOps.td#L130-L174) |
| `pir.slot` | Prover-message event | Class/profile, count, absorbed flag, membership, optional construction binding. [`PirOps.td:176-218`](../../../include/zkc/Dialect/Pir/PirOps.td#L176-L218) |
| `pir.chal` | Fresh challenge event | Explicit dependencies, payload class, domain, space, optional vector mode. [`PirOps.td:221-267`](../../../include/zkc/Dialect/Pir/PirOps.td#L221-L267) |
| `pir.check` | Non-absorbing verifier predicate | Check-contract id, exact params/semantic args/operands, optional transparent expression. [`PirOps.td:269-302`](../../../include/zkc/Dialect/Pir/PirOps.td#L269-L302) |
| `pir.artifact_verify` | Bounded child-verification carrier event | Child, endpoint, semantics, key, statement, child Protocol/relation ids, route, ABI, proof slots, absorption. [`PirOps.td:304-366`](../../../include/zkc/Dialect/Pir/PirOps.td#L304-L366) |
| `pir.reduce` | Generic contract-selected reduction | Input claims, typed dependencies, contract, checks, params, output profiles and asserted anchors. [`PirOps.td:389-425`](../../../include/zkc/Dialect/Pir/PirOps.td#L389-L425) |
| `pir.material_bind` | Stable semantic attachment edge | Local `ValueRef -> MaterialRef`; no alias operation. [`PirOps.td:434-449`](../../../include/zkc/Dialect/Pir/PirOps.td#L434-L449) |
| terminal sinks | Claim closure/routing | Rule plus checks for discharge, or explicit route for export/assume/residual. [`PirOps.td:451-492`](../../../include/zkc/Dialect/Pir/PirOps.td#L451-L492) |

The container verifier uses `ProtocolMemberOpInterface` for phase, label,
thread input/output, absorption, value, and reduction membership rather than a
foreign-open operation walk
([`PirInterfaces.td:15-67`](../../../include/zkc/Dialect/Pir/PirInterfaces.td#L15-L67)).
Challenge-producing operations expose a separate capability interface for
value, class, count, and sampling rule
([`PirInterfaces.td:70-99`](../../../include/zkc/Dialect/Pir/PirInterfaces.td#L70-L99)).

### 5.3 Physical-to-semantic correspondence

The MLIR block is one carrier for two semantic readings:

- operations between `begin` and `end` determine event order;
- token threading fixes the order of stateful transcript events;
- block position also orders unthreaded non-absorbing checks;
- membership attributes and reduce/check selections relate spine events to
  reductions;
- the tail expresses claim production/consumption and material attachments;
- the encoder assigns canonical positions independently of author labels.

The C++ verifier first checks the fixed phase layout and then resolves
cross-references in a second pass
([`lib/Dialect/Pir/PirOps.cpp:400-465`](../../../lib/Dialect/Pir/PirOps.cpp#L400-L465)).
It separately enforces token/membership/claim-use invariants
([`lib/Dialect/Pir/PirOps.cpp:473-731`](../../../lib/Dialect/Pir/PirOps.cpp#L473-L731)).

## 6. Schedule, transcript, and challenges

### 6.1 One identity-bearing total schedule

The current Protocol has exactly one total observable schedule. Absorbing
events update a single transcript state in schedule order; checks remain
ordered but do not update it. The carrier's canonical event index numbers
binds, slots, challenges, checks, and artifact verifications in block order
([`lib/Encoding/CanonicalEncoder.cpp:68-104`](../../../lib/Encoding/CanonicalEncoder.cpp#L68-L104)).
`begin` and `end` frame the schedule but are not numbered semantic events.

`segments` record later run start positions. A standalone Protocol has one
segment; link concatenates runs. Statement bindings must precede the first
challenge in their own segment, while the unabsorbed-material rule is global.
The normative rationale and the unresolved `fs_segment_seam` obligation are at
[`docs/spec/kernel.md:628-677`](../../../docs/spec/kernel.md#L628-L677).

### 6.2 Abstract challenge capability

Normatively, a challenge capability is

```text
(value, origin, pos, payload class, domain, sample space, count, sampling rule)
```

with origins `fresh`, `project`, `derive`, and `imported`. Projected and derived
challenges are pure and retain the source position. Requirement-bearing uses
are distinct from mere reads, and default use is exclusive
([`docs/spec/kernel.md:260-317`](../../../docs/spec/kernel.md#L260-L317)).

The current carrier only has `pir.chal`, whose operation semantics say origin
`fresh`. Scalar and bounded vector samples are admitted; projected, derived,
and imported origins have no current PIR operation. The vocabulary marks
`chal.project` and `chal.derive` reserved
([`docs/spec/vocabularies.md:58-78`](../../../docs/spec/vocabularies.md#L58-L78)).

### 6.3 Requirement generation and BIND

For each requirement-bearing use, `P_req` is a set of event references. BIND
requires every referenced event to precede the challenge and be absorbing.
For a reduction-owned use, the selected `ReductionContract` generates the
required statement bindings, same-and-earlier-round messages, and previous
challenges; authored dependencies may extend but not replace that set
([`docs/spec/kernel.md:580-626`](../../../docs/spec/kernel.md#L580-L626)).

The reduction closure implementation reconstructs contract message roles,
challenge ownership, multiplicity, round ordering, and the required absorbed
prefix
([`lib/Semantics/ReductionClosure.cpp:389-518`](../../../lib/Semantics/ReductionClosure.cpp#L389-L518)).
The source-level negative matrix includes a message committed after its round
challenge and expects the contract-derived prefix error
([`test/Transforms/reduction-closure-invalid.mlir:38-52`](../../../test/Transforms/reduction-closure-invalid.mlir#L38-L52)).

### 6.4 Fresh and Fiat--Shamir readings in the current subject

The current semantic text gives one spine both an interactive fresh-sampling
reading and a construction-profile runner reading. The sealed carrier includes
`kappa` (sponge, codecs, IV policy, constants) and challenge domains/spaces;
projection lowers each `pir.chal` to an OIR squeeze. There is no separate
identity-bearing `FreshPublicCoins` versus `FiatShamir` interpretation tag in
the current PIR schema. Thus the distinction currently appears as two readings
and a projection boundary over one sealed Protocol object, not two separately
identified Protocol subjects.

Construction-profile admission fixes sponge/codec shape and lets the
Soundness Kernel reconstruct sampling bias, but explicitly does not establish
backend transcript conformance
([`docs/spec/vocabularies.md:465-530`](../../../docs/spec/vocabularies.md#L465-L530)).
The Binding Lemma itself remains a stated proof obligation, with its syntactic,
framing, and game-hop parts kept separate
([`docs/spec/kernel.md:927-966`](../../../docs/spec/kernel.md#L927-L966)).

## 7. Claims, reductions, checks, and terminals

### 7.1 Claim identity and linearity

Claim descriptors are exact `(profile id, anchor dictionary)` records. The
position-free descriptor digest is domain-separated, while claim SSA positions
inside one Protocol are canonical production-order references. The carrier
enforces exactly one use of every claim; fan-out or drop requires an explicit
transformer
([`docs/spec/carrier.md:141-158`](../../../docs/spec/carrier.md#L141-L158)).

The anchor membrane is deliberately opaque. A well-shaped digest does not by
itself establish relation denotation, statement meaning, satisfaction, witness
correctness, or compiler correctness
([`docs/spec/kernel.md:319-351`](../../../docs/spec/kernel.md#L319-L351)).

### 7.2 Reduction closure

`ReductionContract` is the authority for both local graph shape and local
implication. Its closed content covers consumed profiles, dependency slots,
rounds, parameters, body-check roles, material constraints, and output
constructors. The current contract format accepts exactly one output. It is
explicitly distinct from relation-domain `RelationContract`
([`docs/spec/vocabularies.md:196-234`](../../../docs/spec/vocabularies.md#L196-L234)).

The implementation checks exact input/dependency shape, parameter dictionaries,
message membership, round/challenge use, check selections and attachments,
material constraints, and reconstructed output descriptors. Representative
implementation regions are
[`ReductionClosure.cpp:316-518`](../../../lib/Semantics/ReductionClosure.cpp#L316-L518)
and
[`ReductionClosure.cpp:958-1089`](../../../lib/Semantics/ReductionClosure.cpp#L958-L1089).

A reduction contract contains no security price and a reduce operation names no
theorem. Security rules and their bindings are post-seal inputs, so changing
them does not alter Protocol identity.

### 7.3 Checks and terminal closure

A `CheckContract` content digest pins its transparent-expression form or opaque
predicate-spec entrypoint plus exact structural ABI. It establishes proposition
and dispatch identity, not conformance of an executable adapter
([`docs/spec/vocabularies.md:361-422`](../../../docs/spec/vocabularies.md#L361-L422)).

A check-backed `TerminalRule` fixes consumed profile, optional exact producer,
role-to-check contracts, attachments, and transparent predicates. Terminal
closure checks exact and injective role selection, producer compatibility, and
every declared semantic/material attachment. Routed sinks instead retain an
explicit route and are admitted according to SealPolicy.

The semantic-closure test suite checks positive sealing/rechecking plus unknown
profiles/contracts/rules, attachment mismatch, material mismatch, malformed
expressions, missing/unused bindings, and wrong transparent predicates
([`test/SemanticClosure/semantic-closure.test:1-56`](../../../test/SemanticClosure/semantic-closure.test#L1-L56)).

### 7.4 Policy

The vocabulary defines five policies and says that each policy governs sink
kinds, check modes, body policies, composition-obligation stance, and minimum
conformance tier
([`docs/spec/vocabularies.md:532-538`](../../../docs/spec/vocabularies.md#L532-L538)).
The current `SealBattery` implementation defines only each policy's permitted
sink set
([`lib/Semantics/SealBattery.cpp:102-129`](../../../lib/Semantics/SealBattery.cpp#L102-L129)).
The status page correspondingly describes protocol policy as partial, with exact
permitted-sink enforcement
([`docs/status.md:104-108`](../../../docs/status.md#L104-L108)).

## 8. Committed objects and stable material

### 8.1 Current admitted form

The concrete committed-object mechanism is `ValueProfile`. A profiled bind or
slot carries one opaque commitment-like value while the profile fixes:

- the element class of the content behind it;
- `arity_log2`;
- origin (`prover_message`, `preprocessed`, or `relation_derived`); and
- a binding route describing where the declared content is discharged.

Origin must agree with the event seat and reduction message source
([`docs/spec/vocabularies.md:174-194`](../../../docs/spec/vocabularies.md#L174-L194)).
The value itself stays opaque to the kernel; profile facts are declarative
identity content, not a checked opening or content-satisfaction judgment.
The current registry contains four concrete LogUp-oriented profiles — committed
column, multiplicities, queries, and preprocessed table — rather than a general
object catalogue
([`registry/protocol-vocabulary.json:3711-3735`](../../../registry/protocol-vocabulary.json#L3711-L3735)).

The vocabulary lists many abstract object families, but only `Commitment` and
`ProofSlot` are admitted in flat PIR form; other object/state families remain
reserved
([`docs/spec/vocabularies.md:456-463`](../../../docs/spec/vocabularies.md#L456-L463)).
There is no current MLIR object-version type or object-state transition
operation corresponding to the abstract kernel's general SSA object model.

### 8.2 Material bindings

`pir.material_bind` connects a local canonical event/result port to a stable
digest-shaped semantic reference. The relation is a partial function and
reverse-injective within one artifact. Each edge must be consumed by a real
reduction or terminal attachment; it proves only the declared reference
equality, not external authorization or runtime-byte correspondence
([`docs/spec/kernel.md:332-351`](../../../docs/spec/kernel.md#L332-L351)).

This mechanism is the only current explicit bridge from verifier-visible SSA
values to stable semantic references. Link preserves the `MaterialRef` and
reindexes the local `ValueRef`.

### 8.3 Bounded child artifact form

`pir.artifact_verify` is an identity-bearing carrier for eight principal child
facts plus optional ABI/proof-slot information. Its tests deliberately pin a
state in which the form seals and canonically encodes but verifier projection
refuses because projection, execution, and conformance rules are reserved
([`test/Encoding/artifact-verify.mlir:1-44`](../../../test/Encoding/artifact-verify.mlir#L1-L44)).
The status page says no child artifact is verified and nothing composes
([`docs/status.md:119-119`](../../../docs/status.md#L119-L119)).

## 9. Canonical encoding and identity

### 9.1 Identity boundary

Protocol identity is a domain-separated hash over canonical semantic carrier
content. For PIR the implementation computes
`SHA256("zkc/pir\n" || canonical_bytes)` and excludes the stored id from the
preimage
([`lib/Encoding/CanonicalEncoder.cpp:1456-1478`](../../../lib/Encoding/CanonicalEncoder.cpp#L1456-L1478)).

The identity includes:

- policy and construction profile;
- the exact content-pinned cited vocabulary subset;
- normalized sources/reductions/sinks and all claim descriptors;
- canonical event rows and material bindings;
- construction routes when present; and
- segment decomposition when present.

It excludes:

- `protocol_name` and author selector labels after positional resolution;
- the stored id;
- evidence, backend names, calibrations, and derived security judgments; and
- theorem citations and derived obligation tables.

The normative identity set is stated at
[`docs/spec/kernel.md:830-896`](../../../docs/spec/kernel.md#L830-L896), and the
carrier's positional normalization at
[`docs/spec/carrier.md:308-344`](../../../docs/spec/carrier.md#L308-L344).

### 9.2 Positional quotient

Author labels select SSA values, reductions, checks, and memberships during
construction, but canonical form replaces those selectors with positions.
`test/Encoding/relabel.mlir` pins equal PIR identities under a consistent
renaming of source, event, check, reduction, membership, material, and terminal
handles
([`test/Encoding/relabel.mlir:1-8`](../../../test/Encoding/relabel.mlir#L1-L8)).

Semantic strings that are not classified as labels remain identity content:
profile ids, contract ids, payload classes, challenge domains, roles, route
names, hole-instance names, and kappa constants. Claim-transformer order is
normalized by content and dependency readiness rather than blindly hashing
authored tail order
([`docs/spec/carrier.md:345-411`](../../../docs/spec/carrier.md#L345-L411)).

### 9.3 Closed vocabulary and content authority

`ProtocolVocabulary` has seven jointly admitted source sections:
`predicate_specs`, `claim_profiles`, `value_profiles`, `check_contracts`,
`hole_contracts`, `reduction_contracts`, and `terminal_rules`. They are not
independently loadable authorities
([`docs/spec/vocabularies.md:80-108`](../../../docs/spec/vocabularies.md#L80-L108)).

The sealed artifact stores exact cited digest tables for claim profiles, value
profiles when used, check contracts, hole contracts when used, reduction
contracts, terminal rules, and consumed construction entries. Predicate-spec
preimages are re-resolved transitively from the environment rather than copied
into the artifact. Unknown fields/constructors and stale content digests fail
closed
([`docs/spec/carrier.md:601-654`](../../../docs/spec/carrier.md#L601-L654)).

### 9.4 Versioning

At v0 the only general stability promise is exact content identity: an id names
the same preimage bytes forever. There are no legacy decoders, upgrade hooks,
or compatibility negotiation; schemas, text, CLI surfaces, and carrier details
may break between revisions
([`docs/spec/versioning.md:3-13`](../../../docs/spec/versioning.md#L3-L13)).
The carrier bytecode version is currently the single 0.0 form rather than an
upgrade protocol.

## 10. Authentication and admission lifecycle

The implemented lifecycle separates three facts:

```text
pir.protocol
  -- semantic judgment + vocabulary stamp + canonical hash --> pir.sealed
  -- bytecode/shape/stored-id validation --------------------> DecodedPirArtifact
  -- exact environment recheck ------------------------------> AdmittedPirArtifact
```

### 10.1 Seal

`SealEngine::seal` first judges open PIR, builds the exact resolved vocabulary,
temporarily stamps it, computes the id, clones the body into `pir.sealed`,
verifies the result, and erases the open container only on success
([`lib/Semantics/SealEngine.cpp:144-186`](../../../lib/Semantics/SealEngine.cpp#L144-L186)).
The open judgment combines MLIR verification, the seal battery, and construction
graph admission
([`lib/Semantics/SealEngine.cpp:189-207`](../../../lib/Semantics/SealEngine.cpp#L189-L207)).

### 10.2 Decode

The artifact writer recomputes identity before bytecode emission. The decoder
checks the producer family marker, exact one-`pir.sealed` shape, MLIR
verification, recomputed identity, and optional caller-expected identity
([`lib/Artifact/Artifact.cpp:49-67`](../../../lib/Artifact/Artifact.cpp#L49-L67),
[`lib/Artifact/Artifact.cpp:104-160`](../../../lib/Artifact/Artifact.cpp#L104-L160)).
`DecodedPirArtifact` is explicitly transport/shape/id authenticated but not
registry-semantically admitted
([`include/zkc/Artifact/Artifact.h:39-70`](../../../include/zkc/Artifact/Artifact.h#L39-L70)).

### 10.3 Admit and capability

Admission reruns `SealEngine::recheck` against one exact immutable
`ProtocolEnvironment`; recheck repeats structural/battery/route judgments and
validates identity
([`lib/Semantics/SealEngine.cpp:209-229`](../../../lib/Semantics/SealEngine.cpp#L209-L229),
[`lib/Artifact/Artifact.cpp:226-246`](../../../lib/Artifact/Artifact.cpp#L226-L246)).
The admitted object exposes its id and environment but no mutable IR accessor;
copies retain one immutable subject and authority
([`include/zkc/Artifact/Artifact.h:72-101`](../../../include/zkc/Artifact/Artifact.h#L72-L101)).

Authority is therefore process-local capability authority. Bytes, the stored
digest, a cloned operation, or a cached verdict do not become an admitted
capability merely by carrying the same fields.

## 11. Projection and the current obligation model

Normatively, every semantic event derives one projection obligation at seal,
and each endpoint projection must cover the obligation set exactly, with no
missing or phantom event positions
([`docs/spec/kernel.md:731-788`](../../../docs/spec/kernel.md#L731-L788)). The
current admitted discharge families cover bind, slot, scalar/vector challenge,
and transparent/opaque check effects
([`lib/Semantics/SealBattery.cpp:958-990`](../../../lib/Semantics/SealBattery.cpp#L958-L990)).

Projection currently:

- requires an admitted PIR capability;
- rejects an empty verifier face;
- requires construction-route totality only for prover projection;
- copies instance-bind labels into ordered OIR `statement_labels`;
- lowers each supported event with source-position provenance;
- adds the endpoint frame (`expect_end; decide` or `end_stream; finish`); and
- recomputes obligations and checks exact realized coverage.

The statement ABI and route-totality gates are visible at
[`PirProject.cpp:280-344`](../../../lib/Dialect/Pir/Transforms/PirProject.cpp#L280-L344),
and the endpoint frame/coverage phase at
[`PirProject.cpp:741-770`](../../../lib/Dialect/Pir/Transforms/PirProject.cpp#L741-L770).

OIR has its own identity. Its `statement_labels`, full entry signature, row
labels, parameter digests, codecs, and endpoint program are identity content
([`lib/Encoding/CanonicalEncoder.cpp:1115-1219`](../../../lib/Encoding/CanonicalEncoder.cpp#L1115-L1219),
[`lib/Encoding/CanonicalEncoder.cpp:1304-1365`](../../../lib/Encoding/CanonicalEncoder.cpp#L1304-L1365)).
The endpoint spec explicitly calls labels endpoint ABI even though author labels
do not enter PIR identity
([`docs/spec/endpoints.md:53-76`](../../../docs/spec/endpoints.md#L53-L76)).

## 12. Current Interface-like surface

No current `ProtocolInterface` or `ProtocolInterfaceId` declaration was found
in `docs/spec`, `include`, `lib`, or `test`. Interface-like responsibilities are
instead distributed as follows:

| Fragment | What it currently exposes | Identity/authority behavior |
|---|---|---|
| Claim descriptor | Profile plus exact semantic anchors | Part of PIR identity; exact face used by link. |
| Instance `pir.bind` labels | Ordered public statement names | Excluded from PIR identity after positional normalization. |
| OIR `statement_labels` and entry types | Endpoint public ABI | Included in OIR identity. |
| Routed sink names | Export/assume/residual surface | Included in PIR identity as semantic route strings. |
| Material references | Stable semantic endpoints | Included in PIR identity and preserved by link. |
| Relation `statement_correspondence` | Relation-instance positions to statement labels | RelationContract content; post-seal and evidence-only relative to PIR. |
| Relation witness ports | Declared private relation input ports | RelationContract content; does not require any endpoint to consume them. |

This decomposition means the current Protocol's canonical semantic quotient and
the current endpoint/relation ABI do not share one explicit identified
Interface object. Section 17 records the resulting read-set conflict without
selecting a remedy.

## 13. Current Plan-like surface

No current `ProverPlan` or `ProverPlanId` declaration was found in the same
corpus. The closest current object is the optional `routes` dictionary embedded
inside PIR and included in Protocol identity.

### 13.1 Route graph

The implemented route graph contains:

- ordered `(witness label, handle class)` declarations;
- named hole instances selecting exact content-pinned `HoleContract`s;
- exact static and semantic parameters;
- ordered typed instance inputs;
- dependencies between hole-instance results; and
- an optional construction binding on each slot.

The parser admits exactly six route-reference classes: bind, prior slot,
challenge, kappa constant, witness handle, and prior hole-instance result
([`lib/Semantics/ConstructionGraph.h:21-40`](../../../lib/Semantics/ConstructionGraph.h#L21-L40),
[`lib/Semantics/ConstructionGraph.cpp:26-83`](../../../lib/Semantics/ConstructionGraph.cpp#L26-L83)).
The graph checks exact contract/parameter/operand shape, handle at-most-one-use,
acyclic instance dependencies, slot result agreement, and temporal availability
([`lib/Semantics/ConstructionGraph.cpp:208-452`](../../../lib/Semantics/ConstructionGraph.cpp#L208-L452),
[`lib/Semantics/ConstructionGraph.cpp:455-554`](../../../lib/Semantics/ConstructionGraph.cpp#L455-L554)).

### 13.2 Boundary of the current claim

Routes are construction declarations, not executable suppliers. A
`HoleContract` digest fixes the call ABI but neither identifies the supplier nor
establishes its internal algebra
([`docs/spec/vocabularies.md:424-454`](../../../docs/spec/vocabularies.md#L424-L454)).
Seal permits missing slot routes; prover projection, not seal, requires every
slot to be constructible
([`docs/spec/carrier.md:222-235`](../../../docs/spec/carrier.md#L222-L235),
[`PirProject.cpp:287-295`](../../../lib/Dialect/Pir/Transforms/PirProject.cpp#L287-L295)).

The construction graph is embedded, shares Protocol identity, and has no
separate admission identity, supplier selection, realization judgment, or
correctness claim. Post-seal Soundness `DerivationPlan` and Compiler
`TransformPlan` are different consumer objects and are not prover construction
plans.

## 14. Relation model and ingress

### 14.1 Ownership boundary

The Protocol Kernel treats claim anchors as opaque. Relation compilation,
payload reading, witness generation, and satisfaction are external. A
`RelationContract` is a post-seal, content-addressed document whose facts are
evidence-only relative to Protocol identity: changing it does not change the
Protocol id, transcript, or structural kernel judgments
([`docs/spec/relations.md:3-43`](../../../docs/spec/relations.md#L3-L43)).

The contract's closed schema includes:

- a pinned claim profile;
- relation-anchor and instance-anchor partition;
- relation format and identity declaration;
- public-instance encoding;
- private witness ports;
- ordered statement correspondence; and
- optional declared shape.

The closed field set is stated at
[`docs/spec/relations.md:63-68`](../../../docs/spec/relations.md#L63-L68).

### 14.2 Identity and reading forms

Relation identity has two deliberately separate sources: a locally computed
content digest over supplied bytes, or an externally attested id plus named
attestor. Current reading forms are `r1cs-bin-v1` and `opaque`
([`docs/spec/relations.md:70-103`](../../../docs/spec/relations.md#L70-L103)).
The R1CS reader parses only the header and skips constraint and wire-map bodies;
it establishes prime, public arity, private-input count, and constraint count,
but no constraint satisfaction or semantic meaning
([`docs/spec/relations.md:343-375`](../../../docs/spec/relations.md#L343-L375)).

### 14.3 Relation instance, witness, and statement correspondence

Current instance encodings are field vector, opaque bytes, or commitment. The
witness interface is either enumerated named ports/counts or one opaque witness
port. Declaring ports does not oblige an endpoint to consume them
([`docs/spec/relations.md:138-177`](../../../docs/spec/relations.md#L138-L177)).

`statement_correspondence` maps relation public positions to sealed artifact
statement labels. The mapping may permute relation order relative to Protocol
absorption order. Label presence is computed, count agreement is cross-checked,
and what a label means remains asserted
([`docs/spec/relations.md:179-221`](../../../docs/spec/relations.md#L179-L221)).

A relation anchor may be transcript-carried by absorbing its fixed projection:
eight low-27-bit limbs, a 216-bit binding of a 256-bit digest. The remaining
security shortfall is explicitly not erased
([`docs/spec/relations.md:233-267`](../../../docs/spec/relations.md#L233-L267)).

### 14.4 Correspondence judgment and trust tiers

The relation judgment reports three positive/evidentiary tiers:

- **computed** from bytes or admitted artifact;
- **cross-checked** agreement between declared and derived facts, which is
  consistency rather than truth; and
- **asserted** residual meaning/provenance/correctness obligations.

The specification defines those tiers at
[`docs/spec/relations.md:269-306`](../../../docs/spec/relations.md#L269-L306) and
permanently excludes intended relation semantics, non-underconstraint, witness
generator correctness, slot meaning, provenance, and bytes-to-anchor identity
from what the reader establishes
([`docs/spec/relations.md:377-388`](../../../docs/spec/relations.md#L377-L388)).

The tool implements contract/header cross-checks, artifact statement-label
membership, transcript-carried relation anchors, material-binding wiring, and
the asserted remainder
([`tools/zkc-relation/zkc-relation.cpp:227-410`](../../../tools/zkc-relation/zkc-relation.cpp#L227-L410)).
It emits a canonical report with `computed`, `cross_checked`, `disagreed`, and
`asserted` lists
([`zkc-relation.cpp:411-434`](../../../tools/zkc-relation/zkc-relation.cpp#L411-L434)).

## 15. Linking and composition

### 15.1 Normative link contract

Normatively, `link` consumes two open Protocols, merges compatible construction
profiles, prefixes face-local namespaces, fuses exact producer export/consumer
source descriptors, splices schedules, retains segments, composes routes,
rechecks claim/material/closure judgments, re-derives challenge domains, and
returns a new open Protocol. The full contract also names imported-challenge
composition obligations and one `fs_segment_seam` obligation per splice
([`docs/spec/boundaries.md:279-334`](../../../docs/spec/boundaries.md#L279-L334)).

### 15.2 Implemented link envelope

`LinkEngine` explicitly scopes itself to the currently represented
fresh/local-challenge carrier
([`include/zkc/Semantics/LinkEngine.h:13-26`](../../../include/zkc/Semantics/LinkEngine.h#L13-L26)).
It:

- validates disjoint face prefixes;
- judges both open inputs;
- merges kappa axis-wise and refuses conflicts;
- fuses each producer export with exactly one consumer source carrying the
  same profile and anchors;
- concatenates event runs and records segment boundaries;
- qualifies route witnesses, hole instances, event selectors, membership, and
  challenge domains;
- preserves/reindexes material bindings;
- chooses the consumer policy for the composite;
- re-judges the completed open Protocol; and
- leaves both inputs intact on every result.

The exact claim fusion is at
[`LinkEngine.cpp:231-270`](../../../lib/Semantics/LinkEngine.cpp#L231-L270),
segment/route construction at
[`LinkEngine.cpp:272-303`](../../../lib/Semantics/LinkEngine.cpp#L272-L303), and
body reconstruction/rejudgment at
[`LinkEngine.cpp:311-422`](../../../lib/Semantics/LinkEngine.cpp#L311-L422).

The link test explicitly says its segment boundary makes the structural
statement-binding rule valid but makes no `fs_segment_seam` soundness claim
([`test/Transforms/pir-link.mlir:1-8`](../../../test/Transforms/pir-link.mlir#L1-L8)).
Route-link tests pin namespace rewriting and re-admission of composed route
graphs
([`test/Transforms/pir-link-routes.mlir:9-43`](../../../test/Transforms/pir-link-routes.mlir#L9-L43)).

This is open-PIR authoring composition. It is not aggregation of admitted
children, verifier-as-relation descent, or a theorem that security properties
compose.

## 16. Implemented correspondence matrix

| Intended judgment/surface | Current correspondence | Evidence classification |
|---|---|---|
| Closed MLIR grammar and local WF | ODS/TableGen plus two-pass container verifier | Implemented; extensive negative tests. |
| Claim linearity | Exact one-use verification over `!pir.claim` | Implemented for current operations. |
| BIND structural rules | Seal spine walk plus contract-derived round checks | Implemented for fresh current challenge forms. |
| Reduction closure | Dedicated content-driven closure checker | Implemented for admitted contracts. |
| Terminal closure | Dedicated rule/attachment/material checker | Implemented for check-backed rules. |
| Policy | Sink-kind table | Partial relative to five normative dimensions. |
| `COV_obl` | Discharge table and `deriveObligations` view | Implemented for bind/slot/challenge/check; incomplete for artifact verification. |
| `COV_realized` | Projector provenance and exact coverage check | Implemented for supported verifier/prover endpoint events. |
| Canonical identity | Independent positional encoder and SHA-256 domain tag | Implemented; source-level parity/golden tests exist. |
| Persisted lifecycle | Decode/id check, registry recheck, private admitted capability | Implemented for current v0 PIR. |
| General object events | Flat value profiles only | Abstract intent ahead of carrier. |
| General challenge origins | `pir.chal` fresh only | Abstract intent ahead of carrier. |
| Relation correspondence | Post-seal contract tool, header reader, evidence ledger | Partial and evidence-only by design. |
| Linking | Fresh/local open-PIR splice with exact face matching | Partial relative to normative imported/seam composition. |
| Interface | Distributed labels/descriptors/routes/correspondence | No first-class current subject. |
| Prover plan | Embedded optional construction route graph | No separately identified current subject. |
| Child artifact verification | Canonical carrier row and seal-side facts | Projection/execution/conformance absent and refused. |

## 17. Conflict, gap, and unknown ledger

This ledger records current-source observations only. It intentionally does not
state a target resolution.

### 17.1 Conflicts

#### C-01 — challenge event row disagrees about author-label content

The carrier first says canonical encoding is fully positional and author labels
never appear
([`docs/spec/carrier.md:313-324`](../../../docs/spec/carrier.md#L313-L324)), but
its exact event-row table spells challenge as
`["chal", payload_class, label, domain, ...]`
([`docs/spec/carrier.md:351-378`](../../../docs/spec/carrier.md#L351-L378)). The
implementation omits the label and emits payload class, domain, space, sorted
dependency positions, and optional mode
([`CanonicalEncoder.cpp:769-797`](../../../lib/Encoding/CanonicalEncoder.cpp#L769-L797)).
The prose, table, and code cannot all be literal simultaneously.

#### C-02 — PIR label quotient versus downstream normative label read sets

PIR relabeling is identity-stable, and the relabel test pins one id for two
consistently renamed Protocols. Projection nevertheless copies instance-bind
labels into `statement_labels`, which enter OIR identity
([`PirProject.cpp:297-344`](../../../lib/Dialect/Pir/Transforms/PirProject.cpp#L297-L344),
[`CanonicalEncoder.cpp:1304-1340`](../../../lib/Encoding/CanonicalEncoder.cpp#L1304-L1340)).
Relation correspondence also consumes those labels normatively
([`docs/spec/relations.md:179-204`](../../../docs/spec/relations.md#L179-L204)).
Therefore one current `ProtocolId` equivalence class admits representatives
whose projected ABI/OIR identity and relation wiring differ without an
additional identified Interface input. This conflicts with the kernel's rule
that accepted statement, proof ABI, or decision-changing data is seal-time
identity-bearing
([`docs/spec/kernel.md:353-367`](../../../docs/spec/kernel.md#L353-L367)).

#### C-03 — relation disagreement: refusal in spec, negative result in tool/tests

The relation specification says a content-digest mismatch refuses and that
every field failure is a named refusal
([`docs/spec/relations.md:308-341`](../../../docs/spec/relations.md#L308-L341)).
The tool instead accumulates disagreements, emits a canonical judgment
document, and exits 1. Its test explicitly says a disagreement is the judgment,
not a failure to reach one
([`test/Relation/relation-disagreements.test:1-16`](../../../test/Relation/relation-disagreements.test#L1-L16)).
This is a semantic outcome conflict, not merely diagnostic wording.

#### C-04 — `artifact_verify` is both reserved-with-no-representation and sealable

The vocabulary defines `reserved` to mean no accepted current representation
and fail-closed use, then lists `artifact_import / artifact_verify` as reserved
([`docs/spec/vocabularies.md:13-22`](../../../docs/spec/vocabularies.md#L13-L22),
[`docs/spec/vocabularies.md:58-74`](../../../docs/spec/vocabularies.md#L58-L74)).
The carrier, encoder, seal battery, status, and tests deliberately admit a
sealable canonical `pir.artifact_verify` representation while refusing
projection. That staged state does not fit the vocabulary's two-state
admitted/reserved definition.

#### C-05 — the exhaustive identity-domain list omits live domains

The versioning specification says its domain-tag list is exhaustive and that a
tag present in the implementation but absent from the list is a defect. That
list omits both `"zkc/value-profile\n"` and
`"zkc/relation-contract\n"`
([`docs/spec/versioning.md:15-22`](../../../docs/spec/versioning.md#L15-L22)).
Both are current normative and implemented digest domains: value profiles are
digested in
[`lib/Registry/ProtocolVocabulary.cpp:158-170`](../../../lib/Registry/ProtocolVocabulary.cpp#L158-L170),
and RelationContracts specify and implement their own tagged digest
([`docs/spec/relations.md:55-61`](../../../docs/spec/relations.md#L55-L61),
[`lib/Registry/RelationContractRegistry.cpp:444-454`](../../../lib/Registry/RelationContractRegistry.cpp#L444-L454)).

#### C-06 — ProtocolVocabulary section count conflates source and sealed views

The overview, vocabulary specification, and carrier define seven required
jointly admitted source sections, including `predicate_specs`. The kernel's
seal section instead says `ProtocolVocabulary` supplies six jointly admitted
v4 sections
([`docs/spec/kernel.md:812-821`](../../../docs/spec/kernel.md#L812-L821)). The
carrier later identifies the likely six being counted as the protocol-entry
families copied into sealed `vocab`, while predicate-spec preimages are resolved
indirectly
([`docs/spec/carrier.md:640-653`](../../../docs/spec/carrier.md#L640-L653)). The
underlying implementation can therefore be reconstructed, but the normative
term “ProtocolVocabulary sections” has two incompatible counts unless the
source-envelope/sealed-table distinction is made explicit.

### 17.2 Implementation gaps relative to current normative intent

#### G-01 — seal does not establish `COV_obl` for `artifact_verify`

The canonical event index includes `artifact_verify`, but
`deriveObligations` handles only bind, slot, challenge, and check; its default is
unreachable
([`CanonicalEncoder.cpp:68-92`](../../../lib/Encoding/CanonicalEncoder.cpp#L68-L92),
[`SealBattery.cpp:1001-1045`](../../../lib/Semantics/SealBattery.cpp#L1001-L1045)).
More fundamentally, the seal battery's `run` path does not call
`deriveObligations`; it performs domain, policy, kappa/profile/segment, spine,
reduction, terminal, and material-use checks and returns
([`SealBattery.cpp:162-199`](../../../lib/Semantics/SealBattery.cpp#L162-L199)).
Thus the implemented seal accepts this semantic event without deriving the one
obligation per event that normative `COV_obl` requires. Projection refuses
before reaching obligation derivation, so the checked test avoids exercising
the missing row.

#### G-02 — policy implementation covers only sink permissions

The normative five policy dimensions include check mode, body policy,
composition stance, and conformance tier in addition to sinks. The current C++
policy table and status claim cover only exact permitted sinks. The remaining
dimensions have no corresponding policy enforcement in the inspected seal
path.

#### G-03 — link omits normative seam/composition-obligation materialization

The normative link contract records `fs_segment_seam` and handles imported
challenge obligations. The implementation explicitly supports fresh/local
challenges, records segment starts, and has no seam-obligation representation
or imported challenge carrier to discharge. The link test expressly disclaims
the soundness seam claim.

#### G-04 — link name rewriting has no `artifact_verify` case

`prefixNames` handles instantiate, bind, slot, challenge, check, reduce, and
discharge selectors, with a default no-op
([`LinkEngine.cpp:149-198`](../../../lib/Semantics/LinkEngine.cpp#L149-L198)).
`artifact_verify` is nevertheless a canonical event and contains a face-local
author label plus a parent route. No dedicated link correspondence or test was
found for this event. Composite rejudgment may catch some collisions, but it is
not an explicit composition semantics for the operation.

#### G-05 — documented construction references exceed implemented route grammar

The carrier says hole inputs may reference anchored material and slots may bind
pure expressions over route references
([`docs/spec/carrier.md:222-231`](../../../docs/spec/carrier.md#L222-L231)). The
implemented `RouteReferenceKind` has neither anchored-material nor expression
constructors; route instances accept only reference strings and slot bindings
only instance results, binds, or constants. This is a direct representation
gap in the Plan-like surface.

#### G-06 — abstract challenge origins exceed current carrier

The kernel defines fresh, project, derive, and imported origins plus associated
composition rules. Current PIR admits only fresh `pir.chal`; there is no
accepted encoding, verifier path, or projection rule for the other origins.

#### G-07 — abstract protocol objects exceed flat committed values

The kernel permits SSA-versioned object state transitions. Current PIR admits
flat commitment/proof-slot forms through profiled values, without general
object identity, state alphabet, transition operation, or object-event closure.

#### G-08 — abstract decision event is created only at OIR framing

The kernel lists decision as a semantic event and the vocabulary calls decision
admitted, but PIR has no decision operation or canonical event row. Projector
unconditionally appends OIR `decide` for verifier endpoints or `finish` for
prover endpoints
([`PirProject.cpp:741-750`](../../../lib/Dialect/Pir/Transforms/PirProject.cpp#L741-L750)).
The terminal endpoint effect therefore has no source Protocol event or
`COV_obl` row in the current carrier.

#### G-09 — relation reader checks header/interface consistency, not relation body

The current R1CS reader skips constraints and wire-map bodies. It cannot check
anchor preimages, constraint satisfaction, underconstraint, witness-generation
correctness, or source-compiler correspondence. This is mostly an explicit
scope boundary, but it leaves the current relation ingress at interface/header
correspondence rather than relation semantic admission.

#### G-10 — no standalone Interface or Plan authority

Interface-like labels and Plan-like routes affect downstream ABIs or prover
construction, but neither has its own current identity/admission/capability
boundary. The first remains partly outside `ProtocolId`; the second is embedded
inside it. This is a missing subject boundary in the current model, not evidence
that either distributed mechanism is unimplemented.

### 17.3 Unknowns not settled by current authority

#### U-01 — link policy combination semantics

The implementation assigns the composite the consumer's policy
([`LinkEngine.cpp:295-303`](../../../lib/Semantics/LinkEngine.cpp#L295-L303)) and
rejudges it. The normative link text explains rejudgment but does not state why
consumer policy, rather than a merge or explicit link input, is the authority.

#### U-02 — intended status of label-only representative variation

Current sources clearly intend PIR id-stable renaming and clearly use labels as
OIR/relation ABI. They do not say whether downstream consumers are meant to
accept arbitrary representatives of one PIR identity, whether a stored carrier
representative itself supplies extra authenticated authority, or whether an
unmodeled Interface identity is assumed. C-02 records the observable fracture;
this item records the missing intended interpretation.

#### U-03 — registry-free recheckability versus implemented admission API

The kernel says seal judgments are re-checkable from artifact-pinned vocabulary
content and predicate-spec preimages, so a consumer needs no registry
([`docs/spec/kernel.md:889-896`](../../../docs/spec/kernel.md#L889-L896)). The
persisted artifact omits predicate-spec preimages, and the implemented admission
API requires a full external `ProtocolEnvironment`. It is unclear whether the
normative statement describes a future self-contained artifact package, a
logical input set independent of registry naming, or the current API after an
environment has supplied those preimages.

#### U-04 — bounded artifact verification's eventual obligation semantics

The current carrier pins child facts and route lifting, but does not define the
projection discharge kind, how child success/failure reaches the parent's
decision, how child assumptions are authenticated, or which exact claim is
covered. These are intentionally reserved, so the carrier row alone does not
settle them.

## 18. Tests and examples inspected

No top-level `examples/` directory exists. Protocol examples are executable
test fixtures and family generators. The status matrix points to Schnorr,
DLEQ/OR-Sigma, Sumcheck, bounded GKR, KZG batching, bounded FRI, and R1CS to
Sumcheck evidence
([`docs/status.md:34-84`](../../../docs/status.md#L34-L84)).

| Evidence family | What the checked-in source asserts | Claim limit |
|---|---|---|
| [`test/Dialect/Pir/invalid.mlir`](../../../test/Dialect/Pir/invalid.mlir) | Closed grammar, thread/layout/label/type refusals | Local carrier verification. |
| [`test/Transforms/pir-seal-invalid.mlir`](../../../test/Transforms/pir-seal-invalid.mlir) | Policy, BIND, kappa, codec, check, and encoding-domain refusals | Current seal cases, not abstract completeness. |
| [`test/Transforms/reduction-closure-invalid.mlir`](../../../test/Transforms/reduction-closure-invalid.mlir) | Adversarial contract shape, membership, challenge, checks, and output cases | Admitted reduction contracts only. |
| [`test/SemanticClosure/semantic-closure.test`](../../../test/SemanticClosure/semantic-closure.test) | Terminal/material closure positive and negative paths | Check-backed current terminal rules. |
| [`test/Transforms/construction-graph-invalid.mlir`](../../../test/Transforms/construction-graph-invalid.mlir) | Route parameters, references, shapes, cycles, handles, and timing | Implemented six-reference route grammar. |
| [`test/Encoding/relabel.mlir`](../../../test/Encoding/relabel.mlir) | Author-label renaming preserves PIR id | Also exposes the downstream ABI issue in C-02. |
| [`test/Encoding/value-profile-resolution.mlir`](../../../test/Encoding/value-profile-resolution.mlir) | Value-profile resolution, origin seat, class/codec, and binding rules | Flat current commitment profiles. |
| [`test/Encoding/artifact-verify.mlir`](../../../test/Encoding/artifact-verify.mlir) | Child-verification row seals/encodes; verifier projection refuses | No child verification or composition. |
| [`test/Transforms/pir-project.mlir`](../../../test/Transforms/pir-project.mlir) | Supported event lowering and coverage | Current endpoint vocabulary. |
| [`test/Transforms/pir-link.mlir`](../../../test/Transforms/pir-link.mlir) | Claim fusion, namespace/domain prefixing, segments, material preservation | Fresh/local open composition; no seam theorem. |
| [`test/Transforms/pir-link-routes.mlir`](../../../test/Transforms/pir-link-routes.mlir) | Construction-route namespace composition | Current route graph only. |
| [`test/Relation/relation-contract.test`](../../../test/Relation/relation-contract.test) | Registry admission and computed/cross-checked/asserted report growth | Header/interface correspondence, not relation truth. |
| [`test/Relation/relation-disagreements.test`](../../../test/Relation/relation-disagreements.test) | Negative correspondence document and exit status 1 | Conflicts with normative refusal wording. |

Because these tests were not executed in this Stage 3.1 task, the table records
their source-declared intent, not a newly observed passing result.

## 19. Retained history and clean breaks

The current sources retain several decisions that explain otherwise surprising
shapes:

- the canonical encoding clean break removed reduction theorem citations,
  container hop citations, and sealed `theorem_rows`; historical encodings are
  not loader migration inputs
  ([`docs/spec/carrier.md:445-450`](../../../docs/spec/carrier.md#L445-L450));
- the former `chal` pseudo-payload class is retired; challenge origin and
  semantic payload class are now orthogonal
  ([`docs/spec/vocabularies.md:235-241`](../../../docs/spec/vocabularies.md#L235-L241));
- `opaque_relation` remains an admitted small compatibility-shaped claim
  profile while relation denotation moved to the external contract boundary;
- scalar event/OIR rows are intentionally preserved while vector/profile/route
  material is added under distinct row heads or optional tails; and
- v0 makes identity-preserving history an exact-byte statement, not a promise
  to upgrade older artifacts.

These notes explain current representation choices but do not upgrade them into
semantic requirements beyond what the normative documents state.

## 20. Exact current support envelope

The strongest accurate high-level statement about the current model is:

> zkc currently represents a closed, totally scheduled, public-coin Protocol
> with fresh challenge occurrences, linear content-pinned claim reductions,
> explicit checks and terminals, flat committed-value profiles, optional typed
> prover construction routes, and canonical positional identity in MLIR PIR.
> It can authenticate and admit that artifact against exact environments,
> project supported verifier/prover OIR with exact event coverage, compose a
> bounded fresh/local open-PIR subset, and produce post-seal relation-interface
> correspondence evidence.

That statement does **not** claim:

- general Protocol object/state semantics in the current carrier;
- separate identified fresh and Fiat--Shamir Protocol subjects;
- projected, derived, or imported challenges;
- semantic relation admission, relation satisfaction, or witness correctness;
- a first-class identified Protocol Interface or Prover Plan;
- child artifact verification, recursion, or verifier-as-relation descent;
- general semantic/security composition;
- complete enforcement of every SealPolicy dimension;
- formal proof of the kernel, Binding Lemma, projection, or implementation
  correspondence; or
- compatibility with every external implementation of an exercised family.

The status document makes the same critical evidence distinction: conditional
soundness judgments, execution evidence, and formal proof are separate
([`docs/status.md:67-70`](../../../docs/status.md#L67-L70)).

## 21. Stage 3.1 conclusion

The current architecture has a coherent central idea: one content-identified
Protocol binds a total transcript schedule to a linear, content-pinned claim
calculus, and immutable admission authority protects all downstream consumers.
Its most mature correspondences are grammar, claim accounting, local reduction
and terminal closure, positional identity, fail-closed artifact admission, and
supported endpoint projection.

Its present boundaries are equally important to the reconstruction. The
abstract kernel is broader than admitted PIR; relations remain external and
evidentiary; committed objects are flat; open linking is narrower than the
normative composition story; Interface and Plan responsibilities are
distributed; and four direct source conflicts plus the listed correspondence
gaps prevent the current documents, carrier, and consumers from being read as
one fully closed model without qualification.

This completes reconstruction of the current model only. It makes no selection
among later Stage 3 design alternatives.
