# K3-D Research and Selection

> **Document kind:** Temporary research and decision record
> **Document state:** Bounded research, selection, and executable revalidation
> complete; K3-E integration remains open
> **Provisional owner:** `project`, coordinating `pir` and `oir`
> **Authority:** None. Durable target rules live in
> [`pir/endpoint-projection-views.md`](../../../pir/endpoint-projection-views.md)
> and [`oir/projection-contract.md`](../../../oir/projection-contract.md).
> This record preserves research pressure, rejected candidates, bounded
> selection, and reopen conditions only.
> **Selection completed:** 2026-08-28

## 1. Question and non-goals

K3-D asked for the smallest source-to-endpoint contract capable of falsifying
the K1/K2/K3-B factorization before semantic freeze:

1. which exact Protocol, Interface, and Plan facts may an endpoint read;
2. what minimum target semantics makes local OIR validity nonvacuous;
3. what independent relation establishes complete graph and static-contract
   correspondence;
4. what enters OIR identity versus the semantic proposition and source-bound
   validation request/capability;
5. where unsupported imported, Oracle, Fresh, and module cases stop; and
6. whether any concrete pressure requires reopening K1, K2, or K3-B.

It did not attempt a final OIR MLIR grammar, a complete optimizer, endpoint
realization, backend support, protocol transformation, formal proof, or
cryptographic property.

## 2. Evidence inspected

### 2.1 Local source and target

The audit traversed the active K1/K2 definitions, all K2 owner-derived views,
Fiat--Shamir static and runtime boundaries, the K3-B Interface and Plan
subjects, canonical carrier, Relations and K3-C exclusions, current OIR
specification and implementation, realization scaffold, and P01/Schnorr
fixture. It compared current code and tests for exact coverage, transcript
schedule, prover/verifier duality, imported-verification refusal, grinding,
and standalone OIR admission.

The current system already demonstrates two useful separations: standalone OIR
admission is not source projection, and an authenticated Fiat--Shamir endpoint
can be checked for exact legacy source coverage. It also demonstrates the cost
of the old fused model: source positions, labels, routes, codecs, and whole
sealed-PIR identity enter endpoint material, so semantically irrelevant source
changes can rotate OIR and transcript identity. The target must retain the
former separation without copying the latter coupling.

### 2.2 Compiler and validation analogues

- [MLIR dialect conversion](https://mlir.llvm.org/docs/DialectConversion/)
  distinguishes target legality and full/partial conversion. This supports a
  closed OIR support table and fail-closed target admission, but target
  legality alone is not source semantic preservation.
- [CompCert](https://compcert.org/man/manual001.html) provides the opposite
  assurance pole: compiler-wide semantic preservation under explicit source
  and target semantics. K3-D does not have the complete languages or proof
  infrastructure needed to claim that model.
- [Alive2](https://github.com/AliveToolkit/alive2) validates individual
  source/target translations and states explicit unsupported boundaries, while
  also documenting restrictions such as interprocedural transforms. This is
  the closest architectural analogue for a separate local target check and
  source-relative relational validator.

The conclusion is not to copy any compiler framework. It is to keep target
legality, producer success, and source preservation as separate propositions,
and to make unsupported scope explicit.

### 2.3 ZK endpoint and protocol pressure

- [Linea's Wizard-IOP and Arcane pipeline](https://eprint.iacr.org/2022/1633)
  demonstrates that protocol compilation can deliberately change query and
  commitment structure across several semantic levels. Therefore ordinary OIR
  projection must not silently perform arithmetization, PIOP compilation,
  polynomial-commitment selection, or recursion; those require independently
  checked Protocol-level transitions.
- Plonky3 and Winterfell place AIR/configuration/public-value meaning at a
  caller-visible verifier boundary. This pressures exact source and Interface
  quotients rather than a target inferred solely from instruction shape.
- RISC Zero receipt composition makes image/claim and unresolved assumptions
  explicit. This pressures claim, reduction, terminal, and counterparty
  obligations as endpoint semantics rather than debug provenance.
- The [SP1 verifier advisory](https://github.com/succinctlabs/sp1/security/advisories/GHSA-c873-wfhp-wx5m)
  records a missing verifier consistency check in a production proof system.
  It is direct pressure against equating locally executable target code with
  complete source obligation coverage.
- Stone/StarkEx verifier boundaries separately expose public input and bind
  verifier configuration. This pressures Interface adequacy and makes ambient
  statement or configuration recovery unacceptable.

These systems are design pressure, not correspondence evidence for zkc.

### 2.4 Research revalidation after the execution-scope correction

The late static/dynamic split was checked again against the primary analogues.
MLIR full conversion establishes target legality and total legalization, but
does not itself state source-behavior preservation. Alive2 adds a separate
source/target refinement check and publishes an explicit unsupported boundary;
it does not infer a compiler-wide theorem from target validity. CompCert can
state whole-program semantic preservation precisely because both languages
and their behaviors are already defined. Wizard-IOP/Arcane shows that ZK
protocol compilation may change queries, coins, and commitment structure
across semantic levels rather than merely re-encode an endpoint.

These observations support the repaired boundary: K3-D may close a static,
exact, no-rewrite projection relation before a complete execution language
exists, but it must not label a partially specified trace relation as exact.
Nonidentity protocol compilation, dynamic endpoint execution, and concrete
wire realization require their own later semantics and checked relations.

## 3. Candidate portfolio

### Candidate A — authored source read manifest

The projector declares which source fields it read and the checker validates
only that declaration. Rejected: the producer can underdeclare the exact fact
it omitted. The manifest becomes self-authorizing.

### Candidate B — target-inferred source manifest

Infer all relevant source facts backward from target operations. Rejected:
the target cannot reveal why a source Statement, Plan recipe, codec, failure,
or claim should have existed. It recreates the source-position dilemma under a
different name.

### Candidate C — unique canonical functional projection

Define one total function from complete source subjects to one canonical OIR,
then compare equality. Deferred: it requires a complete OIR grammar and normal
form, rejects semantically equivalent schedules, and prematurely activates
Stage 4B.

### Candidate D — full trace refinement or bisimulation

State a complete execution-level source/target relation. Retained as the
eventual denotational ideal, but deferred: K3-D lacks complete OIR execution,
strategy, resource, and optimization semantics.

### Candidate E — owner-derived quotient plus independent relational checker

PIR derives exact purpose-specific whole-source-provenance-free views under a
literal recursively total read disposition. Exact Core or Construction IDs
that K2 consumes at runtime remain semantic operands. OIR independently
derives its target universes. A third checker validates exact source coverage
and semantic correspondence.

Selected. It prevents producer-selected omissions, leaves room for several
valid pure schedules under a future relational profile, does not require final
OIR syntax, and keeps local target validity separate from source correctness.
The selected bounded profile itself permits only the one canonical schedule
and uses exact graph equality.

## 4. Selected model

### 4.1 Purpose and views

The closed purpose grammar recognizes FS/Fresh verifier, generic prover, and
Plan-specialized prover endpoints. Bounded support is deliberately smaller:
FS verifier and FS Plan-specialized prover over base non-Oracle, non-module K2
effects and base Plan recipes.

PIR owns one purpose-specific `EndpointSourceView` assembled from three owner
components: K2 Protocol/Core/FS meaning, the role-filtered K3-B Interface
graph, and the reachable K3-B Plan graph. One shared 11-field semantic graph
prevents those components from becoming independently incomplete
correspondence planes.

The Plan closure seeds decision moves and `ReplaceState` payloads, then retains
the complete update row for every selected state. It excludes witness exports,
dead declarations/nodes, private-material keys, source maps, and full source
IDs. Those exclusions are not below-OIR inputs. Reachable recipes are endpoint
meaning; concrete suppliers belong to Realization.

### 4.2 Minimum OIR and projection

The minimum OIR body contains role, exact-used dependencies and types,
constants and pure nodes, role ABI, one action-bearing spine, static FS law,
claims, anchored reductions/terminals, and the optional reachable Plan graph.
A shared exact `EndpointContractLawV0` derives one closed
`DerivedEndpointContractBody`: a complete static-obligation index, exact
requirements, and a completion interface. Storing that result again inside
OIR identity was rejected as duplicate semantic authority. Giving it an exact
non-identity carrier closes independent `LocalOirValid` without recreating
authored effect tables.

A late falsification pass rejected the stronger protected-trace draft. Exact
runtime ports, guarded presence, state versions, draw instances and receipts,
decoder results, wire omission/tagging, scheduling, and reached outcomes need
path-dependent execution laws that K3-D does not own. Pretending to derive
them here would silently design Stage 4B and introduce unowned state joins.
They are therefore explicit Stage 4B non-claims. This narrowing does not
weaken static FS preservation: exact K2 framing, prefix, namespace, retry,
state-advance, decode, and global-failure laws remain in the identity-bearing
graph and exact projection equality.

Projection is a separate exact question. The first selected draft used six
disjoint correspondence planes, but schema cold audit found that it omitted
the value/control/static-FS/claim/outcome graphs while bounded v0 supported no
rewrite needing an existential map. The repaired profile therefore uses one
canonical `EndpointSemanticGraphBody` independently produced by PIR and OIR.
Projection checks exact graph equality and purpose/role compatibility. Four
negative role/dataflow conditions from the earlier draft are now source and
OIR formation laws over that complete graph; a second absence table was
removed as redundant. Both profiles select the same exact derived law, so base
graph equality also transfers the complete derived static contract.
Optimization, rescheduling, split/fusion, or ABI adaptation requires a later
named refinement profile rather than an exception in this one.

This remains translation validation rather than compiler certification: the
producer is unauthoritative, the target is admitted independently, and only an
affirmative source-relative equality check mints a process-local projected-OIR
capability.

### 4.3 Identity

`OirId` identifies target endpoint semantics and exact used semantic
dependencies. It excludes whole source IDs, view IDs, source maps, projector,
checker, capability, evidence, and runtime receipts. The semantic projection
proposition binds only purpose, source-view ID, target OIR ID, and relation
profile. Exact Protocol, Interface, optional Plan, manifest, live authorities,
checker, and limits bind the validation request and process-local
capability instead.

This permits two Plans that differ only in dead recipes or witness exports to
share a semantic prover OIR while keeping different source-bound projection
capabilities. A reachable recipe, ABI, action-spine operand, or static FS
change must rotate target semantics or make reuse projection-negative; a
derived static obligation cannot be changed independently.

### 4.4 Roles and failures

Both FS endpoints derive challenges locally. The Verifier owns checks and the
Protocol verdict. The Prover owns proof production, but K2 defines no semantic
Prover completion for K3-D to project: strategy `Stop`, unavailable authority,
and private search exhaustion remain operational noncompletion. Any host-level
successful generation return belongs to a later execution or Realization
contract. FS sampling exhaustion remains interpretation failure.

An explicitly trivial source verifier may contain no check. K3-D rejects a
target only when it erases a check the exact source requires; it does not turn
the current implementation's nonempty-check policy into a universal semantic
law.

Support classification precedes view extraction and proposition formation, so
`Unsupported` is not a late projection-check escape. The semantic proposition
names the source-view ID, OIR ID, purpose, and exact-equality relation profile.
There is no producer witness in bounded v0. Exact canonical comparison is a
complete decider, so a well-formed mismatch is Negative. Missing dependencies,
authority, formation, limits, and
operational failures retain their qualified variants. A projection Negative
is not proof rejection.

## 5. Important corrections made during selection

1. **Imported verification.** A legacy module carrier with no supported K2
   effect contract stops at PIR admission, so an OIR refusal is unreachable.
   A future already-admitted module effect with no OIR rule is the distinct
   projection-level Unsupported case. Bounded K3-D supports no module-effect
   arm, even if the effect is otherwise admitted.
2. **Interface sufficiency.** Interface admission does not require every
   endpoint transport. Projection therefore needs a role-specific Interface
   adequacy judgment; OIR cannot fill a missing slot ambiently.
3. **Base Plan placement.** The selected Plan contains no realization fields.
   The previous undefined `BelowOirPlanBasis` branch was removed rather than
   treated as a required future definition.
4. **Local validity versus correspondence.** A locally valid target that drops
   the P01 check remains locally valid but is projection-negative. This is the
   decisive discriminator.
5. **Oracle support.** K2 has a native Oracle, but K3-D lacks a nonleaking
   complete endpoint rule. The bounded profile says Unsupported rather than
   pretending coverage.
6. **Proposition and validation.** Checker identity, limits, and live handles
   moved out of semantic proposition identity and into the validation request.
   The producer correspondence map was removed entirely in the exact-equality
   profile.
7. **Prover completion.** The provisional generation-completion variant was
   removed after counterexample review showed that it had no K2 or K3-B owner.
   Proof-message production remains source semantics; host return remains
   downstream.
8. **Claims and reductions.** Static claim, reduction, publication, and
   terminal-closure obligations are anchored graph tables rather than invented
   runtime effects. Each reduction output retains its ordinal, contract, and
   complete possibly-empty/multiple matching claim-ref list; K2 never promised
   one named claim per output.
9. **K2 transcript coordinates.** Original scope, binding, occurrence, and
   challenge ordinals that K2 hashes are semantic scalar operands and are not
   rebased as provenance. Ordinary graph refs remain local.
10. **Per-draw namespace.** The provisional static namespace datum was replaced
    by the exact K2 namespace recipe with runtime draw ordinal `i`.
11. **Complete ABI and control.** Flat ABI atoms were replaced by the complete
    codec/slot/fibre/Statement/transport/completion graph, and the quotient now
    contains constants, pure nodes, total spine order, complete reductions,
    and terminal closure.
12. **Bounded equality.** The incomplete existential six-plane relation was
    replaced by exact canonical semantic-graph equality. General refinement
    remains a separate future profile.
13. **Fixed owner law.** A large serialized schema/rule DAG was replaced by a
    pinned five-root grammar traversal and fixed disposition law. This removes
    an unconstructible duplicate schema while keeping exact owner-coordinate
    receipts, multi-sink reads, complete selected/complement partitions, and a
    separate dependency-preimage ledger.
14. **Derived requirement closure.** Locally demanded pure-node and exact
    static algorithm-use,
    General-codec presentation-path, counterparty, private-material,
    randomness, and state-storage requirement keys are derived exactly.
    General-codec certificates remain admission-only. K2-public Check outputs
    needed by a Prover are reconstructed without creating a second Check
    effect or Verifier authority.
15. **One FS failure.** The construction owns one exhaustion failure. Exact
    framing, per-draw namespaces, state advance before acceptance, retry,
    decode, and exhaustion remain one imported K2 law; K3-D neither copies
    them into each challenge nor manufactures runtime draw rows.
16. **Closed static carrier.** A late cold audit found that the first shared-law
    draft promised a complete protected micro-trace before runtime state and
    wire semantics existed. The repaired law returns the exact static contract
    only. Source extraction uses original K2 public-coin coordinates before
    rebasing; source-blind OIR admission independently reruns graph-local
    `EndpointPublicClosureV0`.
17. **Execution-scope correction.** Dynamic protected traces, presence,
    path-sensitive state, draw instances, codec results, transport packaging,
    and runtime outcomes are explicitly owned by Stage 4B. This was a design
    correction, not a loss of source semantics: all static laws and
    obligations needed by that later execution remain exact.
18. **Pairing deferred after falsification.** The first pair request consumed
    two projection capabilities over one source tuple, making semantic
    Negative vacuous. A second candidate consumed independently admitted OIRs,
    but its role-neutral normalizers were not closed canonical languages: codec
    expansion, roots, rebasing, duality, mismatch partition, and output/work
    bounds remained implicit. K3-D therefore selects no authoritative pair
    proposition or capability. A finite same-fixture comparison may remain a
    pressure probe, while exact target-only pairing moves to the Stage 4B OIR
    owner.

## 6. Reopen verdict and residual work

No K3-D case currently requires reopening K1, the K2 Core/Fiat--Shamir model, or K3-B
Interface/Plan identity. K3-D did reopen and replace older Stage 1/2 OIR
identity and below-Plan candidates because they conflicted with the now-exact
consumer model.

Reopen K2 only if a concrete endpoint needs a verifier-observable effect,
presence state, failure, terminal, influence relation, or prover view that K2
cannot derive. Reopen K3-B only if one exact role ABI or reachable Plan semantic
fact cannot be represented without ambient state. Reopen K3-D for a concrete
Fresh, Oracle, module, generic-prover, optimization, or complete-execution case
only with a positive inhabitant, same-boundary negative, exact identity effect,
and smaller rejected alternative.

K3-E still must audit the joined K1/K2/K3-B/K3-C/K3-D boundary. K4 must pressure
the protocol portfolio. Full OIR syntax/execution and Realization remain behind
a separate Stage 4B activation. The bounded Python instrument is a structural
falsifier; unless it implements the exact K1 `MetaValueV0` bodies, its
JSON-based canonical IDs remain modeled surrogates and cannot be cited as
K1/OIR byte-parity vectors.
