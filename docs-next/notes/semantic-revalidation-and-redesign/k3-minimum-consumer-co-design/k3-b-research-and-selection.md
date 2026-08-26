# K3-B Dependent Surfaces: Research and Selection

> **Document kind:** Temporary research, selection, and falsification record
> **Document state:** Bounded K3-B complete
> **Provisional owner:** `project`, coordinating `pir` and `relations`
> **Authority:** None. Selected contracts become target semantics only in their
> durable owners. This record cannot override those owners or current `docs/`.
> **Started:** 2026-08-27
> **Completed:** 2026-08-27
> **Disposition:** Retain until K3-E confirms that all selected rationale and
> deferrals have durable homes, then delete with the K3 workspace.

## 1. Question and bounded method

K3-B asks whether the closed K1 value/identity substrate and K2
Protocol/Fiat--Shamir kernel expose enough exact meaning for Interface, Plan,
Relations, execution grounding, and a canonical carrier without adding a
second Protocol model or reopening the Core.

The selection was not made by renaming pre-K2 fields. The work compared:

1. the exact K1 and K2 bodies and source views;
2. the pre-K2 Interface, Plan, Relations, correspondence, and carrier pages;
3. current R1CS, relation, projection, and imported-verification behavior as
   regression pressure rather than target authority;
4. primary sources for oracle reductions, R1CS/AIR interfaces, IOP/FRI,
   folding, protocol compilers, and MLIR carriers; and
5. positive inhabitants and same-boundary mutations across the K3-B case
   matrix.

The decisive criterion was constructibility of the minimum consumer questions
`REL-Q1`--`REL-Q4`, not similarity to the current implementation.

## 2. Research pressure and design inferences

| Source or case | Source pressure retained | K3-B inference; not a source claim |
|---|---|---|
| [ArkLib oracle reductions](https://verified-zkevm.github.io/ArkLib/blueprint/chap-oracle_reductions.html) | Public statement, private witness, oracle statements, shared oracles, and input/output relations are distinct; prover and verifier derive output statements separately. | Reductions require ordered input/output relation occurrences, distinct public/witness/oracle transforms, and an explicit output-agreement obligation. Security and completeness remain Analysis questions. |
| [zkInterface](https://github.com/QED-it/zkinterface) | Circuit header, constraint system, public variables, and witness messages are separate and ordered. | Mathematical definition, public instance, private witness, artifact layout, and streaming are separate subjects or judgments. Equal lengths or serialization positions do not ground semantics. |
| [Halo2 arithmetization](https://zcash.github.io/halo2/concepts/arithmetization.html) and [Plonky3 AIR](https://github.com/Plonky3/Plonky3/blob/main/air/src/air.rs) | Fixed, instance/public, advice/trace, preprocessed, and periodic data have different roles. | `Statement`, public parameter, relation witness, advice, phase input, and randomness cannot be collapsed into public/private. |
| [IOPs and BCS](https://eprint.iacr.org/2016/116.pdf) and [FRI](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.14) | Logical Oracles, commitments, queries, values, authentication paths, and verifier checks are different objects and occurrences. | Use K2 Oracle/effect/value coordinates plus a typed commitment-grounding graph. A commitment root is not an Oracle or a lossy value bridge. |
| [Nova](https://crypto.iacr.org/2022/papers/538806_1_En_13_Chapter_OnlinePDF.pdf) and [HyperNova](https://www.andrew.cmu.edu/user/bparno/papers/hypernova.pdf) | Folding consumes ordered relation instances and produces a new relation instance; committed instances, witnesses, openings, accumulators, and later compression are distinct. | Claims and reductions need occurrence-explicit, potentially n-ary and relation-changing graphs. Exact many-to-one relation refinement is not computationally priced value loss. |
| [MLIR dialect definition](https://mlir.llvm.org/docs/DefiningDialects/) and [bytecode format](https://mlir.llvm.org/docs/BytecodeFormat/) | Dialect operations, properties, interfaces, and bytecode versioning are extensible implementation mechanisms. | Canonical PIR fixes one closed physical profile and exact inverse read law; parser acceptance and generic MLIR extensibility grant no semantic authority. |
| Schnorr and verifier-private Fresh fixtures | One public value can be both invocation input and scoped Statement; a verifier-private input can be valid for Fresh while unavailable to the prover and ineligible for FS if it reaches a public-coin sink. | Interface assignment must cover both invocation maps while Statement coverage remains a separate occurrence graph. |
| Native Oracle/FRI boundary | Publication, challenge, query, answer, claim reduction, and repeated equal values have distinct positions. | K2 typed occurrences are sufficient at this boundary; no generic `ObjectRef` is currently justified. |
| `sha256-216` | The shipped 256-to-216 mapping has constructible digest collisions; the existing security game additionally needs adversary-supplied preimages. | A lossy value projection names its collision relation and derives exact uses. Analysis prices only a separately established premise; discarded bits alone are not hardness. |

Primary sources constrain the model but do not select zkc identities,
capabilities, or carrier spelling. FRI/BCS and folding remain constructive K3-B
pressure until K4 runs their full protocol witnesses.

## 3. Selected dependency graph

```text
K1 values, algorithms, modules, and typed semantic identity
       |                         |
       v                         v
K2 Protocol ----------------> ProverPlan
       |                         |
       |                         v
       |                  PlanWitnessSurface
       v                         |
ProtocolRelationBinding          |
       ^                         v
       |                  PlanWitnessBinding
       +-------- RelationInterface

ProtocolInterface is an independent presentation of Protocol.
Checked correspondence combines exact operands; it is not another root.
```

The dependency direction is load-bearing:

- `ProtocolInterface` and `ProverPlan` depend on one exact `ProtocolId`;
- neither contains a Relations-owned identity;
- `RelationInterface` depends only on K1 meaning;
- `ProtocolRelationBinding` depends on Protocol and relation meaning, but not
  on an external Interface or Plan;
- `PlanWitnessBinding` depends on a PIR-owned witness view and relation
  meaning, but not on Protocol correspondence; and
- a checked aggregate may combine these facts without becoming a new semantic
  owner.

This avoids both a literal dependency cycle and unnecessary identity coupling.
One strategy may serve multiple relation presentations, and one verifier-side
relation correspondence may be assessed without choosing a prover.

## 4. Interface and Plan selection

### 4.1 Interface

The selected Interface has four independent surfaces:

1. decoded external value slots and exact K1 codecs;
2. a total target map over every public and verifier-private
   `CoreInvocation` input, with role-derived visibility;
3. an external-Statement-to-scoped-`BindingRef` occurrence graph; and
4. role-qualified transport and completion presentation over exact K2 effects.

External slot reuse is explicit. Every invocation target occurs exactly once;
every declared slot must be used by assignment, Statement presentation, or
transport. A public input is not automatically a Statement, and a derived
child-scope Statement is not invented as an invocation input.

Transport binds external channels to guarded K2 message, challenge, Oracle,
module-observation, terminal, or interpretation-failure coordinates. It does
not author visibility, occurrence activity, or Fiat--Shamir framing. A Fresh
challenge may be verifier-to-prover transport; an FS challenge is derived and
need not occupy the proof ABI.

### 4.2 Plan

The selected Plan identifies one structural implementation of K2's strategy
decision boundary. Its private roles are disjoint:

```text
WitnessIngress | Advice | ConfidentialContext
PrivateRandomnessRequirement | PersistentStrategyState
```

It may also expose explicitly typed `DerivedWitnessExport` coordinates.
Relation-specific meaning is attached later; neither ingress nor export names
a `RelationInterfaceId`.

Decision routes are total over potential K2 `ProverDecisionPoint`s. Operands
may name only the exact current `ProverView`, declared private material,
randomness, prior state, and prior Plan-node outputs. Routes fix legal move
constructors, payload types, and state updates. Realization-only scratch,
search queues, scheduling, resources, providers, and deployment facts are not
semantic Plan fields.

`PlanRealizes` checks decision coverage, typing, causality, state closure,
exact dependency use, and confinement. It does not prove witness satisfaction,
move correctness, randomness quality, termination, honest-prover
completeness, or security.

### 4.3 Narrow witness surface; OIR views deferred

K3-B selects exactly one source-ID-free Plan projection:
`PlanWitnessSurface`. Its identified body contains the Protocol ID and a keyed
map of witness role, exact value type, and occurrence class. It contains no
`ProverPlanId`, Plan-local node, decision reference, private source, or checked
derivation ID. A process-local checked extraction retains the exact source Plan
and private back-map without placing either in the surface identity.

This narrow quotient is sufficient for Relations witness attachment and
repairs the old Plan/OIR identity contradiction at the one seam K3-B actually
needs. K3-B does **not** select a generic purpose-view constructor. Concrete
Interface and Plan projections for OIR remain K3-D work; each must define its
own closed purpose grammar, exact read manifest, normalized view body, checked
extraction, and identity effect.

## 5. Relations selection

### 5.1 Relation subjects

`RelationDefinition` is a K1 semantic subject over exact used modules, one
typed relation-kind declaration, and a canonical definition payload. It does
not identify artifact bytes or a proving layout.

`RelationInterface` gives ordered, typed occurrences in four roles:

```text
PublicInstance | PrivateWitness | OracleStatement | PhaseInput
```

`RelationInstance` supplies every public-instance occurrence, public Oracle
binding, and phase-input value. A phase value may be formed abstractly once it
exists; whether it came from the exact challenge or reduction occurrence is a
separate protocol/run-grounding question. Private witness and Oracle
assignments use distinct owner-local capabilities; neither secret receives a
portable content-derived identity.

### 5.2 Two bindings and one occurrence graph

`ProtocolRelationBinding` contains relation occurrences plus exact maps for:

- relation public inputs to scoped Statement bindings;
- phase inputs to challenges or derived public occurrences;
- public Oracle/material roles to Oracle or effect occurrences;
- relation meanings to K2 claims; and
- ordered input/output relation meanings to K2 reductions.

`PlanWitnessBinding` maps every relation witness occurrence to a legal
`WitnessIngress` or `DerivedWitnessExport` entry in one exact
`PlanWitnessSurface`.

Mappings are occurrence graphs, not global value-keyed functions. Equal values
and repeated uses never alias. A question may separately demand functional,
injective, mapped-only, or whole-surface coverage.

Claims and reductions remain structural resources and transitions. A
reduction declaration records ordered input/output relation occurrences,
public-instance transformation, witness transformation, Oracle/material
evolution, and any prover/verifier output-agreement obligation. Its shape does
not prove any claim true or any property preserved.

### 5.3 Three value bridges, plus relation refinement

The exact value-representation bridge sum remains:

1. total isomorphism with both inverse laws;
2. injective embedding with exact image predicate and inverse on the image;
3. directional lossy projection with no inverse claim, an exact collision
   relation, exact source/target occurrence uses, and an Analysis loss hook.

Lossy use count is derived from distinct canonical binding uses; it is not an
authored number. K3-B permits quantitative consumption only at its closed
run-grounded relation-instance seam, where every counted use has an exact live
source binding and consumer join. Structural Plan and artifact mappings carry
no implicit count claim. A preimage or security premise is an independently
checked source, never a bridge default.

Bridge meaning contains only endpoint types and exact algorithms. Exhaustive
controls, certificate-law declarations, certificates, assumption evidence,
and evaluator limits are external validation basis. The same separation
applies to definition/model and refinement propositions: validation material
is bound into a checked result, never hashed into the proposition or bridge
identity. K3-B supports owner-derived exhaustive checking only for K1 domains
whose complete enumeration follows mechanically from the closed root grammar;
definition/model and refinement checks retain only their exact certificate
lanes until their stronger quantified finite semantics is defined.

Many-to-one transformations such as committed-relation-to-base-relation
projection are **not** a fourth value bridge. They use a separately typed
`RelationTransform` or `RelationRefinement` contract that states the exact
relation-preservation direction and witness/public/material transformations.
Commitment construction/opening is likewise a separate
`CommitmentGrounding` contract.

### 5.4 Artifact and grounding algebra

Artifact interpretation is expectation-free. An exact profile declares typed
fact fields and finite multiplicities; each observation is:

```text
Unread | Observed(CanonicalSeq<CanonicalValue>)
```

Thus observed absence is distinct from unread. A selector is
`At(field, ordinal)` or `Whole(field)`. Comparisons state exact typed
expectations and return field-factored agreement or disagreement.

A grounding equation is a finite acyclic typed DAG of exact source
coordinates and K1 algorithm applications, followed by explicit equality
clauses and one canonical evaluation order. False equality is a completed
negative. Missing authority, missing facts, unsupported algorithms, malformed
typing, or checker failure retain their own qualified outcomes.

### 5.5 Structural, external, run, and satisfaction questions

K3-B keeps four questions separate:

1. mapped structural correspondence of requested edges;
2. optional whole Statement or witness-surface coverage;
3. external Interface/instance correspondence after decoding; and
4. run-grounded correspondence over a PIR-issued occurrence view.

The PIR run view binds exact `ProtocolId`, invocation, completed record,
source occurrences, types, and values. It is derived either during generation
or after affirmative K2 replay over the exact invocation. Optional causal
provenance is retained only when separately live. A caller tuple, raw record,
equal value, or stored `CheckedReplayMatch` identifier cannot mint the view.

Relation satisfaction remains an occurrence-local Relations operation over an
exact semantic model, instance, phase inputs, private witness/Oracle
capabilities, and assumptions. It is independent of structural or run
correspondence and produces no automatic soundness, knowledge, or endpoint
claim.

The selected evaluator meaning is an identity-bearing deterministic command
machine. Exact K1 `start` and per-Oracle `resume` algorithms can return
`Decide(Boolean)` or one typed Oracle query carrying the next private state.
Only the Relations-owned driver holds restricted lookup capabilities and feeds
the same-ordinal answer back to the machine. Thus implementation providers
cannot choose relation truth, Portable Algorithms never receive secret Oracle
material or capabilities, and limit exhaustion remains noncompletion rather
than `false`.

## 6. Canonical carrier selection

Canonical PIR is a factor-preserving single-root MLIR graph carrying exactly
one `(InteractiveCore, Protocol)` pair. Every field of the K2
`InteractiveCoreBody` appears once in its fourteen-field order:

```text
used modules; public inputs; verifier-private inputs; constants;
derived values; scopes; bindings; challenges; Oracles; checks;
claims; reductions; terminals; occurrences
```

The Protocol root carries the exact Core body/ID, `Fresh` or
`FiatShamir(TranscriptConstructionId)`, and the claimed `ProtocolId`. For FS,
the complete construction body and its dependencies remain external
authentication inputs. Module bodies, imports, algorithms, contracts, and
prior-meta preimages are likewise external; the graph carries their exact
typed references and direct used-module set.

The carrier API is pair-valued:

```text
Lower_B : (InteractiveCore, Protocol over that Core) -> CanonicalPirGraph
Read_B  : CanonicalPirGraph -> (InteractiveCore, Protocol)
```

Both inverse laws hold over the authenticated canonical graph domain, modulo
only in-memory MLIR identity and unavoidable SSA alpha-renaming. The reader
cannot synthesize an external transcript construction or dependency body.

Typed local ordinals are body-local. Durable coordinates include the exact
owner identity:

```text
CoreRef<K> = (CoreId, K, ordinal)
ProtocolScopedRef<K> = (ProtocolId, CoreRef<K>)
```

Final operation mnemonics, textual assembly, and bytecode policy remain later
work. Unknown carrier syntax is malformed, while a known admitted
`ModuleEffectRef` with no supported evaluator is semantically unsupported.
Those outcomes must not collapse.

Imported verification is represented by one exact-used module effect whose
typed payload may retain the child Protocol coordinates, independently
specified semantic verifier algorithms and evaluation contracts, proof-input
ABI declarations, nominal claim contracts, and exact semantic parameters.
Concrete artifacts, Protocol Interfaces, Plans, relation correspondences, OIR,
and Evidence remain satellites and cannot select Core semantics. Carrier shape
does not claim successful child verification. K3-D must return typed
`Unsupported` until it has a complete OIR projection and execution rule;
partial lowering is forbidden.

## 7. Rejected alternatives

| Alternative | Reason rejected at K3-B |
|---|---|
| Patch old ports, objects, randomness, and obligation names | Their K2 sources do not exist; renaming would preserve false authority and unreachable checks. |
| Put `RelationInterfaceId` in `ProverPlan` | Adds unnecessary Relations-to-PIR coupling, rotates equivalent strategies, and forces Plan admission to consume later-owner authority. |
| One monolithic relation binding | Couples verifier correspondence to a particular prover and external presentation. |
| Bind whole `PlanId` into OIR | Unread changes rotate OIR and reproduce the recorded contradiction. |
| Put source-qualified references inside a purpose view | The full source ID leaks transitively into the quotient and defeats stability. |
| Treat every private value as witness | Misclassifies advice, confidential context, randomness, state, and search. |
| Treat Oracle data as witness or commitment root as Oracle | Erases distinct query-access, publication, and opening semantics. |
| One bridge with optional flags | Permits an embedding or lossy map to pose as equivalence and hides which laws were checked. |
| Put certificates, exhaustive controls, or evidence in semantic identity | Rotates stable meaning when only validation method changes and permits replay material to masquerade as proposition content. |
| Trust an evaluator callback to return satisfaction | Leaves two providers free to assign opposite truth values under the same semantic IDs and gives no enforceable Oracle-access law. |
| Treat committed relation refinement as lossy value projection | Confuses exact logical abstraction with computational security loss. |
| Caller-created run tuple | Cannot establish what the exact verifier execution consumed. |
| Generic Protocol `ObjectRef` | No current executable or constructive case needs it; typed K2 values, Oracles, effects, and occurrences remain sufficient. |
| Extend the current TableGen additively | The current token/slot carrier encodes a different semantic model; target migration requires a replacement boundary after freeze. |

## 8. Validation matrix and strength

| Case | K3-B strength | Decisive observations |
|---|---|---|
| Schnorr/Sigma | P01 non-regression plus finite K3 attachment cases | public input versus Statement; proof ABI; witness/randomness/state separation; wrong scope/value/occurrence. The K3-B instrument does not execute claim/reduction meaning. |
| Verifier-private Fresh | New executable boundary | total invocation assignment, role isolation, Fresh success, FS refusal only when private influence reaches a live public-coin sink |
| R1CS/AIR | Finite typed attachment fixture plus malformed controls | definition/layout split; public/witness order; artifact facts; phase-input shape. No R1CS/AIR proving or satisfaction execution. |
| Sumcheck/native FRI | Finite public-Oracle interaction boundary | publication, query, answer, repeated-occurrence selection, and public run-view attenuation. No complete FRI or reduction-meaning execution. |
| Nova/HyperNova | Structural folding-shaped fixture | n-ary/relation-changing shape and accumulator/witness/state/material separation only; no executable relation/reduction graph. |
| `sha256-216` | Existing executable probe plus source/use mutation | three lane separation; derived occurrence count; missing preimage premise |
| Imported verification | Carrier/exclusion discriminator | imported-verification remains a semantic module field and K3-D must refuse partial lowering; no child-verifier or field-by-field OIR execution is claimed. |
| K2 carrier | Finite lower/read boundary fixture | tagged round trip and literal disposition manifest over the bounded legacy K2 executable shape, Fresh/FS same Core, external construction dependency, coordinate mutation, and satellite exclusion. The durable fourteen-field disposition is a specification selection, not an executable fixture result. |

Full FRI/BCS execution, R1CS/AIR proving, folding/IVC execution, actual child
verification, final MLIR spelling, and broad protocol-family coverage remain
outside the K3-B claim.

## 9. K2 reopen verdict and K3 handoff

No K3-B case currently requires a new K2 identity-bearing field or generic
object. The selected downstream surfaces can name every required fact through
K1 types and K2 inputs, bindings, occurrences, Oracles, module effects,
claims, reductions, terminals, and owner-derived views.

K2 reopens only if an executable K4 case demonstrates a verifier-observable
material object, legal prover-view fact, or acceptance-relevant effect that
none of those coordinates can represent without an ambient read or authored
mirror.

K3-B hands K3-C exact relation, run, bridge-use, claim/reduction, and optional
causal sources. K3-C must still define adversary/game semantics, theorem
applicability, relation-bound properties, and quantitative loss. K3-D receives
the purpose-view factorization, complete carrier source, typed effects, and
imported-verification refusal obligation; it still owns the exact OIR read set,
identity effect, coverage, and source-relative projection result.

The bounded gate, repaired falsifiers, and exact evidence limits are recorded
in [K3-B Validation](k3-b-validation.md). Completion here does not freeze the
semantic kernel, establish implementation conformance or a cryptographic
proof, close K3-C or K3-D, or activate Stage 4B.
