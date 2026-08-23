# ZK-system protocol, relation, and carrier boundaries

> **Document kind:** Temporary primary-source comparative research dossier
> **Document state:** Stage 3.2 comparative research complete; absorbed into
> completed Stage 3 convergence
> **Stage:** Stage 3 — Protocol, canonical PIR, and Relations co-design
> **Cases:** zkInterface, Noir ACIR/Brillig, Halo 2, Marlin, STARK/AIR with
> Winterfell, Plonky3, and Nova/HyperNova
> **Authority:** None. Source facts describe the named systems. Design
> inferences and zkc transfers are research hypotheses, not selected Stage 3
> semantics, admitted schemas, implementation correspondence, or proof claims.
> **Research snapshot:** 2026-08-22. Repository links to `main` or `master`
> are mutable and must be rechecked before later reliance.
> **Disposition:** Absorb reviewed findings into Stage 3 candidate comparison,
> convergence, and the exact durable owner; then delete this dossier.

## 1. Question and selection method

This dossier asks what mature proof-system theories, interchange formats, and
libraries actually make first-class when they represent a relation or execute
a proof protocol. It is deliberately narrower and deeper than the Stage 1
[ZK-adjacent IR survey](../../stage-1-ir/cases/zk-proof-adjacent-irs.md):
the concern here is the joint boundary among Protocol/PIR and Relations.

The comparison examines:

- the identity-bearing protocol and relation subjects, if any;
- relation definition, public instance, private witness, and witness-building
  separation;
- transcript messages, challenges, causal phases, and terminal checks;
- committed objects and how they are grounded in the relation;
- static assembly, batching, recursion, folding, and other forms called
  “composition”;
- verifier-facing interfaces and prover-side construction plans;
- proof, key, and relation serialization or versioning; and
- choices that were rational locally but became expensive interoperability or
  evolution boundaries.

The set is intentionally heterogeneous:

1. **zkInterface** is a serialized relation-and-witness interchange protocol.
2. **ACIR/Brillig** is a compiler/backend IR with both constraints and witness
   computation.
3. **Halo 2** is a tightly integrated PLONKish protocol and circuit library.
4. **Marlin** gives an explicit theoretical and implementation factorization
   of an indexed relation, a public-coin AHP, a polynomial commitment scheme,
   and Fiat--Shamir.
5. **STARK/AIR and Winterfell** expose the relation-to-protocol boundary and
   challenge-dependent arithmetization phases.
6. **Plonky3** is a highly modular toolkit in which protocol closure is largely
   expressed through Rust configuration and ordered prover/verifier code.
7. **Nova/HyperNova** make composition itself a protocol over committed
   relation instances and expose why occurrence structure matters.

Only papers, official documentation, schemas, and first-party repositories are
used for source facts. Project issues are used only as first-party records of
an acknowledged design pressure, never as a ratified specification.

## 2. Central findings

### 2.1 There is no existing universal “ZK IR” subject

The surveyed systems stabilize different layers:

```text
zkInterface             serialized R1CS relation and assignment messages
ACIR                    backend-facing constraint program plus solver hints
Halo 2                  PLONKish circuit, keys, and one concrete proof schedule
Marlin                  indexed relation + AHP + PCS + Fiat--Shamir compilation
AIR / Winterfell        trace-validity relation plus one concrete STARK schedule
Plonky3                 composable proof-system mechanisms and executable schedule
Nova / HyperNova        folding and IVC over committed relation instances
```

None provides a language-independent, closed object whose meaning jointly
includes arbitrary interactive events, exact relation ingress, Fiat--Shamir
interpretation, multi-Protocol composition, and a portable verifier-facing
interface. That absence supports a Protocol IR, but it does not determine its
grammar.

### 2.2 Relation, protocol, plan, and carrier recur as distinct axes

Across the cases, at least four separations repeatedly appear even when an API
later fuses them:

```text
relation meaning          what instance/witness pairs satisfy a predicate
protocol meaning          what messages, coins, checks, and outcomes occur
construction plan         how witnesses, traces, or prover messages are produced
carrier                   how circuits, keys, proofs, and messages are encoded
```

zkInterface stops at the first and fourth axes. ACIR includes relation meaning
and construction hints but not the backend protocol. Halo 2, Winterfell, and
Plonky3 expose all four through code and types, but do not package them as one
portable semantic subject. Marlin separates the layers most clearly in theory,
then specializes them again in its library. Nova demonstrates that a
composition construction can create a new relation and a new protocol rather
than merely connect existing proof objects.

### 2.3 The Fiat--Shamir input is part of Protocol meaning

The strongest implementation evidence is not “these systems use a hash.” It is
that the exact absorbed sequence changes which challenge is sampled.

- Marlin initializes Fiat--Shamir from a protocol label, indexed verifier key,
  and public input, then absorbs each round's commitments and prover message,
  later evaluations, before sampling the corresponding challenges. See the
  first-party [Marlin implementation](https://github.com/arkworks-rs/marlin/blob/master/src/lib.rs).
- Halo 2 writes proof elements and hashes them through the same transcript
  interface; its proof encoding follows the protocol transcript. See
  [Halo 2 proofs](https://zcash.github.io/halo2/design/implementation/proofs.html).
- Plonky3's prover explicitly observes trace dimensions, commitments, and
  public values before sampling challenges. Its source also records that some
  AIR-defining data remains ambient rather than directly observed. See the
  [uni-STARK prover](https://github.com/Plonky3/Plonky3/blob/main/uni-stark/src/prover.rs).

**Design inference.** A hash or challenger identifier alone cannot identify a
Fiat--Shamir Protocol. The construction must close over typed observation
events, their order, their codecs or canonical encodings, domain separation,
challenge domains, rejection/resampling behavior, and any public parameters or
identities that are ambient in an implementation.

### 2.4 “Composition” names several non-equivalent constructions

The cases use the word for materially different relations:

| Construction | Example | What it changes |
|---|---|---|
| Static relation assembly | zkInterface gadgets; Halo 2 chips | Builds one larger relation before proving |
| Shared proving of several instances | Halo 2 multi-instance proofs | Runs one specialized protocol over several instances with shared components |
| Argument compilation | Marlin AHP plus PCS | Replaces oracle access with commitment/opening subprotocols |
| Batch STARK proving | Plonky3 batch-STARK mechanisms | Creates a particular combined protocol and transcript |
| Recursive verification | verifier circuit inside a proof system | Makes acceptance of child proofs part of an outer relation |
| Folding | Nova/HyperNova | Transforms several committed relation instances into an accumulator instance |
| IVC/NIVC | Nova/HyperNova | Repeats an augmented step relation while carrying a recursive invariant |

These cannot be represented faithfully by graph union, artifact concatenation,
or transition adjacency. Each has different identities, occurrence maps,
public interfaces, schedules, assumptions, and property-transport obligations.

### 2.5 Modularity without semantic closure moves meaning into ambient code

Plonky3's field, extension field, challenger, hash, PCS, FRI, AIR, and security
parameters are powerful independent components. Halo 2 parameterizes curves,
transcripts, circuits, and layouts. Winterfell parameterizes AIR, fields,
hashes, random coins, and proof options. Their flexibility is valuable, but a
verifier must still possess the exact compatible combination.

The first-party
[Plonky3 universal-verifier proposal](https://github.com/Plonky3/Plonky3/issues/511)
therefore identifies field, hash, challenger, PCS, opening protocol, AIR shape,
security parameters, verification-key content, serialization, and versioning
as interoperability dimensions. The proposal is evidence of the pressure, not
an adopted solution.

**Design inference.** zkc should learn from component modularity without
allowing a canonical Protocol to remain semantically open. A component choice
that can change transcript observations, accepted proofs, public values,
commitment interpretation, or terminal outcome is semantic input, even when a
host language can infer it from a generic type.

## 3. Comparative object map

| Case | Relation subject | Instance and witness | Protocol schedule | Plan or hidden executor | Carrier/evolution boundary |
|---|---|---|---|---|---|
| zkInterface | R1CS constraints over one field and variable namespace | `Circuit.connections` plus `Witness` assignments | Out of scope | Gadget instance/witness reduction | FlatBuffers messages, length framing, `zkif` magic; proof/key formats excluded |
| ACIR/Brillig | Ordered backend-facing constraint opcodes | Named public/private witness sets and a witness map | Backend-owned, out of ACIR | Brillig, directives, solver order, black-box backend lowering | Tagged serialized Rust schema plus compressed program bytes; capability meaning remains profile-dependent |
| Halo 2 | Ordered PLONKish configuration and assignments | Instance, advice, and fixed columns | Concrete PLONK, lookup, quotient, opening, and PCS transcript | Circuit synthesis, chips, layouter, floor planner | Opaque proof byte stream whose length/order depends on circuit configuration |
| Marlin | Indexed R1CS relation | Index, public input, witness; index keys | Explicit multi-round AHP compiled with PCS and Fiat--Shamir | Constraint synthesis and round-specific prover algorithms | Typed proof and keys specialized to field, PCS, and FS implementation |
| Winterfell | AIR transition/boundary predicate | Public inputs plus main/auxiliary trace | Concrete STARK verifier and Fiat--Shamir-derived randomness | Trace builder and `Prover` strategy | Proof carries protocol data/options; verifier still receives AIR type and external acceptance policy |
| Plonky3 | AIR evaluated by a builder | Public values, main/preprocessed traces | Ordered code over generic challenger and PCS | Trace generation plus generic Rust configuration | Proof/config are library types; universal encoding/profile remains an explicit design problem |
| Nova/HyperNova | Committed relaxed R1CS or CCS and augmented step relations | Public accumulator instance, committed witness/error, private openings | Folding rounds, Fiat--Shamir compilation, recursive update | Step circuit, public parameters, folding and compression strategy | Library types specialize curve cycle and commitments; no protocol-neutral interchange format |

## 4. zkInterface: relation interchange, not proof-protocol interchange

### 4.1 Source model

**Source fact.** zkInterface divides communication into `Circuit`,
`R1CSConstraints`, and `Witness` messages. A complete circuit's incoming
connections are the proof's public inputs. Constraint generation and witness
generation may run separately, and multiple constraint or witness messages are
defined by concatenation. Variable identifiers are unique in one global
constraint-system namespace; gadget call/return messages carry connection
variables and a `free_variable_id`. See the
[zkInterface proposal](https://docs.zkproof.org/pages/standards/accepted-workshop3/proposal-zkinterface.pdf)
and its
[FlatBuffers schema](https://github.com/QED-it/zkinterface/blob/master/zkinterface.fbs).

**Source fact.** The format specifies canonical little-endian field values,
typed FlatBuffers roots, a `zkif` file identifier, and length-prefixed message
framing. It permits general `KeyValue` information for names, types, hints,
configuration, and other complementary data.

**Source fact.** The proposal explicitly excludes backend proof algorithms,
proof formats, and proving/verification-key formats. Its initial normative
relation language is R1CS; other constraint systems were future scope.

### 4.2 What it gets right

The interface makes several boundaries operationally real:

- a relation can be generated without a witness;
- witness reduction is not relation construction;
- a gadget's input/output connection is distinct from its local variables;
- a backend can consume streamed relation and assignment messages without
  knowing the frontend's implementation; and
- transport framing can remain independent of in-process, subprocess, pipe,
  or file deployment.

This is strong precedent for a relation-ingress interface that does not require
one compiler or one address space.

### 4.3 Path-dependent constraints

The format's interoperability target made several rational choices that do not
scale into a Protocol semantic model:

1. **Global numeric allocation.** Gadget composition relies on one monotonically
   coordinated variable namespace. Alpha-renaming is mathematically possible,
   but identity and composition are operationally tied to allocation order.
2. **Roles by convention.** Whether a connection is input, output, local, or
   public depends on call position and convention rather than a general typed
   relation-interface object.
3. **Open metadata.** `KeyValue` makes experimentation and forward extension
   easy but cannot carry semantics required for independent admission unless an
   exact profile separately defines the key and interpretation.
4. **R1CS closure.** Concatenation is a useful assembly rule for constraints
   in one field and namespace. It does not model transcript interleaving,
   shared verifier coins, committed-object authority, or recursive composition.

### 4.4 zkc transfer and analogy limit

**Design inference.** Relations should own a typed definition, field/regime,
instance/witness separation, and explicit interface ports. An ingress stream or
serialized artifact may carry such a subject, but the carrier is not the
subject and does not grant admission authority.

**Analogy limit.** A zkInterface message is tool communication, not a
prover/verifier event. Its concatenation law cannot determine Protocol
composition, and its proof-system exclusions mean it cannot identify a
Protocol even when a backend accepts the messages.

## 5. Noir ACIR/Brillig: useful separation with a deliberate mixed lane

### 5.1 Source model

**Source fact.** ACIR is a backend-facing constraint IR between a frontend and
a proving system. A current `Circuit` contains constraint opcodes, separate
private parameters, public parameters, public return values, and diagnostic
payloads. A `Program` contains ACIR circuits and separate Brillig bytecode
functions. See the current
[ACIR circuit source](https://github.com/noir-lang/noir/blob/master/acvm-repo/acir/src/circuit/mod.rs)
and the [ACIR reference](https://docs.rs/crate/acir/latest).

**Source fact.** ACIR opcodes constrain witness values, while Brillig executes
unconstrained witness computations and adds no constraint by itself. Noir
requires the programmer to constrain relevant results and performs coverage
checks for unconstrained calls. See the official
[unconstrained-functions guide](https://noir-lang.org/docs/language/unconstrained).

**Source fact.** ACIR contains black-box operations whose efficient or exact
backend realization depends on supported curves, hashes, lookups, and other
backend capabilities. The ACIR reference also notes that opcode order is
mathematically irrelevant to a system of equations but materially affects the
solver because witnesses must become available in execution order.

### 5.2 What it gets right

ACIR makes a practically important distinction:

```text
constraint opcodes       values that must satisfy the relation
Brillig / directives     one method of constructing required witness values
```

This is direct evidence that a prover-side computation can be useful and
portable without becoming part of the verifier-visible relation. It also shows
why `ProverPlan` cannot be inferred merely from a relation: a solver may need
ordering, bytecode, foreign calls, and backend-specific strategies that do not
change the accepted predicate.

The current tagged schema and separate public/private/return sets are stronger
evolution and interface mechanisms than an untyped opcode list alone.

### 5.3 Path-dependent constraints

1. **Constraint and plan coexist in one program container.** Brillig is clearly
   non-constraining, but it travels with the ACIR program and uses its witness
   identifiers. A consumer must know which lane is authoritative for acceptance.
2. **Backend-neutrality has a profile.** A black-box opcode name does not by
   itself close over field, curve, generator, hash, or exact backend semantics.
   “ACIR compatible” is therefore a capability and interpretation contract,
   not unconstrained semantic portability.
3. **Order has two meanings.** Constraint order can be relation trivia while
   solver order is plan-relevant. Hashing one physical list without a declared
   canonical equivalence would make plan trivia alter semantic identity.
4. **Protocol is downstream.** Proof messages, Fiat--Shamir absorption,
   commitment schemes, checks, and proof carriers remain backend-owned.

### 5.4 zkc transfer and analogy limit

**Design inference.** Stage 3 should require a typed bridge from relation ports
to Protocol obligations and a separate bridge from `ProverPlan` outputs to
those obligations. A plan may contain executable code or hints; neither should
change the Protocol or relation identity unless it changes a declared semantic
input.

**Analogy limit.** ACIR's public inputs are verifier-visible relation values,
not automatically a complete `ProtocolInterface`. ACIR also cannot determine
the identity or property claims of the backend protocol that consumes it.

## 6. Halo 2: transcript discipline inside a specialized system

### 6.1 Relation and construction model

**Source fact.** Halo 2's PLONKish circuit defines ordered fixed, advice, and
instance columns, polynomial constraints, lookups, equality constraints, and a
maximum degree. Fixed values are circuit-owned, advice values are normally
prover-provided, and instance values are shared with the verifier. The design
keeps ordering even where it does not affect mathematical circuit meaning so
that key generation is deterministic. See the
[PLONKish arithmetization](https://zcash.github.io/halo2/concepts/arithmetization.html).

**Source fact.** Chips provide reusable instructions over columns; a top-level
chip composes lower-level chips and may share columns. A layouter and floor
planner decide region placement. See the
[chip composition model](https://zcash.github.io/halo2/concepts/chips.html).

This separates three notions that a portable model should not conflate:

```text
gadget or instruction intent
PLONKish constraint-system meaning
physical layout and proving strategy
```

They are related, but a change in one need not have the same identity or
preservation consequence as a change in another.

### 6.2 Protocol and transcript model

**Source fact.** Halo 2 describes the proof protocol as an interactive argument
whose output transcript contains all prover/verifier messages and whose
verifier returns a decision. It explicitly distinguishes the public-coin
interactive protocol from its Fiat--Shamir realization. See the
[protocol description](https://zcash.github.io/halo2/design/protocol.html).

**Source fact.** The implementation does not expose a general `Proof` struct.
Proofs are opaque byte streams written and hashed through `TranscriptWrite`
and read and hashed through `TranscriptRead`. The encoding follows the protocol
sections, and vector lengths depend on circuit-specific constants. The stated
rationales include avoiding accidental proof fields that are not absorbed and
supporting several instances with shared protocol components. See
[Halo 2 proofs](https://zcash.github.io/halo2/design/implementation/proofs.html).

### 6.3 What it gets right

- Every serialized proof element passes through the same transcript boundary.
- The proof order is the protocol order rather than an after-the-fact object
  serialization.
- Circuit configuration and instance multiplicity explicitly determine the
  expected message shape.
- Multi-instance proving is a distinct construction with shared components,
  not accidental concatenation of independent proofs.

This is unusually strong evidence for treating transcript events, wire output,
and proof carrier as related but separately observable aspects.

### 6.4 Path-dependent constraints

The opaque stream is rational inside a verifier that already owns the exact
circuit, keys, curve, transcript implementation, and protocol version. It is a
poor self-describing interchange object:

- the byte stream does not independently state its circuit-dependent vector
  dimensions;
- the same structural proof slots have meaning only under matching keys and
  verifier code;
- changing transcript encoding can change challenge derivation and proof
  bytes even if a high-level circuit relation appears unchanged; and
- circuit composition, multi-instance proving, and recursive verification are
  distinct operations despite all producing “a Halo 2 proof.”

### 6.5 zkc transfer and analogy limit

**Design inference.** Canonical PIR should make the complete ordered protocol
schedule explicit enough that a clean-room implementation can construct the
same interactive trace and Fiat--Shamir observation schedule. A later wire
codec can follow that schedule, as Halo 2 does, without making raw byte identity
the definition of Protocol meaning.

Halo 2 also supports keeping layout/prover strategy in a `ProverPlan`, provided
the plan's outputs are checked against exact Protocol obligations and any
layout-dependent relation or key identity is surfaced rather than hidden.

**Analogy limit.** Halo 2's concrete protocol should not become the universal
PIR grammar. Its closed circuit-specific assumptions are precisely what make
the opaque-stream design safe and efficient locally.

## 7. Marlin: the clearest relation-to-protocol factorization

### 7.1 Source model

**Source fact.** Marlin defines an algebraic holographic proof for an indexed
R1CS relation and compiles it with a polynomial commitment scheme to obtain a
preprocessing zkSNARK with a universal, updatable SRS. The indexed relation
separates a reusable index from each public instance and private witness. See
the [Marlin paper](https://eprint.iacr.org/2019/1047.pdf) and the first-party
[implementation overview](https://github.com/arkworks-rs/marlin).

The architecture can be read as:

```text
indexed R1CS relation
  -> public-coin algebraic holographic proof
  -> oracle polynomials and verifier queries
  -> polynomial commitments and opening argument
  -> Fiat--Shamir non-interactive argument
```

Each arrow changes the represented subject and adds assumptions or concrete
mechanisms. This is much closer to the Stage 3 problem than treating a final
proof struct as the protocol.

### 7.2 Implementation closure

**Source fact.** The arkworks implementation parameterizes `Marlin` by field,
polynomial commitment scheme, and Fiat--Shamir RNG. It creates separate index
prover/verifier keys. Fiat--Shamir initialization absorbs a protocol name,
indexed verifier key, and padded public input; subsequent rounds absorb typed
commitment/message encodings, then evaluations before the PCS opening
challenge. See the
[Marlin implementation](https://github.com/arkworks-rs/marlin/blob/master/src/lib.rs).

**Source fact.** The resulting `Proof` groups round commitments, evaluations,
prover messages, and a PCS proof. Verification reconstructs the same ordered
round state and query set from the indexed verifier key and public input.

### 7.3 What it gets right

- The relation index is neither the universal SRS nor an instance.
- The AHP is a public-coin protocol before Fiat--Shamir.
- The PCS is a compilation mechanism for oracle access, not the R1CS relation.
- Indexed commitments and prover-round commitments have different provenance
  and lifetimes.
- Fiat--Shamir binds the verifier key and public instance before round
  challenges.

These are strong precedents for `InteractiveCore`, explicit committed-object
declarations, and a distinct `FiatShamir(TranscriptConstructionId)` subject.

### 7.4 Path-dependent constraints

The formal factorization is clearer than the portable representation. In the
library:

- Rust generic parameters select the field, PCS, and Fiat--Shamir engine;
- `to_bytes!` calls and vector positions participate in the concrete
  transcript grammar;
- a fixed three-round proof layout encodes one AHP family; and
- proof/key serialization is a library contract rather than a
  protocol-neutral schema with an independently admitted semantic identity.

This is not a defect in a specialized implementation. It illustrates the gap
between a modular proof construction and a portable Protocol subject.

### 7.5 zkc transfer and analogy limit

**Design inference.** Stage 3 candidates should be able to name all of the
following without hiding one in another:

```text
RelationDefinitionId
RelationInterfaceId
relation instance occurrence
committed object declaration and commitment occurrence
public-coin Protocol Core
PCS or subprotocol occurrence
Fiat--Shamir construction
ProtocolInterfaceId
ProverPlanId
```

The exact names remain candidate work. The important result is the separability
of their identity and correspondence judgments.

**Analogy limit.** Marlin's indexed R1CS and polynomial-oracle rounds do not
imply that every zkc Protocol must use preprocessing, a PCS, three rounds, or
algebraic messages.

## 8. STARK/AIR and Winterfell: a relation with protocol-shaped dependencies

### 8.1 AIR is a relation layer

**Source fact.** The STARK construction first arithmetizes computation into an
AIR and then applies an algebraic linking IOP and low-degree testing. See the
primary [STARK paper](https://eprint.iacr.org/2018/046.pdf). The AIR describes
valid traces; it is not by itself the full commitment, challenge, query, and
terminal-check protocol.

**Source fact.** Winterfell's `Air` contract fixes the base field, public input
type, transition constraints, boundary assertions, degrees, periodic values,
and trace context. The trace is the prover's execution witness. Public inputs
are tied to trace cells through assertions. See the official
[Winter AIR documentation](https://github.com/facebook/winterfell/blob/main/air/README.md).

### 8.2 Randomized AIR crosses the boundary intentionally

**Source fact.** Winterfell's randomized AIR splits trace construction into a
main segment and later auxiliary segments. The auxiliary segment consumes
verifier randomness that, in the non-interactive protocol, is derived after
commitment to the earlier segment.

This yields a precise seam:

```text
AIR requirement:       an auxiliary phase receives randomness with stated type
Protocol obligation:  commit to the earlier segment, then produce that randomness
Prover plan:           construct the auxiliary trace from prior values and randomness
```

An entirely “protocol-agnostic relation” would be unable to state this causal
requirement. Conversely, putting the challenge generator inside the AIR would
make the relation own transcript semantics that belong to the proof protocol.

### 8.3 Protocol configuration and reliance policy

**Source fact.** Winterfell's `ProofOptions` controls queries, blowup, grinding,
field extension, and FRI behavior, while associated prover types select the
hash and random coin. Verification receives the concrete AIR, proof, public
inputs, and acceptable-options policy. The proof carries some context and
options, but it does not make the external AIR implementation or relying
policy disappear. See the
[Winterfell repository guide](https://github.com/facebook/winterfell/blob/main/README.md).

### 8.4 Path-dependent constraints

- The AIR is a host-language trait implementation, so exact constraint meaning
  is ambient code rather than a portable canonical relation artifact.
- The proof and its embedded options identify protocol data, but the caller
  still selects which AIR and which minimum acceptable configuration to trust.
- Trace generation is a prover method and may have many implementations even
  for the same AIR.
- Constraint-degree declarations and trace layout are both mathematical inputs
  and performance commitments; treating them as unchecked hints makes the
  consumer boundary ambiguous.

### 8.5 zkc transfer and analogy limit

**Design inference.** A relation interface may declare typed phase inputs,
including challenges, without owning their source. PIR must satisfy those
requirements through explicit causal events. `ProverPlan` may own trace
construction. A verifier-facing interface must identify the exact Protocol and
relation binding, while policy about acceptable parameters remains a later
reliance decision rather than semantic admission.

**Analogy limit.** AIR's current/next-row model and boundary assertions are one
relation family. They cannot define general commitment schemes, arbitrary
interactive roles, or all non-AIR protocols.

## 9. Plonky3: component modularity exposes the closure problem

### 9.1 Source model

**Source fact.** Plonky3 is a toolkit of fields, hashes, challengers, matrix and
polynomial commitments, PCSs, FRI, AIRs, and PIOP implementations rather than a
single fixed proving system. See the
[Plonky3 repository](https://github.com/Plonky3/Plonky3).

**Source fact.** `BaseAir` states trace width, optional preprocessed trace,
periodic columns, expected public-value count, and row-access information;
`Air::eval` contributes constraints through an abstract builder. See the
[AIR traits](https://github.com/Plonky3/Plonky3/blob/main/air/src/air.rs).

**Source fact.** The uni-STARK prover takes a generic configuration, AIR,
trace, and public values. It commits to traces, observes instance dimensions,
commitments, and public values in a challenger, samples constraint-combination
and opening challenges, commits to quotient data, and invokes the configured
PCS opening protocol. See the
[uni-STARK prover](https://github.com/Plonky3/Plonky3/blob/main/uni-stark/src/prover.rs)
and matching
[verifier](https://github.com/Plonky3/Plonky3/blob/main/uni-stark/src/verifier.rs).

### 9.2 What it gets right

Plonky3 makes substitution boundaries concrete:

- AIR constraint evaluation is abstract over symbolic, scalar, packed, and
  verifier builders;
- challenger behavior is a distinct component;
- a PCS owns commitment domains, openings, and verification;
- fields, hashes, FRI, MMCS, and zero-knowledge choices can be varied; and
- preprocessed and witness-dependent traces are distinct inputs.

This is compelling evidence for typed component interfaces and for avoiding a
monolithic implementation that hard-codes every proof system.

### 9.3 The acknowledged closure and interoperability pressure

The same modularity leaves an exact verifier distributed across generic types,
runtime values, AIR code, and ordered calls. The source contains an explicit
comment that the constraint polynomials themselves are not directly observed
before a challenge and that the verifier must independently know which AIR it
is checking. Separately, the universal-verifier proposal says deployed
verifiers often hard-code AIR dimensions and constraints and proposes a
verification-key format that would represent them.

**Design inference.** This is a clean example of ambient semantic dependency:
the prover and verifier agree because they execute matching code, not because a
closed portable Protocol object independently names every observation and
predicate. Closing that dependency is exactly a semantic-IR problem; merely
serializing the Rust proof struct would not solve it.

### 9.4 Path-dependent constraints

1. **Combinatorial configuration.** Independent component types maximize
   experimentation, but a portable verifier cannot realistically accept every
   combination without profiles, resource bounds, and version policy.
2. **Generic types as identity.** Host-language type equality gives strong
   in-process compatibility while offering no language-independent Protocol
   identity.
3. **AIR code as verifier context.** A proof object is meaningful only with an
   exact AIR and configuration supplied out of band.
4. **Configuration granularity becomes wire policy.** Separating PCS
   commitments from opening protocols can enable upgrades, but only if their
   compatibility and transcript effects are specified rather than inferred.

### 9.5 zkc transfer and analogy limit

**Design inference.** Canonical PIR should be small and closed while its
implementation can still lower to modular components. A `ProtocolInterface`
can expose the immutable exact configuration required by a verifier, but it
must depend on the `ProtocolId`; it cannot retroactively fill semantic holes in
the Protocol. `ProverPlan` can choose optimized component implementations only
within the obligations fixed upstream.

**Analogy limit.** Plonky3's current traits are implementation interfaces, not
a proposed zkc schema. Reproducing their generic parameter graph in PIR would
encode Rust architecture rather than language-independent meaning.

## 10. Nova and HyperNova: composition creates new semantic subjects

### 10.1 Folding subject and protocol

**Source fact.** Nova introduces relaxed R1CS because ordinary R1CS does not
support the desired folding construction. A committed relaxed-R1CS instance
contains public input/output values, a relaxation scalar, and commitments to a
witness vector and error vector; the satisfying witness includes those vectors
and commitment openings. A public-coin folding protocol combines two instances
of the same structure into one, using a committed cross term and verifier
challenge. See the primary
[Nova paper](https://eprint.iacr.org/2021/370.pdf).

This is not proof aggregation in the generic sense:

```text
two committed relation instances + witnesses
  -> commitment to cross term
  -> fresh public challenge
  -> one new committed relaxed-relation instance + folded witness
```

The output is another relation instance that retains a precise satisfiability
connection to the inputs. A later SNARK can compress the accumulated result,
but folding itself is not a SNARK proof of both inputs.

### 10.2 IVC and occurrence structure

**Source fact.** Nova builds IVC by augmenting a step circuit so each recursive
step both executes the user transition and verifies/folds the running recursive
state. The public statement names an initial state, final state, and number of
steps. The first-party
[Nova repository](https://github.com/microsoft/Nova) exposes a step-circuit
interface, public parameters specialized to that circuit and curve cycle,
recursive proving, verification, and optional later compression.

A child step may occur many times with different state, witness, and position.
The semantic claim is about the ordered chain of occurrences, not merely the
presence of one child definition in a graph.

### 10.3 Path dependence and HyperNova

**Source fact.** Nova's folding requires compatible relaxed-R1CS structure.
Heterogeneous steps therefore require multiplexing into one structure or a
different construction. HyperNova introduces folding for customizable
constraint systems, supports folding multiple instances, and builds NIVC for
multiple step functions. See the primary
[HyperNova paper](https://eprint.iacr.org/2023/573.pdf).

This is a particularly useful path-dependent lesson: the same-structure
restriction made Nova simple and efficient, but it became a first-class design
constraint for heterogeneous composition. HyperNova does not “remove” the
constraint for free; it selects a richer relation family and a different
folding/IVC construction.

### 10.4 What it gets right

- relation structure, public instance, private witness, and commitments to
  witness-owned vectors are distinct;
- folding has its own interactive message and challenge schedule;
- the accumulator is a new identity-bearing occurrence, not a bag of inputs;
- recursive state interfaces are explicit and ordered;
- folding and final proof compression are separate mechanisms; and
- a change in supported heterogeneity changes the relation and protocol model,
  not only an implementation plan.

### 10.5 zkc transfer and analogy limit

**Design inference.** Stage 3 composition candidates need explicit child
occurrences, input/output port bindings, state flow, schedule or interleaving,
and construction-specific output identities. A folding construction should be
represented as a named relation or Protocol transformation with exact
assumptions, not as generic `compose(children)`.

Property transport must also be specific. “The folded instance is satisfied if
the inputs are” is not automatically zero knowledge, knowledge soundness,
succinctness, or validity of a later compressed proof. Those conclusions belong
to separate theorem/model-backed relations.

**Analogy limit.** Relaxed R1CS, CCS, curve cycles, and recursive step circuits
are not universal Protocol primitives. Nova demonstrates why composition and
occurrences must be explicit, not that PIR should adopt one folding algebra.

## 11. Cross-case pressure ledger

### 11.1 Relation ontology pressure

The cases support a candidate ontology with at least the following semantic
roles, without yet fixing Stage 3 names or fields:

| Role | Evidence | Required separation |
|---|---|---|
| Relation definition | R1CS matrices, ACIR constraints, PLONKish configuration, AIR | Predicate meaning versus its carrier or backend |
| Relation interface | zkInterface connections, ACIR public/private sets, AIR public values, IVC state | Named ports and visibility versus a concrete instance |
| Relation instance occurrence | Marlin public input, Halo 2 instance columns, STARK public values, Nova accumulator state | Values at one use site versus reusable definition |
| Witness occurrence | zkInterface assignments, ACIR witness map, advice/trace, Nova openings | Private satisfying data versus public instance |
| Committed-object declaration | Marlin oracle polynomial, trace column, Nova witness/error vector | What may be committed, under which relation role |
| Commitment occurrence | round commitment, trace root, accumulator commitment | One protocol event and provenance versus the declared object |
| Correspondence judgment | relation carrier to semantic definition; object to relation role | Checked agreement versus either subject's local validity |

The survey does **not** establish that each row should be one serialized top-level
object. It establishes that collapsing their identities or authorities loses
information used by real systems.

### 11.2 Protocol closure pressure

A clean-room Protocol description must close over every input that the cases
currently obtain from matching code, generic types, keys, or convention:

- role and event types;
- total observable schedule plus causal dependencies;
- public-coin challenge domains and sampling rules;
- committed-object type, commitment scheme, and opening/check relationship;
- relation definition and exact interface occurrence;
- verifier-visible public values and their encoding;
- field, group, extension, hash, PCS, FRI, and other semantic regimes when used;
- terminal checks and qualified outcomes;
- Fiat--Shamir domain separation, observation sequence, codecs, and challenge
  interpretation;
- subprotocol occurrence bindings and schedule composition; and
- rejection rules for malformed, unsupported, mismatched, or incomplete input.

This is closure of meaning, not a requirement that PIR implement every
primitive internally. A Protocol may depend on an exact separately identified
semantic object if the dependency and interpretation are closed and immutable.

### 11.3 Interface versus plan pressure

The survey gives concrete examples of both sides:

| Verifier-facing requirement | Prover-side construction choice |
|---|---|
| Public input shape and ordering | Witness solver and Brillig code |
| Exact circuit/AIR/relation identity | Trace generator or circuit synthesis |
| Verification/index key and public parameters | Proving key, caches, layout, FFT/PCS strategy |
| Proof event and codec contract | Memory layout, batching, parallelism, hardware |
| Accepted semantic regime | Concrete library implementation of each mechanism |

**Design inference.** `ProtocolInterface` should contain the immutable minimum
a consumer needs to bind values and execute verification for one exact
Protocol. `ProverPlan` should contain one admitted construction strategy and
must be related back through `PlanRealizes`. Neither should duplicate or amend
Protocol semantics.

### 11.4 Serialization and versioning pressure

The systems reveal three legitimate but distinct carrier strategies:

1. **Self-framed interchange messages:** zkInterface provides schema, message
   kinds, lengths, and magic, but intentionally omits the proof protocol.
2. **Versioned/tagged compiler artifact:** ACIR evolves a tagged opcode schema
   and program serialization, but backend capability meaning still needs a
   profile.
3. **Context-dependent proof stream or struct:** Halo 2, Marlin, Winterfell,
   Plonky3, and Nova rely on matching verifier context and specialized types.

No strategy establishes semantic identity merely by decoding bytes. A Stage 3
candidate must separately answer:

```text
What semantic subject do these bytes purport to carry?
Which schema and semantic regime interpret them?
Is the representation physically canonical?
Does it correspond to the claimed semantic subject?
Has that subject passed whole-Protocol or relation admission?
```

### 11.5 Qualified-outcome pressure

Several library verifier APIs eventually return a boolean or undifferentiated
error, which is appropriate for a narrow local caller but insufficient for the
Stage 3 model. External cases require distinct outcomes for at least:

- relation instance unsatisfied;
- malformed proof or carrier;
- incompatible relation, key, Protocol, or regime;
- unsupported component or version;
- challenge-domain or transcript-construction refusal;
- missing ambient definition or parameter;
- terminal verification rejection; and
- local verification success that does not establish a requested transported
  property.

The dossier does not choose exact enums. It records that one boolean cannot
support clean cross-domain authority or later reliance.

## 12. Composition taxonomy required of Stage 3 candidates

Every equal-resolution Stage 3 candidate should instantiate, reject, or defer
each row below rather than expose one unqualified composition operator.

| Kind | Input subjects | Output subject | Required occurrence data | Separate relation needed |
|---|---|---|---|---|
| Relation assembly | Relation fragments/interfaces | One relation definition | Port and variable binding, namespace, field/regime | Assembly preservation/correspondence |
| Protocol sequencing | Protocol occurrences | One composed Protocol | Total/partial order, shared state, role binding | Trace semantics and property composition |
| Protocol parallel/interleaved composition | Protocol occurrences | One composed Protocol | Interleaving and challenge independence/sharing | Observer-specific trace/distribution relation |
| Same-core multi-instance proving | One Protocol definition plus instances | Specialized batched Protocol occurrence | Instance order, shared commitments/challenges | Batch correctness and property transport |
| Oracle/commitment compilation | Open protocol plus commitment mechanism | New Protocol | Oracle-to-commitment and query/opening map | Compilation correctness and property transport |
| Fiat--Shamir compilation | Fresh-public-coin Protocol | Fiat--Shamir Protocol | Prefix/occurrence map and transcript construction | `FSCompile` plus property-specific transport |
| Recursive wrapping | Child verifier plus outer relation/Protocol | New outer Protocol | Child proof/interface occurrence in outer witness/instance | Verifier-circuit correspondence and transport |
| Folding/accumulation | Committed relation instances | Accumulator relation instance and Protocol | Ordered inputs, cross terms, challenge, accumulator state | Folding correctness and later property transport |
| IVC/NIVC | Step relation occurrences plus recursive state | Recursive Protocol | Initial/final state, step tags, occurrence order | Iteration invariant and compression relations |

This taxonomy is a design-space input, not a requirement that v0 support every
row. A v0 refusal can be correct if it is explicit and identity-preserving.

## 13. Candidate-opening opportunities

The sources suggest capabilities that a clean-sheet zkc model could provide
without copying any one library:

1. **Closed protocol manifests with modular implementations.** Preserve
   Plonky3-like component substitution in the workbench while admitting only a
   small canonical Protocol whose exact semantic dependencies are explicit.
2. **Typed transcript construction.** Preserve Halo 2's “written means
   absorbed” discipline while representing semantic observations separately
   from one byte codec and one hash implementation.
3. **Relation-phase requirements.** Allow AIR-like relation interfaces to ask
   for typed post-commitment challenges without letting the relation define
   their derivation or schedule.
4. **First-class committed-object grounding.** Represent the distinction seen
   in Marlin and Nova between a relation-owned value/object, its protocol
   commitment occurrence, and any later opening/check claim.
5. **Multiple plans per exact Protocol.** Admit ACIR/Brillig-like witness
   solvers, Halo 2 layouts, Winterfell trace builders, and alternate PCS
   implementations only through explicit coverage of the same obligations.
6. **Occurrence-native composition.** Make repeated child occurrences, state
   flow, shared challenges, and interleaving explicit so folding, batching,
   recursion, and sequencing cannot collapse into graph membership.
7. **Portable refusal.** A clean-room verifier should be able to say that a
   Protocol is well-formed but unsupported under its local realization
   profile, without changing Protocol identity or claiming semantic rejection.
8. **Independent interface identities.** One Protocol can expose several
   admitted verifier-facing interfaces or prover plans, while each remains
   dependent on the exact Protocol and unable to change its meaning.

These opportunities must later be compared against representation size,
admission decidability, MLIR carrier constraints, implementation feasibility,
and Stage 4 consumer needs.

## 14. Non-conclusions and reversal triggers

This dossier does not establish:

- that zkc should copy Halo 2, Marlin, AIR, Plonky3, Nova, ACIR, or
  zkInterface;
- that every proof system can be losslessly represented in v0;
- that a universal component algebra is possible or desirable;
- that every relation, commitment, key, interface, or plan must be a top-level
  serialized object;
- that an exact carrier schema, MLIR operation set, identity hash, or version
  policy has been selected;
- that a source paper's security result transfers to a zkc representation;
- that implementation code and prose specifications agree in every cited
  project; or
- that current zkc code implements any inferred requirement.

The main findings should be reopened if an equal-resolution candidate shows
that:

1. relation/protocol/plan separation cannot represent a required protocol
   without duplicated authority;
2. a semantic dependency can be safely left ambient while retaining
   language-independent clean-room interpretation;
3. occurrence-explicit composition prevents a required algebra from being
   stated or checked;
4. a smaller ontology preserves every identity, observer, outcome, and later
   consumer used by the required scenarios; or
5. a relevant mature system supplies a portable closed Protocol model that
   invalidates the observed gap.

## 15. Primary-source ledger

| Case | Primary sources used | What was extracted |
|---|---|---|
| zkInterface | [proposal](https://docs.zkproof.org/pages/standards/accepted-workshop3/proposal-zkinterface.pdf), [schema](https://github.com/QED-it/zkinterface/blob/master/zkinterface.fbs) | Relation/witness messages, gadget connections, allocation, framing, explicit exclusions |
| Noir ACIR/Brillig | [circuit source](https://github.com/noir-lang/noir/blob/master/acvm-repo/acir/src/circuit/mod.rs), [ACIR reference](https://docs.rs/crate/acir/latest), [unconstrained functions](https://noir-lang.org/docs/language/unconstrained), [profiler](https://noir-lang.org/docs/tooling/profiler) | Public/private roles, constraint/plan split, black-box profile, solver ordering, carrier evolution |
| Halo 2 | [arithmetization](https://zcash.github.io/halo2/concepts/arithmetization.html), [chips](https://zcash.github.io/halo2/concepts/chips.html), [protocol](https://zcash.github.io/halo2/design/protocol.html), [proof encoding](https://zcash.github.io/halo2/design/implementation/proofs.html), [prover](https://github.com/zcash/halo2/blob/main/halo2_proofs/src/plonk/prover.rs) | Circuit roles, layout/composition, interactive/FS distinction, transcript-coupled proof stream |
| Marlin | [paper](https://eprint.iacr.org/2019/1047.pdf), [repository](https://github.com/arkworks-rs/marlin), [implementation](https://github.com/arkworks-rs/marlin/blob/master/src/lib.rs) | Indexed relation, AHP/PCS compilation, keys, ordered FS binding, proof structure |
| STARK/AIR and Winterfell | [STARK paper](https://eprint.iacr.org/2018/046.pdf), [Winter AIR](https://github.com/facebook/winterfell/blob/main/air/README.md), [repository guide](https://github.com/facebook/winterfell/blob/main/README.md), [verifier](https://github.com/facebook/winterfell/blob/main/verifier/src/lib.rs) | AIR/protocol boundary, public inputs, randomized phases, options and verifier context |
| Plonky3 | [repository](https://github.com/Plonky3/Plonky3), [AIR traits](https://github.com/Plonky3/Plonky3/blob/main/air/src/air.rs), [prover](https://github.com/Plonky3/Plonky3/blob/main/uni-stark/src/prover.rs), [verifier](https://github.com/Plonky3/Plonky3/blob/main/uni-stark/src/verifier.rs), [universal-verifier proposal](https://github.com/Plonky3/Plonky3/issues/511) | Modular components, ambient closure, transcript order, interoperability dimensions |
| Nova/HyperNova | [Nova paper](https://eprint.iacr.org/2021/370.pdf), [Nova repository](https://github.com/microsoft/Nova), [HyperNova paper](https://eprint.iacr.org/2023/573.pdf) | Committed relaxed relation, folding schedule, IVC occurrences, same-structure pressure, heterogeneous extension |

## 16. Handoff to Stage 3 candidate work

The external cases do not select the zkc target. They establish the minimum
questions that every candidate must answer at equal resolution:

1. What exact subject owns relation meaning, its interfaces, instances,
   witnesses, and committed-object roles?
2. What exact subject owns the interactive schedule, challenges, checks,
   terminal outcomes, and prover obligations?
3. Which semantic dependencies are embedded, which are exact immutable
   references, and how is closure checked?
4. How does `ProtocolInterface` expose verifier-required values without
   duplicating Protocol semantics?
5. How can several `ProverPlan`s satisfy one Protocol while retaining distinct
   admission and `PlanRealizes` judgments?
6. How does Fiat--Shamir identify every absorbed observation, codec, prefix,
   challenge occurrence, and refusal rule?
7. Which composition families are supported, refused, or deferred, and what
   new subject and relation does each create?
8. Which carrier details are semantic, which are canonical trivia, and which
   are plan- or realization-local?
9. How do malformed, mismatched, unsupported, unsatisfied, rejected, and
   property-not-transported outcomes remain distinct?
10. Can a clean-room reader reconstruct all of the above without the original
    Rust/C++ types, ambient registry, or verifier source?

Only a candidate that answers those questions can legitimately claim to have
learned from the surveyed systems rather than merely borrowed their nouns.
