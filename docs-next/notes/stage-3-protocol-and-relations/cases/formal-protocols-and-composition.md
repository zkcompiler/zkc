# Formal Protocols and composition

> **Document kind:** Temporary primary-source comparative dossier
> **Document state:** Stage 3.2 research complete; convergence input
> **Authority:** None. Source facts, zkc design inferences, candidate
> implications, and falsifiers are labeled separately. This page neither
> defines Protocol semantics nor establishes a cryptographic property.
> **Scope:** Sigma-protocol and Fiat--Shamir interfaces, interactive oracle
> proofs, composition frameworks, modular proof formalisms, and machine-checked
> protocol descriptions.
> **Disposition:** Absorb reviewed constraints, non-transfers, and primary-source
> rationale into the selected PIR and Relations owners and the Stage 3
> convergence record, then delete this page before documentation cutover.

## 1. Research question

What architecture can represent an interactive proof Protocol, construct a
non-interactive Protocol, relate it to a separately owned relation, and compose
Protocols without treating structural well-formedness as a cryptographic
theorem?

The investigation distinguishes four layers:

```text
subject construction
structural correspondence
property-specific theorem transport
deployment-specific conclusion
```

The first three are relevant to the Stage 3 model. The fourth demonstrates why
even a proved property is not an unqualified conclusion about every use of a
Protocol.

This is architecture research, not cryptographic review. It studies what
semantic inputs, maps, interfaces, and assumptions a future checker or theorem
would need. It does not evaluate the security of any zkc implementation.

## 2. Evidence and inference discipline

Only primary papers, active standards drafts, official project documentation,
and source repositories are used.

| Primary source | Exact evidence used | Installed scope or limit |
|---|---|---|
| [CFRG Sigma Proofs for Linear Relations draft](https://datatracker.ietf.org/doc/draft-irtf-cfrg-sigma-protocols/) | Separate relation, instance, witness, prover state, commitment, challenge, response, verifier, simulator, validation, serialization, and non-interactive surfaces | Active Internet-Draft; three-message Sigma protocols for a particular family of linear relations |
| [CFRG Fiat--Shamir Transformation draft](https://datatracker.ietf.org/doc/draft-irtf-cfrg-fiat-shamir/) | Separate duplex interface, codecs, initialization, session context, per-round transformation, argument serialization, rejection behavior, and conditional security requirements | Active Internet-Draft; concrete duplex construction under random-oracle assumptions |
| [Interactive Oracle Proofs](https://eprint.iacr.org/2016/116.pdf) | Multi-round oracle interaction, non-interactive construction, transcript-state ordering, and state-restoration-dependent analysis | Public-coin IOP and random-oracle model; not an IR definition |
| [Fiat--Shamir Transformation of Multi-Round Interactive Proofs](https://eprint.iacr.org/2021/1377) | Round- and protocol-class-sensitive security loss for multi-round Fiat--Shamir | Property theorem for named protocol classes and assumptions, not a universal construction certificate |
| [Interactive Oracle Proofs with Constant Rate and Query Complexity](https://eprint.iacr.org/2016/324.pdf) | An explicit IOP composition theorem with outer/inner compatibility and derived parameter equations | One proof-composition construction; not general concurrent Protocol composition |
| [Universally Composable Security](https://eprint.iacr.org/2000/067) | Property preservation under a defined execution, environment, adversary, and ideal-functionality framework | A security framework, not a graph-composition or carrier law |
| [Modular Design of Secure yet Practical Cryptographic Protocols](https://eprints.illc.uva.nl/id/eprint/1998/) | Sigma protocols as typed building blocks whose compound protocols and properties require a construction theory | Specialized Sigma and monotone-composition setting |
| [SSProve paper](https://eprint.iacr.org/2021/397) and [formal repository](https://github.com/SSProve/ssprove) | Typed import/export packages, sequential and parallel composition, separation and compatibility premises, and relational program logic | A Rocq game-based proof framework, not a transcript-centric PIR |
| [VCVio repository](https://github.com/Verified-zkEVM/VCVio) | Typed oracle computation syntax, denotational probability semantics, handlers, simulations, and unary and relational proof modes | A Lean formalization framework; its internal syntax is not a neutral interchange standard |
| [ArkLib repository](https://github.com/Verified-zkEVM/ArkLib) and [OracleReduction sources](https://github.com/Verified-zkEVM/ArkLib/tree/main/ArkLib/OracleReduction) | Executable IOR specifications, relation reduction, composition, lifting, execution, BCS, Fiat--Shamir, and security as separate modules | An evolving Lean library centered on interactive oracle reductions |

An Internet-Draft is design evidence, not a settled standard. A formal
repository demonstrates one workable semantic factorization, not that its host
language, definitions, or theorem coverage should become zkc authority.

## 3. Sigma protocols: relation, interaction, and construction interfaces

### 3.1 Source facts

The CFRG Sigma draft defines the statement as a public instance and the
witness as a secret value satisfying a relation. It then specifies separate
interactive algorithms:

```text
ProverCommitment(instance, witness, randomness)
  -> commitment, private prover state

ProverResponse(private prover state, challenge)
  -> response

Verifier(instance, commitment, challenge, response)
  -> accept or reject
```

The private prover state is single-use. The optional simulator has a distinct
interface and is used by some composition and compact-serialization
constructions. Instance validation, transcript-shape validation, relation
serialization, and proof serialization are separately specified.

The draft also records a decisive limitation: structural instance validation
cannot know every semantic fact about how group elements were obtained, so a
structurally valid instance can still underlie an unsound argument.

AND composition is direct for the draft's linear-relation representation.
OR, threshold, and heterogeneous composition are different constructions and
carry separate soundness and zero-knowledge conditions.

### 3.2 Installed constraints that make the design rational

The draft targets one three-message public-coin protocol family over
prime-order groups. Fixed protocol shape and ciphersuites make concrete
interfaces, canonical encodings, instance validation, and interoperability
vectors practical. A simulator is meaningful because the selected Sigma
family has the required structure.

### 3.3 Strengths

- Relation inputs, private state, messages, verification, and serialization
  are reviewable as different surfaces.
- State lifetime and transcript shape are explicit.
- Structural validation can reject malformed instances without pretending to
  decide every security-relevant fact.
- Composition is exposed through a typed protocol interface rather than a
  generic byte concatenation convention.

### 3.4 Difficult-to-reverse choices

- The three-message shape is embedded throughout the interface.
- The relation representation and ciphersuite fix concrete algebraic domains.
- Simulator-dependent constructions cannot be generalized to Protocols with
  no corresponding simulator.
- Concrete serialization and batching choices serve interoperability, but
  they are not a universal semantic identity scheme.

### 3.5 Non-transfers to zkc

zkc must not assume that every Protocol:

- has exactly one commitment, one challenge, and one response;
- proves a linear preimage relation over a prime-order group;
- has a single-use state of the same form;
- provides a simulator;
- admits AND composition by concatenating relation declarations; or
- inherits Sigma soundness, knowledge, or zero-knowledge results.

### 3.6 zkc design inference

The following must be different subjects or judgments:

```text
RelationDefinition
RelationInterface
RelationInstance
PrivateWitnessAssignment

InteractiveCore
Protocol
ProtocolInterface

RelationSatisfies(instance, witness)
ProtocolAccepts(protocol, interface, inputs)
RelationCorrespondsAtInterface(protocol, protocol interface, relation interface)
```

Structural relation admission cannot establish satisfaction, Protocol
correspondence, or a cryptographic property. A relation digest embedded in a
Protocol is only a reference until the exact relation subject and binding are
supplied.

## 4. Fiat--Shamir: a construction before a theorem

### 4.1 Source facts

The CFRG Fiat--Shamir draft does not specify the transformation as a single
hash call. Its non-interactive prover and verifier jointly depend on:

- the source public-coin interactive argument;
- an initialization and application/session context;
- a stateful duplex interface;
- an ordered transcript of typed prover and verifier messages;
- an encoding for the instance and every prover message;
- a decoder and sample space for every verifier message;
- proof serialization and deserialization; and
- exact malformed-input and rejection behavior.

The session tag identifies the argument system, message types, codec order,
sampling behavior, suite, language, version, and application context. The
instance is absorbed before the first prover message. Each verifier message is
derived from the state after the exact preceding prefix.

The IOP compiler likewise evolves a transcript state across rounds so that
the generated verifier messages bind the public instance and prior prover
oracles in order. Its security analysis is characterized by state-restoration
properties of the source IOP.

The multi-round Fiat--Shamir paper shows that the general loss depends on the
number of rounds and oracle queries, while stronger special-sound structure
admits different bounds. The transformation's syntax therefore does not
determine one universal theorem.

### 4.2 Installed constraints that make the designs rational

The CFRG draft fixes a duplex family, byte- or field-level codecs, and a
random-oracle-oriented analysis to obtain reproducible interoperability. The
IOP results fix public-coin interaction, oracle messages, and particular
adversarial models so their reductions and quantitative bounds are
well-defined.

### 4.3 Strengths

- The mathematical Protocol and its transcript realization are separately
  visible.
- Message order, context binding, codecs, sampling, and rejection cannot be
  silently supplied by a backend.
- A verifier can reproduce challenge derivation from explicit inputs.
- Property theorems state additional source-protocol and oracle assumptions.

### 4.4 Difficult-to-reverse choices

- A fixed session-identifier width and concrete suite are interoperability
  choices, not universal semantics.
- The exact treatment of absorb and squeeze is construction-specific.
- A public-coin and random-oracle theorem family excludes other challenge
  interpretations.
- Message and instance codecs become property-relevant once they affect the
  transcript.

### 4.5 Non-transfers to zkc

zkc must not install as Core axioms:

- a 32-byte context identifier;
- a particular hash, duplex, rate, capacity, or byte order;
- random-oracle security;
- public-coin admissibility for every Protocol;
- the CFRG proof-string format; or
- a universal multi-round Fiat--Shamir security bound.

### 4.6 zkc design inference

`TranscriptConstruction` is an immutable identified subject containing at
least:

```text
construction semantic regime
initialization and exact context binding
state-machine or oracle profile
typed absorb and squeeze operations
injective framing and value codecs
challenge decoding and sample spaces
abort and rejection behavior
proof serialization policy, when selected
composition-context binding
```

Construction and theorem relations remain separate:

```text
ConstructFS(source Protocol, TranscriptConstruction)
  -> target Protocol
   + Core, Protocol, event, challenge, and transcript-prefix maps

FSCompile(source Protocol, target Protocol, theorem or model basis)
  -> affirmative | negative | unsupported | cannot-answer | refusal

PropertyTransport(property, source result, FS result)
  -> qualified target result
```

The target Protocol is authenticated and admitted independently. Removing or
changing a theorem basis can make `FSCompile` unavailable without making the
target malformed.

## 5. Interactive oracle proofs: round and oracle structure are semantic

### 5.1 Source facts

An IOP consists of multiple ordered rounds. The verifier sends randomness,
the prover returns an oracle message, and later verifier behavior may query
current and earlier oracle messages before the final decision. Round count,
alphabet, proof length, verifier randomness, query complexity, and soundness
are separate parameters.

The non-interactive IOP construction commits prover oracles and derives
round-specific verifier messages from evolving transcript state. Its theorem
requires a state-restoration property because a non-interactive adversary can
seek several oracle-derived continuations from a prior prefix.

The multi-round Fiat--Shamir results similarly distinguish general protocols,
special-sound classes, sequential repetition, and parallel repetition.

### 5.2 Installed constraints

The model is designed for probabilistically queried prover messages and
public verifier coins. Oracle availability across later rounds and the chosen
query model are essential to the stated efficiency and security results.

### 5.3 Strengths

- Interaction order and retained oracle access are first-class.
- Complexity and property parameters are explicit rather than hidden in one
  `secure` label.
- The compiler exposes why an exact prior prefix matters.
- The analysis demonstrates that two protocols for the same relation can have
  materially different transformation behavior.

### 5.4 Non-transfers to zkc

Not every Protocol message is an oracle, and not every verifier has deferred,
non-adaptive, or sublinear query access. IOP alphabets, query measures,
state-restoration definitions, and proof-length equations belong to named
profiles and Analysis results.

### 5.5 zkc design inference

Interactive Core needs enough structure to distinguish Protocols that decide
the same relation but differ in:

- role and port types;
- event occurrences and mandatory causal dependencies;
- one total observable schedule;
- message retention and later access;
- fresh challenge occurrences, sample spaces, and counts;
- checks, failures, and terminals; or
- abstract prover and endpoint obligations.

Every event and challenge needs an occurrence identity. A transcript prefix
cannot be reconstructed from SSA reachability, an unordered set of values, or
a later printer traversal.

## 6. Composition: structural construction and property preservation

### 6.1 IOP composition source facts

The IOP composition theorem combines an outer robust proof system with an
inner proof system for the outer verifier's relation. It requires a quantified
compatibility condition between the inner proximity parameter and outer
robustness. The resulting proof system has a new round structure and derived
proof-length, randomness, query, and error parameters.

This is not concatenation. The inner system proves a claim about what the
outer verifier would accept, and the theorem states exact assumptions and
parameter equations.

### 6.2 UC source facts

The UC framework gives protocols meaning within an execution model containing
parties, an adversary, an environment, and ideal functionalities. Universal
composition preserves a defined security relation within that framework,
including concurrent contexts.

The composition theorem is therefore a property result over a semantic model.
It is not a carrier-level rule saying that arbitrary Protocol graphs can be
joined without new obligations.

### 6.3 Modular Sigma source facts

Cramer's modular methodology develops compound protocols from Sigma building
blocks together with proofs that named properties survive under specified
constructions. Monotone AND/OR-style claims, secret sharing, simulator
structure, and the chosen Sigma family make those results possible.

### 6.4 SSProve source facts

SSProve represents packages with import and export interfaces and formalizes
sequential and parallel composition. Its laws expose their premises:

- sequential linking requires matching intermediate interfaces and compatible
  state locations;
- parallel validity requires interface compatibility and separation;
- parallel commutativity requires disjoint exports; and
- interchange requires several validity and separation conditions.

SSProve then uses a probabilistic relational program logic to prove
lower-level game relations. The algebraic construction layer and property
proof layer cooperate but remain distinguishable.

### 6.5 Installed constraints

Each framework selects a semantic universe that makes its theorem meaningful:

- IOP composition selects outer/inner verifier relations and quantitative
  robustness and proximity measures.
- UC selects an adversarial execution and ideal-world comparison.
- modular Sigma methods select a protocol family and simulator or extraction
  structure.
- SSProve selects stateful packages, typed imports and exports, locations, and
  a probabilistic semantics.

### 6.6 Strengths

- Composition premises are named rather than inferred from surface
  compatibility.
- Compound systems receive new semantic objects and derived parameters.
- Interface matching and state separation are explicit review surfaces.
- Property preservation is proved in the model that defines the property.

### 6.7 Difficult-to-reverse choices

- One framework's composition operator encodes its own notion of interaction,
  environment, state, or relation reduction.
- Algebraic laws that are unconditional for raw syntax may require validity
  premises before they mean anything about an admitted Protocol.
- A package interface alone does not capture transcript order, shared
  challenges, claim flow, or relation correspondence.
- Property models are not interchangeable merely because they all use the
  word composition.

### 6.8 Non-transfers to zkc

zkc must not equate:

```text
syntactic splice
semantic Core construction
child-to-target structural correspondence
security-property composition
deployment-level safety
```

It must not assume universal associativity, commutativity, identity, or
interchange for a generic Protocol-composition operator. Those laws must be
stated for a named constructor, observer, and set of premises.

### 6.9 zkc design inference

A structural composition specification consumes:

```text
tagged child Core occurrences
exact child faces and child-to-target maps
causal seams
one target observable schedule
dependency and obligation closure
failure and terminal propagation
challenge policy
```

The challenge policy distinguishes at least:

```text
IndependentChallenge(child occurrence, child challenge)
SharedChallenge(equivalence class, exact consumers)
DerivedChallenge(source occurrences, derivation)
ImportedChallenge(external authority)
```

The specification constructs one new Core candidate. The candidate undergoes
ordinary authentication and admission. A separate `CoreComposition` result
retains the construction inputs and child-to-target maps. Structural success
does not transport completeness, soundness, knowledge, zero knowledge,
distributional bounds, or cost claims.

Intrinsic Core identity should commit to normalized target semantics.
Construction provenance receives its own identity unless the history itself
is observable in the target semantics.

## 7. Machine-checked descriptions: syntax, semantics, handlers, and proofs

### 7.1 VCVio source facts

VCVio uses typed oracle-computation syntax. It gives that syntax denotational
probability semantics, interprets or replaces oracle behavior through
handlers, and provides separate unary and relational proof modes. Logging,
caching, simulation, and concrete execution are interpretations or
transformations of the computation rather than fields in one universal
protocol record.

### 7.2 ArkLib source facts

ArkLib describes an interactive oracle reduction from one relation to another.
Its public project structure separates protocol specifications, oracle
interfaces, execution, composition, context lifting, BCS, Fiat--Shamir, and
security. It aims to construct executable specifications through composition
and lifting, then prove completeness and round-by-round knowledge soundness
through corresponding generic theorems.

The project explicitly treats equivalence between executable specifications
and extracted implementation code as further work rather than an automatic
consequence of protocol formalization.

### 7.3 SSProve source facts

SSProve combines high-level package algebra with a lower-level probabilistic
relational program logic. Its repository maps paper claims to machine-checked
definitions and theorems and records the axioms on which the formalization
depends.

### 7.4 Installed constraints

These frameworks can exploit dependent types, monads, proof-assistant
elaboration, and their own probability libraries. Their internal syntax is
optimized for proof construction and mechanization, not cross-language
interchange, stable content identity, or MLIR tooling.

### 7.5 Strengths

- Protocol syntax and mathematical interpretation are explicit.
- Oracle or external behavior is supplied through typed interfaces.
- Simulation, equivalence, and security results are named relations.
- Proof dependencies and assumptions can be inspected.
- Executable specifications can coexist with later implementation-equivalence
  work.

### 7.6 Difficult-to-reverse choices

- A host proof assistant's term language, universe structure, and libraries
  permeate its definitions.
- Rich higher-order syntax may not have a small stable cross-language normal
  form.
- Formal projects evolve their abstractions as theorem coverage grows.
- Machine checking one denotation does not establish that a separate carrier
  or implementation denotes the same subject.

### 7.7 Non-transfers to zkc

zkc must not:

- make a Lean or Rocq AST the normative PIR carrier;
- treat successful elaboration as Protocol admission;
- infer implementation equivalence from an executable specification;
- infer theorem coverage from the existence of a formalization adapter; or
- serialize proof-assistant capabilities as semantic authority.

### 7.8 zkc design inference

The stable bridge is a checked, versioned denotation from admitted zkc
subjects into a formal system:

```text
denote[formal semantic regime](admitted Core view)
  -> formal protocol or effect object
   + total occurrence map
   + type and port map
   + challenge interpretation map
   + relation-interface map
```

The denotation result establishes only its named correspondence. Formal
theorems consume that result plus explicit assumptions. A proof assistant can
then own its theorem objects without becoming PIR authority.

### 7.9 Canonical finite guard decisions

Bryant's original reduced ordered decision-diagram work supplies a narrower
tool for Stage 3 admission than a general theorem prover: fixing variable
order and reduction rules gives a canonical graph representation of a Boolean
function and supports graph-based Boolean operations, while retaining a
worst-case exponential-size caveat. The primary source is [Randal E. Bryant,
“Graph-Based Algorithms for Boolean Function Manipulation”
(1986)](https://www.cs.cmu.edu/~bryant/pubs.html).

The zkc inference is deliberately conservative. Guard positions may use a
physically canonical reduced ordered decision diagram over a finite ordered
set of occurrence-exact atoms. Direct reduction then decides syntactic Boolean
equality, satisfiability, and implication without an ambient SMT solver.
Distinct opaque Boolean function results remain independent atoms, so the
checker may refuse an implication that needs function-specific mathematics;
it never upgrades that missing theory into an admission fact. This is a Core
admission subalgebra, not the representation of arbitrary protocol
computation, and size limits belong to a later implementation/profile policy.

## 8. Cross-case design forces

### 8.1 Required subject boundaries

The cases jointly pressure the following architecture:

```text
RelationDefinition
  -> RelationInterface
  -> RelationInstance(public assignment)
  +  PrivateWitnessAssignment

InteractiveCore
  + ChallengeInterpretation
  -> Protocol

Protocol
  -> ProtocolInterface
  -> ProverPlan

Fresh Protocol + TranscriptConstruction
  -> FS Protocol + FSConstruction result

child Cores + CoreCompositionSpec
  -> target Core + CoreComposition result

admitted subjects + semantic model + assumptions
  -> Analysis result
```

No arrow licenses an inference outside its named judgment.

### 8.2 Required Core information

Core must retain:

- semantic dependency references;
- roles and canonical semantic ports;
- pure values and protocol objects;
- typed effect occurrences;
- mandatory causal edges and one total observable schedule;
- fresh challenge occurrences and exact sample-space requirements;
- claim or reduction flow;
- checks, failures, and terminals; and
- abstract prover and endpoint obligations.

The total schedule is not redundant with the causal graph because transcript
prefixes and observable event order need one exact answer.

### 8.3 Required result separation

At minimum, the architecture needs distinct result families for:

```text
physical canonicality
semantic authentication
whole-subject admission
relation satisfaction
relation-to-Protocol correspondence
FS construction
FS theorem or model correspondence
Core composition
formal denotation
property transport
```

An affirmative result from one family must not be substitutable for another.

### 8.4 Required outcome separation

The sources require more than a boolean result:

```text
malformed input
structurally invalid subject
admitted subject
verifier rejection
negative relation result
unsupported semantic model or property
cannot answer from supplied inputs
policy or capability refusal
checker or theorem-engine failure
```

In particular, structurally admitted and cryptographically sound are not
synonyms.

### 8.5 Laws must be indexed

Every equivalence or composition law names:

- exact source and target subjects;
- direction;
- observer or semantic model;
- assumptions and quantitative parameters;
- checker or theorem basis;
- supported outcomes; and
- algebraic laws that hold under those premises.

There is no unindexed universal `Equivalent`, `Valid`, or `Composes` result.

## 9. Candidate implications

### Candidate A — semantic quotient over a rich representative

**Pressure:** Negative.

A rich sealed representative tends to place relation references, transcript
construction, interfaces, plan details, and theorem evidence in one identity
or admission boundary. The cases repeatedly separate those layers. Candidate
A remains viable only if its quotient and views make every distinction above
functional and independently authenticated; at that point it approaches the
satellite structure of Candidate C.

### Candidate B — physically canonical multi-subject bundle

**Pressure:** Mixed to negative.

A bundle can package the source, construction, interface, and checked results
conveniently. It must not make package membership semantic authority or force a
change in one subject to change the identities of unrelated subjects. The
formal cases support typed assembly, not one bundle-wide semantic identity.

### Candidate C — small semantic kernel with typed satellites

**Pressure:** Strongly positive.

This candidate best matches the recurring factorization:

- Core owns exact interaction and observable order.
- Transcript construction owns framing, codecs, context, and challenge
  derivation.
- Relations owns definition, public instance, private witness, and
  correspondence.
- Interface and Plan remain dependent subjects.
- Structural construction results retain exact maps.
- Analysis owns theorem bases, assumptions, and property transport.

It also permits several formal denotations over one stable admitted Core.

### Candidate D — typed event calculus as canonical subject

**Pressure:** Positive as a denotational model; conditional as the carrier.

VCVio and the formal frameworks show that typed effect syntax and handlers are
powerful for interaction and formal reasoning. Candidate D is attractive if
its closed normal form remains small, first-order, reviewable, and bijective
with canonical PIR. It fails as the semantic center if domain-owned claim,
relation, or correspondence meanings become generic effects whose adequacy
depends on ambient handlers.

### Candidate E — parameterized protocol modules

**Pressure:** Positive as an authoring layer over Candidate C.

Cramer, ArkLib, and SSProve demonstrate the value of reusable modules,
composition, lifting, and interface laws. Their results also show that
instantiation constraints are not themselves correspondence or property
proofs. Candidate E should elaborate a fully closed Core, preserve exact
construction maps, and leave the closed result independently admissible.

## 10. Candidate falsifiers exported by this dossier

| Falsifier | Candidate failure exposed |
|---|---|
| A structurally admitted relation instance is automatically treated as a sound statement | Relation admission has absorbed a property claim |
| Protocol identity is unchanged when transcript order, message codec, challenge sampling, or application binding changes | Identity omits observable construction semantics |
| An FS target cannot exist until a security theorem is installed | Subject construction and property transport are collapsed |
| Removing a theorem basis invalidates an otherwise unchanged target Protocol | Theorem authority has contaminated Protocol identity or admission |
| A composition operation merely unions graphs or namespaces | Target schedule, seams, challenge policy, or closure is missing |
| Repeated child use cannot distinguish child occurrences | Composition loses occurrence-sensitive meaning |
| Shared challenges are represented by identifier aliasing alone | Distribution, prefix, and dependency obligations are unrepresented |
| Structural composition automatically transports soundness or zero knowledge | Property composition has no explicit model and assumptions |
| Associativity or commutativity is asserted without constructor-specific premises | An algebraic law has been generalized beyond its interface conditions |
| One generic equivalence result substitutes for trace, distribution, relation, construction, and property relations | Observer and theorem boundaries are erased |
| A formal adapter can omit an occurrence or challenge-prefix map | Formal theorems cannot be tied back to the exact admitted subject |
| Proof-assistant elaboration is accepted as PIR admission | Formal host authority has replaced zkc semantic authority |
| An executable formal specification is presumed equivalent to backend code | Implementation correspondence is unproved |
| Malformed, rejected, unsupported, cannot-answer, refusal, and checker failure collapse into one result | Consumers cannot preserve epistemic boundaries |

Any equal-resolution candidate that triggers one of these falsifiers needs a
redesign, not merely a diagnostic improvement.

## 11. Questions retained for convergence

The sources constrain but do not decide these Stage 3 choices:

1. Which part of application-context binding belongs to reusable
   `TranscriptConstruction`, and which part is supplied as an exact
   construction input?
2. Which closed first-order event algebra is sufficient for current and
   credible future Protocols without importing a universal effect runtime?
3. Which composition constructors deserve v0 names beyond the general
   `CoreCompositionSpec` contract?
4. Which formal semantic regimes should receive first-class denotation
   profiles, and which remain external adapters?
5. Which relation and Protocol views are the smallest total inputs for a
   correspondence checker?

Convergence must answer only those needed to close the v0 semantic model. It
must not standardize a theorem library or authoring module language
prematurely.

## 12. Non-claims

This dossier does not establish that:

- any current or proposed zkc Protocol is complete, sound, zero knowledge, or
  a proof of knowledge;
- a cited Sigma, IOP, Fiat--Shamir, UC, or composition theorem applies to zkc;
- the CFRG drafts are final standards;
- a particular transcript construction is correctly implemented;
- structural Core composition preserves a cryptographic property;
- VCVio, ArkLib, or SSProve currently formalizes the selected zkc model;
- an eventual formal denotation is adequate or implementation-preserving; or
- Candidate C has been selected by this dossier.
