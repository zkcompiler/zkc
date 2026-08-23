# Protocol, Fiat--Shamir, relation, and composition theory

> **Document kind:** Temporary primary-source research dossier
> **Document state:** Stage 3.2 research complete
> **Authority:** None. Source results, design inferences, and zkc candidate
> constraints are labeled separately. This page proves no property of zkc.
> **Scope:** Interactive and oracle protocols, transcript constructions,
> relation/instance/witness boundaries, structural composition, and the
> separation between construction and property transport.
> **Disposition:** Absorb reviewed constraints and rationale into the selected
> PIR and Relations owners and the Stage 3 convergence record, then delete this
> page before documentation cutover.

## 1. Research question

What is the smallest semantic structure that lets zkc represent an
interactive proof protocol, construct a Fiat--Shamir Protocol, relate the
Protocol to a separately owned relation, and compose Protocols without
silently claiming a cryptographic theorem?

The question has four different levels:

```text
protocol subject construction
structural or observational correspondence
property-specific theorem transport
use-specific security or deployment conclusion
```

The literature strongly supports keeping these levels separate. A construction
can be well-defined when no theorem has been selected; a structural relation
can hold while a security property fails to transport; and a proved property
can remain unusable under a different deployment context.

## 2. Source discipline

This dossier uses papers, standards drafts, official protocol documentation,
and primary formalization repositories. Draft standards are treated as design
evidence, not settled standards. Library behavior is evidence about one
realization, not a universal protocol semantics.

| Source | Primary contribution used here | Limit |
|---|---|---|
| [Interactive Oracle Proofs](https://eprint.iacr.org/2016/116.pdf) | Explicit multi-round oracle interaction and a compiler whose security is characterized by a separate state-restoration property | Does not prescribe an IR or concrete transcript codec |
| [Fiat--Shamir Transformation of Multi-Round Interactive Proofs](https://eprint.iacr.org/2021/1377.pdf) | Round- and protocol-class-sensitive security loss and transcript-tree structure | Its theorems cannot be inherited by arbitrary zkc Protocols |
| [A Fiat--Shamir Transformation From Duplex Sponges](https://eprint.iacr.org/2025/536.pdf) | A concrete duplex-sponge transformation and a distinct security analysis | An idealized construction is not an implementation-conformance proof |
| [SAFE](https://eprint.iacr.org/2023/522.pdf) | Typed I/O patterns, domain separation, and stateful sponge framing | A sponge API alone does not define Protocol meaning |
| [CFRG Fiat--Shamir draft](https://datatracker.ietf.org/doc/draft-irtf-cfrg-fiat-shamir/) | Concrete separation of Sigma protocol, codec, duplex interface, transform, and proof serialization | Internet-Draft; narrow Sigma-protocol scope |
| [CFRG Sigma-protocol draft](https://datatracker.ietf.org/doc/draft-irtf-cfrg-sigma-protocols/) | Explicit instance, witness, commitment, challenge, response, verification, serialization, and AND/OR composition surfaces | Internet-Draft and not a general IOP language |
| [Merlin transcript protocol](https://merlin.cool/use/protocol.html) | Concrete responsibility split between mathematical values, codecs, labels, framing, and challenge sampling | Documentation for one transcript framework, not a security theorem |
| [zkInterface proposal](https://docs.zkproof.org/pages/standards/accepted-workshop3/proposal-zkinterface.pdf) | Separate circuit/instance/witness messages and distinct instance and witness reductions | Constraint interchange, not proof-protocol semantics |
| [Modular Design of Secure yet Practical Cryptographic Protocols](https://eprints.illc.uva.nl/id/eprint/1998/) | Typed modular Sigma-protocol construction and composition as a theorem-governed discipline | The construction family is narrower than zkc's intended Protocol space |
| [Universally Composable Security](https://eprint.iacr.org/2000/067.pdf) | Security preservation requires a semantic execution model and an explicit composition theorem | UC is a property framework, not zkc's structural composition definition |
| [VCVio](https://github.com/Verified-zkEVM/VCVio) | Typed oracle specifications, effectful computations, handlers, and simulation as separate formal objects | A formalization mechanism, not a ready-made PIR schema |
| [ArkLib](https://github.com/Verified-zkEVM/ArkLib) | Executable protocol specifications assembled through explicit composition and lifting interfaces | Ongoing library design; no automatic transfer to zkc |

## 3. Interactive Protocol is not relation satisfaction

### Source result

The IOP and multi-round Fiat--Shamir papers define a relation over public
instances and witnesses, then separately define interacting prover and verifier
machines, ordered messages, verifier challenges, and a final verdict. The
CFRG Sigma draft makes the same split operationally: the instance and witness
types are inputs to commitment, response, and verifier algorithms, not the
protocol transcript itself.

zkInterface independently separates constraint-system construction, public
instance material, and witness assignment. It explicitly does not standardize
backend proof algorithms or proof formats.

### Design inference

The following are different subjects:

```text
RelationDefinition
RelationInterface
RelationInstance = public statement under that interface
PrivateWitnessAssignment
InteractiveCore
Protocol
ProtocolInterface
```

`RelationSatisfies(instance, witness)` is a predicate about relation meaning.
`ProtocolAccepts(protocol, interface, proof, instance)` is an execution-level
predicate. `RelationCorrespondsAtInterface` is the independently checked bridge
between them. None of the three implies either other one without an additional
theorem or declared construction.

### Rejected shortcut

A relation digest stored in a Protocol claim does not establish relation
meaning, public-instance encoding, witness validity, or correspondence. It is
only an opaque reference until an admitted relation subject and exact mapping
are supplied.

## 4. Interaction shape is semantic

### Source result

IOPs make round count, oracle messages, verifier coins, query behavior, and
final verification explicit. Their Fiat--Shamir analysis depends on
state-restoration structure. Multi-round Fiat--Shamir results distinguish
protocol classes and transcript trees; general security loss and the loss for
special-sound classes are not interchangeable.

### Design inference

An ideal Core must retain:

- typed roles and semantic ports;
- every message, public binding, transcript absorption, fresh challenge,
  check, claim transition, and terminal occurrence;
- mandatory causal edges;
- one identity-bearing total observable schedule;
- exact challenge sample spaces and counts;
- abstract endpoint and prover obligations; and
- exact failure and terminal behavior.

Two Protocols may decide the same relation while differing in round structure,
message occurrences, challenge prefixes, accepted behavior, or security loss.
They are not `ProtocolEq` merely because their final verifier predicate is
extensionally similar.

## 5. Fiat--Shamir is a typed subject construction

### Source result

The current CFRG draft factors a Sigma protocol, codecs, a duplex-sponge
interface, initialization, transform, and proof serialization. The duplex
paper likewise defines a concrete transformation before proving properties of
that transformation. SAFE treats the sponge as a stateful typed I/O machine
rather than an unframed hash invocation.

Merlin places responsibility for mathematical-object encoding, fixed message
labels, domain separation, and challenge-to-scalar conversion in the proof's
transcript protocol even though the framework supplies the underlying framed
state machine.

### Selected constraint for candidate evaluation

A transcript construction must identify at least:

```text
initialization and domain input
state-machine or oracle profile
typed absorb and squeeze operations
injective framing
value codecs
challenge decoding and sampling
abort and rejection behavior
composition-context binding
construction semantic regime
```

The construction of a Fiat--Shamir Protocol is deterministic over an admitted
fresh-public-coin Protocol and one exact transcript construction. It produces:

- a new Protocol subject and identity;
- total source/target Core and Protocol maps;
- event- and challenge-occurrence maps; and
- an exact transcript-prefix map for every derived challenge.

Target admission checks that construction structurally. It does not require a
security theorem.

### Important non-implication

`ConstructFS(source, construction) = target` is not `FSCompile`. The latter is
a theorem- or model-basis-indexed relation. A property-specific transport from
source to target is a third judgment. Removing the theorem basis can make
`FSCompile` unavailable without making the target Protocol malformed.

## 6. Prefixes, occurrences, and framing cannot be inferred later

### Source result

Merlin and the CFRG draft make labels, lengths, mathematical codecs, and
challenge extraction part of transcript behavior. SAFE documents cross-
protocol collision and ambiguous I/O-pattern risks when domain and operation
shape are not bound. The multi-round literature reasons over trees of
transcripts sharing exact prefixes.

### Design inference

Every transcript action needs an occurrence identity independent of a display
name. Every challenge construction needs the exact ordered prefix of semantic
absorb occurrences that precedes it. The prefix cannot be reconstructed from
ordinary SSA reachability, a set of values, or a later printer traversal.

Framing and sampling belong to the transcript construction; the Core owns the
typed semantic items and order being framed. This split allows one Core to be
studied under several constructions without pretending the resulting
Protocols have one identity.

## 7. Three different meanings of composition

The sources expose three noncollapsible composition levels.

### 7.1 Structural Protocol construction

This is Stage 3's subject. It builds one new Core from tagged occurrences of
child Cores plus explicit face maps, causal seams, one total schedule,
challenge policy, dependency closure, obligation closure, and failure/terminal
propagation.

The IOP composition literature demonstrates that composition changes verifier
and proof structure. The Sigma literature demonstrates that AND, OR, and
threshold composition have different algorithms and proof obligations. Merlin
demonstrates one concrete sequential transcript composition technique.

None supports defining general composition as graph union or concatenation.

### 7.2 Structural relation between children and composite

A checked `CoreComposition` result retains tagged child-to-composite maps. It
can support later transport reasoning, but it establishes only the named
structural contract. If two construction histories yield the same intrinsic
Core semantics, their Core identity may coincide while their independently
identified composition results remain different.

This separates semantic identity from construction provenance.

### 7.3 Property composition

Cramer-style Sigma composition, IOP composition theorems, and UC each require
an exact property model and assumptions. The existence of structural
composition does not transport soundness, knowledge, completeness, zero
knowledge, non-malleability, or a quantitative bound.

Property composition therefore belongs to later Analysis. Stage 3 exports the
maps and assumptions that such a theorem would need.

## 8. Shared and repeated challenges

Repeated use of one child and shared challenge policies are not namespace
details.

A composition candidate must distinguish:

```text
IndependentChallenge(child_occurrence, child_challenge)
SharedChallenge(equivalence_class, exact consumers)
DerivedChallenge(source_occurrences, derivation)
ImportedChallenge(external_authority)
```

Shared or derived challenges change dependency, prefix, distribution, and
property assumptions. They require explicit target occurrences and cannot be
created by identifier aliasing. Repeated child occurrences receive distinct
tags even when they cite the same `CoreId`.

The current zkc composition-boundary research already identifies imported
challenges, joint transcript state, domain re-derivation, and connector
obligations as the important pressure points. The theory supports that focus
while rejecting any inference that closing those structural obligations alone
proves security of the composite.

## 9. Formalization lessons

VCVio represents oracle computations as typed syntax interpreted by handlers;
simulation is an explicit relation between a specification and an
implementation. ArkLib similarly separates executable protocol
specifications, composition/lifting interfaces, commitment compilation, and
Fiat--Shamir work.

The transferable lesson is not that zkc must adopt either library. It is that
these layers deserve separate identified inputs and judgments:

```text
Core syntax
challenge interpretation
handler or realization
structural construction map
simulation or correspondence
property theorem
```

A single generic `valid` result would erase exactly the hypotheses formal
reasoning needs.

## 10. Opportunity implications

The clean separation enables capabilities that are difficult under a sealed
carrier monolith:

1. compare several transcript constructions over one admitted Core without
   conflating Protocol identity;
2. admit an FS target before a theorem library supports it, while refusing all
   unsupported property transports;
3. retain source-to-target occurrence and prefix maps suitable for later
   machine-checked theorems;
4. compose repeated Cores with explicit independent, shared, or derived
   challenge policies;
5. give relation and endpoint consumers narrow views over the same exact
   Protocol Interface rather than duplicate label registries;
6. represent an external relation without requiring its artifact bytes, then
   interpret and compare bytes later; and
7. compare construction histories without making provenance part of intrinsic
   semantic identity unless it is genuinely observable.

## 11. Constraints exported to the candidate portfolio

Every serious Stage 3 candidate must answer all of these questions at equal
resolution:

- Is Protocol meaning independent of relation satisfaction and carrier bytes?
- Does Core contain one total observable schedule and occurrence namespace?
- Are semantic values separated from their transcript codecs?
- Is FS target construction available independently of `FSCompile` and later
  property transport?
- Are exact source/target occurrence and prefix maps retained?
- Does relation correspondence consume the exact admitted Protocol Interface?
- Does composition build and admit one new Core rather than join graphs?
- Are repeated children and shared challenges explicit?
- Is construction provenance separate from intrinsic identity unless observed?
- Can every negative, unsupported, cannot-answer, refusal, malformed, and
  checker-failure outcome remain distinct?

Any candidate that cannot answer one of these without ambient registry state,
generic metadata, or a universal proof object is incomplete.

## 12. Non-claims

This dossier does not establish that:

- any current or target zkc Protocol is sound, complete, zero knowledge, or a
  proof of knowledge;
- a cited theorem applies to zkc's current or target grammar;
- a duplex, Merlin, or CFRG-compatible transcript is correctly implemented;
- a structural composition preserves any cryptographic property;
- relation correspondence implies relation satisfaction; or
- any formalization library validates zkc.

