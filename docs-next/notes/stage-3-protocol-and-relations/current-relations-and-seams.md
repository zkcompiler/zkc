# Current Relations model and Protocol seams

> **Document kind:** Temporary Stage 3.1 reconstruction
> **Document state:** Reconstruction evidence; no target architecture selected
> **Authority:** None. Current normative meaning remains under `docs/spec/`;
> implementation support is determined by the current checkout and its tests.
> This page does not ratify a relation ontology, canonical PIR change,
> migration, or Stage 3 candidate.
> **Research date:** 2026-08-22
> **Scope:** The current relation domain, its Protocol/PIR seams, current
> correspondence tooling, and the relation-facing parts of Soundness,
> Compiler, OIR, linking, and verifier descent.
> **Disposition:** Preserve conflicts and unknowns through Stage 3 comparison;
> absorb reviewed conclusions into durable owners, then delete this temporary
> page before `docs-next/` authority cutover.

## 1. Question and method

This reconstruction asks one deliberately pre-design question:

> What relation model does the current repository actually define, implement,
> and exercise, and exactly where does it meet Protocol meaning?

The answer is assembled from four evidence planes that are not interchangeable:

1. **Normative intent** -- principally `docs/spec/relations.md`, then the
   owning parts of `kernel.md`, `vocabularies.md`, `carrier.md`,
   `boundaries.md`, `endpoints.md`, `soundness.md`, and `compiler.md`.
2. **Live semantic inputs** -- the checked-in ProtocolVocabulary,
   RelationContract registry, construction profiles, and soundness signature.
3. **Implementation correspondence** -- registry loaders, the relation CLI,
   sealed-artifact views, R1CS reader, anchor projection, construction routes,
   endpoint projection, soundness projection, and compiler records.
4. **Evidence** -- unit tests, lit tests, examples, and current status claims.

The sections below label direct correspondence, partial correspondence,
conflict, gap, and unknown separately. Target-architecture documents are used
only to identify vocabulary already in circulation; they are not treated as a
description of the current model.

## 2. Executive reconstruction

The current system does **not** contain one integrated semantic object called a
relation. It contains three useful but incompletely connected layers:

```text
outside zkc
  mathematical predicate / source relation / witness generator
                 |
                 | opaque identity or author assertion
                 v
current Protocol/PIR core
  ClaimDescriptor(profile, anchors)
  + exact claim occurrence and claim-flow edges
  + optional MaterialBinding(ValueRef, MaterialRef)
                 |
                 | post-seal comparison only
                 v
current relation domain
  RelationContract + optional relation bytes
  + statement-label correspondence
  + computed / cross-checked / asserted report

independent current prover path
  PIR construction routes -> prover-skeleton OIR -> suppliers/run record
```

The Protocol core represents **a claim about opaque references**, not a
mathematical predicate `R(instance, witness)`. `RelationContract` is a
post-seal, content-addressed description of how an external relation interface
is to be read and compared with a sealed artifact. It is not protocol content,
not the denotation of the relation, not a witness capability, and not a
satisfaction judgment (`docs/spec/relations.md:20-46`;
`docs/spec/kernel.md:319-330`).

The strongest faithful summary of the present model is therefore:

```text
Protocol relation claim
  = exact claim occurrence carrying a closed profile and opaque anchor tuple

RelationContract
  = separately identified, post-seal interface declaration and evidence input

Relation correspondence
  = consistency ledger over one loaded artifact presentation, one contract,
    optional bytes, and currently one caller-supplied field expectation

Relation satisfaction
  = not represented or decided
```

This separation is intentional in several places and accidental in others.
Opacity at the kernel boundary is explicit and well defended. The missing
identity and correspondence links between relation, instance, witness,
interface, endpoint, and invocation are acknowledged by the roadmap and status
matrix as partial work (`docs/status.md:99-120`; `docs/roadmap.md:14-30`).

## 3. Authority and evidence map

| Surface | Current role | What it may establish | What it does not establish |
|---|---|---|---|
| `docs/spec/kernel.md` | Canonical Protocol semantics | Protocol structure, claims, anchors, claim flow, material-reference equality, seal boundary | Relation denotation, payload meaning, satisfaction, witness correctness |
| `docs/spec/vocabularies.md` | Canonical ProtocolVocabulary semantics | Closed claim-profile anchor shape and cited local reduction/check semantics | Resolution of an anchor into a RelationContract or application relation |
| `docs/spec/relations.md` | Canonical relation-domain document | RelationContract schema, evidence tiers, correspondence judgment, R1CS header reading, permanent nonclaims | Predicate truth, underconstraint freedom, witness correctness, bytes-to-anchor truth |
| `docs/spec/endpoints.md` | Canonical OIR endpoint semantics | Endpoint ABI, linear handles, construction-route projection, run/conformance boundaries | Relation satisfaction, witness semantics, algebraic correctness of fills |
| `docs/spec/soundness.md` | Canonical conditional analysis semantics | Exact Protocol-claim subjects and selected security/completeness derivations | A first-class relation subject or executable satisfaction predicate |
| `docs/spec/compiler.md` | Canonical checked-transform semantics | Structural transform legality, claim lineage, conditional loss, attributed preservation claims | General relation compilation or established property transport |
| JSON registries | Live admitted content | Exact profile/check/reduction/hole/value declarations used by current tools | Truth of external prose, adapter execution, external relation facts |
| C++ implementation | Current correspondence evidence | What current loaders, projections, and tools compute | Normative authority where it differs from the specifications |
| Tests/examples | Bounded evidence | Behavior on the exact exercised cases | Exhaustive semantics, proof, or untested cross-domain correspondence |

There is a documentation-routing defect: `relations.md` declares itself
canonical for the relation domain (`docs/spec/relations.md:1-9`), but the
normative-document table in `docs/spec/overview.md` does not list it. This does
not remove the document's self-declared authority, but it makes discovery and
conflict resolution less reliable.

## 4. Exact current object inventory

The table below separates objects the repository actually identifies from
concepts that currently exist only as prose, declarations, or external facts.

| Concept | Current representation | Identity-bearing now? | Current semantic status |
|---|---|---:|---|
| Mathematical relation definition | No kernel or relation-domain object | No | External and opaque |
| Relation source | No admitted input language | No | Explicitly outside zkc scope |
| Relation artifact bytes | Optional bytes passed to `zkc-relation` | Only a computed `content_digest` when present | Read only through a bounded format reader; not admitted as the relation named by anchors |
| Claim profile | ProtocolVocabulary entry `{kind, ordered anchor names}` | Yes, by tagged entry digest when cited | Shape and coarse role only |
| Claim descriptor | `(profile id, exact anchor dictionary)` | Yes, inside Protocol identity and by a position-free descriptor digest | Protocol-local claim identity; anchors remain opaque |
| Claim occurrence | Canonical claim position within an artifact | Yes, as `{artifact_id, claim_ref}` in analysis | Exact Protocol subject, but not a relation instance |
| RelationContract | Closed registry entry | Yes, by `SHA256("zkc/relation-contract\n" \|\| canonical JSON)` | Post-seal evidence-only interface declaration |
| Relation interface | Fields dispersed inside RelationContract | Only indirectly through the contract digest | No separate admitted subject or capability |
| Relation instance | Anchor names plus encoding declaration and statement-label map | No first-class value | Instance shape is declared; an actual typed instance is not constructed |
| Statement instance | Instance-stage PIR binds / OIR public arguments | OIR labels and order enter OIR identity; PIR labels do not enter PIR identity | Runtime values are not connected to a typed RelationInstance by an admitted judgment |
| Witness interface | RelationContract `witness_ports`; separately, route witness labels and handle classes | Contract declaration and Protocol routes enter different identities | No judgment equates these two interfaces |
| Witness assignment | Opaque OIR handles and supplier inputs | Exact run records bind consumed input digests | No relation-local satisfaction or ownership semantics |
| Committed object | Profiled PIR value plus a ValueProfile | Profile content is cited through ProtocolVocabulary | Size/content class/origin declaration; committed contents remain opaque |
| ProtocolInterface | No current semantic object | No | Interface-like facts are dispersed across PIR, RelationContract, and OIR |
| ProverPlan | No current semantic object | No | Construction routes are the closest orchestration carrier; CompilerPlan is a different object |
| Relation correspondence result | Specified canonical report; emitted JSON in the CLI | Spec says yes; implementation does not compute/store its digest | Partial implementation |
| `RelationSatisfies(instance,witness)` | No object or judgment | No | Explicit nonclaim |

### 4.1 Relation definition

The kernel Protocol is

```text
P = (E, <=, A, C, R, chi, K, anchors, B_M)
```

with an ordered event/transcript spine and a linear claim-flow graph
(`docs/spec/kernel.md:59-97`). Its claims are proof obligations carrying a
stable occurrence and a `ClaimDescriptor(profile, anchors)`
(`docs/spec/kernel.md:180-207`). There is no field containing a predicate,
relation program, evaluator, or typed `R(x,w)`.

The neutral `pir.instantiate` source carries an admitted profile and exact
anchors. The specification explicitly prohibits inferring relation meaning
from its authoring label or source spelling (`docs/spec/vocabularies.md:198-202`;
`docs/spec/kernel.md:223-227`). Therefore the current relation definition is an
external semantic premise, not a latent field recoverable from PIR.

### 4.2 Claim profiles and claim descriptors

A `ClaimDescriptorProfile` supplies exactly a coarse kind and an ordered,
unique anchor schema. The admitted relation-flavored profiles are:

| Profile | Kind | Exact anchors | Current reading |
|---|---|---|---|
| `opaque_relation` | `relation` | `contract`, `statement` | Both values are explicitly uninterpreted compatibility anchors |
| `r1cs` | `relation` | `a`, `b`, `c`, `public` | Matrix and public-input anchors are opaque |

The profile entry and every cited vocabulary dependency are content-pinned in
the sealed artifact. The descriptor's exact tuple is a claim-graph object;
descriptor equality is load-bearing for reduction and link composition
(`docs/spec/vocabularies.md:97-148`; `docs/spec/kernel.md:845-870`).

This gives the current core a strong answer to **which opaque claim occurrence
is flowing where**. It gives no answer to **which mathematical relation the
anchors denote** or **whether a runtime instance and witness satisfy it**.

### 4.3 RelationContract

`RelationContract` is the current relation-domain center. Its closed fields are:

```text
claim_profile              {name, digest}
relation_anchors           map<anchor_name, sha256-ref>
instance_anchors           ordered distinct anchor names
format                     r1cs-bin-v1 | opaque
identity                   content_digest and/or {attested_id, attestor}
instance_encoding          field_vector | opaque_bytes | commitment
witness_ports              enumerated | opaque
statement_correspondence   ordered [{slot, statement_label}]
declared_shape             optional {constraint_count}
```

The C++ representation corresponds directly to this schema
(`include/zkc/Registry/RelationContractRegistry.h:17-105`). The loader:

- rejects unknown fields and malformed shapes;
- pins the named claim profile by digest;
- enforces the normative profile-specific anchor partition;
- admits only `r1cs-bin-v1` and `opaque`;
- keeps content-derived and attested identity evidence separate;
- admits three instance-encoding variants with no default;
- enforces unique witness port names;
- enforces contiguous correspondence slots and unique labels; and
- computes the tagged contract digest
  (`lib/Registry/RelationContractRegistry.cpp:125-220`, `222-316`,
  `318-455`).

The contract is deliberately post-seal. It is not loaded by `seal`, does not
move Protocol identity, and may be attached to an older sealed artifact
(`docs/spec/relations.md:25-53`; `docs/spec/boundaries.md:72-79`). The current
`ProtocolEnvironment` contains ProtocolVocabulary and optional construction
profiles, but no RelationContract registry
(`include/zkc/Registry/ProtocolEnvironment.h:16-47`).
The separation is also fail-closed at the vocabulary boundary: a
`relation_contracts` section is not part of ProtocolVocabulary's admitted
closed schema, and `test/Registry/protocol-vocabulary.test:36-42` preserves its
rejection as a future seam rather than an ambient extension.

### 4.4 Relation identity and relation artifacts

The current contract keeps two evidence forms distinct:

- `content_digest` says only that the supplied bytes hash to this value;
- `attested_id` plus `attestor` says that the named party asserts an external
  identifier denotes the relation.

Neither form proves that the bytes or external identifier denote the relation
named by the sealed claim anchors (`docs/spec/relations.md:70-87`). All three
checked-in example contracts are attested-only; none pins relation bytes by
`content_digest` (`registry/relation-contracts.json:1-116`). One FRI fixture
even uses the digest of empty input as its `contract` relation anchor, which
the relation judgment correctly surfaces as a vacuous scope gate rather than
treating as meaningful identity (`registry/relation-contracts.json:3-35`).

There is no admitted relation-artifact capability, artifact schema id,
process-local authority, or adapter-result object. Bytes remain an optional CLI
argument. The R1CS reader derives bounded header facts from those bytes, but
the permanent bytes-to-anchor gap remains asserted.

The two checked-in FRI contracts exercise the other declared family shape:
`instance_encoding = commitment(payload_class = rs)` with one opaque
`codeword` witness port (`registry/relation-contracts.json:3-67`). With
`format = opaque`, the current relation tool can check only artifact-side
anchor/label structure and report declarations and assumptions. It does not
bind an actual root commitment or codeword witness to either contract.

### 4.5 Instance interface versus instance value

The contract can describe one of three public-instance interfaces:

- `field_vector(field_order, arity)`;
- `opaque_bytes(digest_function = sha256)`; or
- `commitment(payload_class)`.

`statement_correspondence` maps relation instance positions to the sealed
artifact's instance-stage statement labels. It permits a permutation because
relation instance order and Protocol absorption order can differ. Protocol-only
public labels may remain outside the map. Label presence is computed, arity
agreement is cross-checked, and the meaning of a slot-to-label association is
always the named assumption
`zkc.assume.statement_correspondence_wiring`
(`docs/spec/relations.md:138-157`, `179-221`).

This is an **interface correspondence declaration**, not an instance object.
No current judgment constructs a typed ordered value from invocation inputs,
hashes or decodes it according to `instance_encoding`, and proves that value is
the instance named by the claim's instance anchor. In particular:

- `opaque_bytes` declares a digest function but no current flow admits or binds
  an actual byte stream;
- `commitment` declares a payload class but no current flow equates a concrete
  commitment occurrence with the instance anchor; and
- `field_vector` checks declared/header arity and label presence, not runtime
  field elements or an instance-anchor preimage.

### 4.6 Witness interface versus witness assignment

RelationContract has two witness-interface shapes:

- an ordered enumerated list of `{name, count}` ports; or
- one opaque whole-witness port `{name}`.

The document explicitly says a declaration does not oblige an endpoint to
consume those ports (`docs/spec/relations.md:159-177`). This limitation is
real in the implementation. The relation CLI cross-checks the total enumerated
private-input count against an R1CS header, but it never compares port names or
port structure with construction routes, OIR `witness_labels`, handle classes,
hole operands, or a concrete invocation.

The prover path independently defines:

```text
PIR route witnesses     ordered [label, handle_class]
route instances         HoleContract + parameters + ordered references
prover OIR ABI           statement values + opaque linear witness handles
execution               supplier-selected hole calls
run record               exact artifact/profile/supplier/input digests
```

Construction route validation is substantial: the builder admits a closed
dictionary, resolves exact HoleContracts, checks typed inputs, dependencies,
acyclicity, temporal availability, slot binding, and handle linearity
(`lib/Semantics/ConstructionGraph.h:21-95`;
`lib/Semantics/ConstructionGraph.cpp:167-235`, `540-604`). Prover projection
requires route totality and projects the route witness pairs into OIR ABI
(`lib/Dialect/Pir/Transforms/PirProject.cpp:218-256`, `287-355`). But this is a
Protocol construction interface, not a checked realization of RelationContract
witness ports.

Successful prover execution says that a supplier emitted boundary-conformant
values and bytes. The run record binds the inputs it used; neither route
validation nor run conformance establishes relation satisfaction
(`docs/spec/endpoints.md:319-370`).

### 4.7 Committed objects

Committed objects have a separate current model in ProtocolVocabulary.
`ValueProfile` states:

```text
element_class
arity_log2
origin = prover_message | preprocessed | relation_derived
binding_route
```

The kernel never reads committed contents. The profile gives soundness rules a
declared content arity and provenance class
(`docs/spec/vocabularies.md:174-194`;
`include/zkc/Registry/ProtocolVocabulary.h:28-68`). The loader closes the
schema, bounds `arity_log2` to `0..64`, and computes a tagged profile digest
(`lib/Registry/ProtocolVocabulary.cpp:115-171`). The sealed soundness view then
collects role-indexed committed arities for rules that price them
(`lib/Soundness/PirSoundnessAdapter.cpp:858-935`).

This machinery is independent of RelationContract's
`instance_encoding.kind = commitment`:

- no object identity ties a profiled commitment occurrence to a
  RelationContract instance;
- no relation binds the committed content to a relation instance or witness;
- `binding_route` is currently an unresolved declaration; and
- although `preprocessed` and `relation_derived` origins are admitted, the C++
  model states that only `prover_message` currently has an expressible carrier
  (`include/zkc/Registry/ProtocolVocabulary.h:50-67`).

The present committed-object model is therefore useful size/provenance metadata
for Protocol analysis, not yet a relation-local committed-value semantics.

## 5. Current ingress and lifecycle

The two current ingress paths remain separate until a post-seal report:

```text
ProtocolVocabulary + ConstructionProfiles
                 |
                 v
Open PIR --seal--> persisted sealed artifact --admit--> immutable capability
   ^                         |                         |
   |                         |                         +--> Soundness / project
pir.instantiate              |
(profile + anchors)          +------------------------------+
                                                             |
RelationContract registry --load by CLI name--> contract ----+--> report
optional relation bytes ----------hash/header reader---------+
optional caller field expectation ---------------------------+
```

### 5.1 Protocol ingress

`pir.instantiate` is the only admitted relation-flavored source. Seal checks
profile resolution, anchor shape, claim linearity, transcript binding,
coverage, reduction closure, terminal closure, and the cited vocabulary
closure. It explicitly does not load relation payloads, run predicates, or
check witness satisfaction (`docs/spec/kernel.md:790-821`).

RelationContract content is not among the authorities stamped into a sealed
Protocol artifact. A later contract can describe a fixed artifact without
changing it. This preserves the kernel's opacity boundary, but it also means
there is no seal-time or admission-time relation interface capability.

### 5.2 Relation-domain ingress

The current `zkc-relation` invocation takes:

```text
sealed artifact
RelationContract registry path
contract registry key
ProtocolVocabulary path
ConstructionProfile registry path
optional relation bytes
optional caller-supplied expected field order
```

(`tools/zkc-relation/zkc-relation.cpp:29-50`). The loader structurally admits
the registry entry, the Protocol artifact is decoded and admitted, and a
`SealedSoundnessView` is reconstructed. The relation report itself is not
loaded into either environment and does not mint a reusable admitted
capability.

### 5.3 Current join point

The only implemented join between relation-domain data and a sealed Protocol
is the `zkc-relation` correspondence computation. It does not modify the
artifact, participate in seal, constrain endpoint projection, bind an
invocation, or become a premise consumed by the soundness evaluator.

The specification anticipates later consumption by digest and names anchored
material, preprocessed-index binding, and bounded child-artifact verification
as downstream seams (`docs/spec/relations.md:390-407`). Those end-to-end chains
are not present today.

## 6. Normative correspondence judgment

### 6.1 Subject and intended algorithm

The normative input is:

```text
(sealed artifact, RelationContract, optional relation-artifact bytes)
```

The judgment is intended to:

1. authenticate the pinned claim-profile content and exact normative anchor
   partition;
2. find a covered artifact claim and compare its relation anchors;
3. optionally hash and parse relation bytes;
4. cross-check all available interface facts;
5. compare statement correspondence and material grounding; and
6. emit computed, cross-checked, and asserted facts, or named refusal
   (`docs/spec/relations.md:308-341`).

### 6.2 Normative anchor partition

| Profile | Relation anchors fixed by contract | Instance anchors read per artifact |
|---|---|---|
| `r1cs` | `a`, `b`, `c` | `public` |
| `opaque_relation` | `contract` | `statement` |

The partition must exactly cover the profile. Relation-anchor values scope the
contract to a relation; instance-anchor names identify fields that may vary by
artifact (`docs/spec/relations.md:105-136`).

### 6.3 Material grounding has two different rules

The normative document draws a load-bearing distinction:

- an **instance anchor** is grounded by a materially bound statement value
  whose label occurs in `statement_correspondence`;
- a **relation anchor** is grounded by a value equal to the anchor's normative
  transcript projection; statement wiring is irrelevant
  (`docs/spec/relations.md:205-221`).

A generic MaterialBinding only establishes declared stable-reference equality.
It does not by itself establish authorization, runtime bytes, or relation
meaning (`docs/spec/kernel.md:332-351`).

### 6.4 Anchor transcript projection

For a `sha256:` anchor, the normative projection takes the low 27 bits from
each of eight big-endian 32-bit digest words. It therefore carries 216 of 256
bits. The C++ implementation follows that algorithm and packs the eight limbs
at a 32-bit stride (`include/zkc/Relation/AnchorProjection.h:22-42`;
`lib/Relation/AnchorProjection.cpp:26-59`).

This projection is total for admitted anchor syntax and avoids field
reduction, but it is intentionally lossy as a map from digests. Equality of
projections is not equality of full SHA-256 references. The normative document
therefore requires a collision-game term in any rule that relies on this
binding (`docs/spec/relations.md:233-267`).

### 6.5 R1CS reading boundary

`r1cs-bin-v1` is a header-only reader. It scans the file's closed section-type
set, requires exactly one header, bounds every extent, rejects unknown section
types, and derives only:

```text
prime
public arity = public outputs + public inputs
private-input count
constraint count
wire count
```

It deliberately does not read constraint bodies or prove constraint meaning,
sufficiency, compiler correctness, or witness-generation correctness
(`docs/spec/relations.md:343-375`;
`include/zkc/Relation/R1csHeader.h:13-37`;
`lib/Relation/R1csHeader.cpp:96-214`).

### 6.6 Trust tiers and permanent nonclaims

The report's tiers are an evidence ledger:

- **computed** -- derived from the artifact or bytes alone;
- **cross-checked** -- two declared/derived sides agree;
- **asserted** -- a named party or assumption supplies meaning;
- the implementation additionally emits **disagreed** for negative
  cross-checks.

Agreement means consistency, not truth. The permanent asserted set includes:

- intended predicate meaning;
- absence of underconstraint;
- witness-generator correctness and completeness;
- meaning of slots and witness ports;
- byte provenance; and
- correspondence between supplied bytes and the relation named by sealed
  anchors (`docs/spec/relations.md:269-306`, `377-388`).

The judgment is therefore not and cannot be presented as
`RelationSatisfies(instance, witness)`.

## 7. Implemented correspondence path

The implementation currently performs this effective computation:

```text
contract = registry.lookup(caller_contract_name)
artifact = decode_and_admit(caller_artifact)
view     = buildSealedSoundnessView(artifact presentation)

check contract.profile digest against current ProtocolVocabulary
select first claim whose anchor dictionary contains all fixed relation anchors
optionally hash bytes and parse an R1CS header
cross-check available header/interface declarations
compare correspondence labels with view.statementLabels
compare optional caller field with contract field
detect seal-stage values equal to relation-anchor projections
inspect material references against correspondence labels
emit JSON {artifact, contract_digest, computed, cross_checked,
           disagreed, asserted}
return 0 when disagreed is empty, 1 otherwise, 2 before subject is reached
```

The core implementation is in `tools/zkc-relation/zkc-relation.cpp:90-434`.

### 7.1 What corresponds directly

The following intended behavior is present and has direct code support:

- closed RelationContract parsing and canonical contract digest;
- fixed `r1cs` and `opaque_relation` anchor partitions;
- claim-profile digest pin checking;
- refusal when no artifact claim carries the contract's relation anchors;
- empty-digest scope obligation;
- optional content hashing;
- bounded R1CS header parsing;
- arity, field, witness-count, and constraint-count comparisons;
- statement-label presence and protocol-only label reporting;
- relation-anchor projection recomputation;
- explicit attestation, bytes-to-anchor, statement-wiring, underconstraint,
  generator, and provenance assumptions; and
- a three-way exit taxonomy distinguishing affirmative, negative, and
  cannot-answer behavior.

### 7.2 What is presentation-dependent

`SealedSoundnessView` reconstructs the public statement ABI from PIR bind
labels (`lib/Soundness/PirSoundnessAdapter.cpp:721-728`). The relation tool
then decides correspondence using those labels
(`tools/zkc-relation/zkc-relation.cpp:273-295`). But PIR canonical identity is
fully positional and erases every author label
(`lib/Encoding/CanonicalEncoder.cpp:1-12`), and
`test/Encoding/relabel.mlir:1-35` confirms that consistently relabelled
protocols have the same PIR id.

Consequently, the same emitted subject pair
`(artifact_id, contract_digest)` can yield different correspondence results for
two id-equivalent PIR presentations: one presentation may use labels the
contract names and the other may consistently rename them. OIR later makes
endpoint labels identity-bearing (`docs/spec/carrier.md:480-484`), but the
relation report neither names an OIR artifact nor carries a separately
identified Protocol interface.

This is not merely missing ergonomics. The implementation's emitted subject is
insufficient to replay the label-sensitive judgment it reports.

### 7.3 Claim occurrence selection

The tool verifies the contract's profile pin globally, then scans
`claimAnchorsByIndex` and stops at the first anchor dictionary containing the
fixed relation anchors (`tools/zkc-relation/zkc-relation.cpp:117-173`). It does
not emit the matched `ClaimRef`, require the selected claim's profile in that
loop, compare exact full descriptor shape there, or diagnose multiple matching
occurrences.

The current two relation profiles use disjoint relation-anchor names, which
limits cross-profile ambiguity in the present registry. Multiple occurrences
of the same relation with different instance anchors remain possible, however,
and the first-match rule makes the correspondence report occurrence-ambiguous.

### 7.4 Report identity and consumption

The output JSON contains artifact id, contract digest, and four fact arrays
(`tools/zkc-relation/zkc-relation.cpp:411-434`). It has no:

- report schema/version tag;
- report identity or recomputed digest;
- exact claim occurrence;
- relation-byte input digest when the contract did not pin it as identity;
- caller-field input identity;
- source registry or admitted-authority record; or
- loader/consumer that admits it as an immutable premise.

This falls short of the normative requirement that correspondence output be
canonical identified content consumed by digest
(`docs/spec/relations.md:336-341`).

### 7.5 Concrete R1CS path

The repository's R1CS example makes the present boundary observable. Its
source claim carries matrix anchors plus a `public` instance anchor, while the
spine separately binds two scalar statement inputs labelled `x` and `cs`
(`test/Soundness/Inputs/r1cs-entry.mlir:9-14`). The RelationContract declares a
two-element field-vector instance and maps slots 0 and 1 to those labels
(`registry/relation-contracts.json:69-113`).

The only `pir.material_bind` in the example binds `%cs` to the downstream
batched-sum claim's `statement` anchor, not to the source relation claim's
`public` anchor (`test/Soundness/Inputs/r1cs-entry.mlir:27-30`). The relation
tool can nevertheless return an affirmative correspondence report because it
checks the source instance anchor's presence, declared arity, and label
existence; it does not require an actual instance-anchor binding or inspect the
runtime values of `x` and `cs`.

The paired soundness test then reports the downstream statement anchor as
grounded and carries the R1CS constraint count as an explicit assumption
(`test/Soundness/r1cs-entry.test:14-35`). That is valid evidence about the
Protocol claim chain. It is not evidence that the original `public` anchor is
the encoding of the two public values, that the R1CS bytes are the sealed
matrices, or that any witness satisfies them.

## 8. Protocol-facing seams

### 8.1 Anchors and MaterialBinding

Claim anchors inhabit the same digest-shaped namespace as MaterialRef. A
`pir.material_bind` connects one canonical local ValueRef to one stable
MaterialRef, and seal checks function/reverse-injectivity and actual
attachment use. Linking preserves MaterialRef and reindexes only ValueRef
(`docs/spec/kernel.md:319-351`; `docs/spec/boundaries.md:312-317`).

This is a useful identity seam, but its current guarantee is intentionally
narrow: declared reference equality. It does not prove that runtime bytes hash
to the reference, that a supplier is authorized, that a relation artifact is
the referenced relation, or that a witness satisfies it.

### 8.2 Statement ABI

Instance-stage `pir.bind` operations supply the current statement ordering.
Projection turns them into ordered OIR `statement_labels` and public arguments
(`docs/spec/endpoints.md:53-76`;
`lib/Dialect/Pir/Transforms/PirProject.cpp:260-299`, `340-355`).

There are currently three different views of “the statement”:

1. an opaque claim instance anchor;
2. a positionally identified PIR instance-stage bind whose author label is
   excluded from PIR identity; and
3. an OIR public argument whose label and order are included in OIR identity.

RelationContract maps relation slots to the second view by author label. No
identified current object unifies all three.

This also means projection over two PIR presentations with the same Protocol
id can produce different OIR identities, because projection reads the erased
PIR labels while OIR deliberately authenticates them. Projection remains
deterministic over the complete admitted in-process artifact capability; it is
not currently a function of `ProtocolId` alone, and it names no separate
interface input that accounts for the difference.

### 8.3 Interface-like current behavior

What a future reader might mistake for one Protocol interface is currently
distributed across independent authorities:

| Fact | Current owner |
|---|---|
| Claim anchor schema | Claim profile in ProtocolVocabulary |
| Exact relation/instance anchor partition | `relations.md` plus RelationContract loader |
| Public-instance encoding | RelationContract |
| Relation slot to statement label mapping | RelationContract |
| Public input order and payload classes | PIR instance binds, projected to OIR |
| Endpoint statement labels | OIR identity |
| Witness port declaration | RelationContract |
| Witness handle labels/classes | PIR construction routes and prover OIR |
| Check ABI | CheckContract / OIR check call |
| Child artifact ABI | Reserved bounded `artifact_verify` row |

There is no `ProtocolInterface` object, id, admission judgment, or exact
Protocol-to-interface relation in the current implementation.

### 8.4 Plan-like current behavior

Two unrelated current mechanisms use plan-like ideas:

- **PIR construction routes** are identity-bearing Protocol content. They
  declare route witnesses, exact HoleContract instances, typed ordered
  references, and proof-slot sources. They are the closest current analogue to
  prover orchestration, but they are not a separately identified subject and
  carry no relation-satisfaction or completeness theorem
  (`docs/spec/endpoints.md:291-327`).
- **CompilerPlan** selects checked Protocol transformations and soundness
  derivation steps. It is not a prover plan and does not bind witness inputs,
  suppliers, or relation invocation.

Prover-skeleton OIR is a projected endpoint program rather than a plan subject.
Backend realization remains reserved. There is no current `PlanRealizes`
judgment.

### 8.5 Satisfaction and execution

Terminal closure establishes a typed implication edge to the propositions
named by checks. For opaque checks it pins predicate identity and structural
ABI, not predicate execution (`docs/spec/kernel.md:571-576`;
`docs/spec/boundaries.md:160-169`).

Endpoint execution may run check suppliers and prover-hole suppliers, but its
contracts are operational. Verifier acceptance is not automatically a
relation-correspondence theorem; prover success is not relation satisfaction;
and conformance evidence is scoped to exact runs and acceptors
(`docs/spec/endpoints.md:182-189`, `329-370`).

No implemented judgment currently takes an admitted relation definition,
typed instance, witness capability or assignment, and evaluator semantics and
returns a satisfaction result with attributable residual trust.

## 9. Soundness, Fiat--Shamir, and property transport

### 9.1 Analysis subjects remain Protocol claims

The Soundness Kernel's closed subject set is:

```text
ProtocolClaim {artifact_id, claim_ref}
ConsumedClaimVector {artifact_id, consumer_claim_ref, ordered sources}
ExternalInstance {subject_schema, typed_arguments}
```

Direct rule application concludes about an exact Protocol claim occurrence
(`docs/spec/soundness.md:68-142`). There is no RelationDefinition,
RelationInstance, RelationCorrespondence, ProtocolInterface, or invocation
subject.

`claim_unsatisfied(claim_ref)` occurs as the one admitted round-state predicate
(`docs/spec/soundness.md:229-247`). This is a semantic index inside the theorem
context, not an executable relation predicate recovered from the claim's
anchors. Likewise, the completeness interpretation speaks abstractly of an
honest prover holding a witness in the subject's relation
(`docs/spec/soundness.md:300-325`); current carrier and evaluator types do not
construct that relation or witness.

### 9.2 Current Fiat--Shamir model

There is no current `FSCompile` construct in source or current normative
specifications. The kernel gives one spine two readings:

- fresh challenge sampling for the interactive reading; or
- execution by the selected construction profile's duplex runner for the
  Fiat--Shamir reading (`docs/spec/kernel.md:78-97`).

The executable analysis bridge is
`StateRestorationToFiatShamirDuplex`. It takes a StateRestoration
`ScalarResult`, retains its bound exactly once, and adds construction-specific
capacity, codec-bias, and relation-anchor collision terms to produce a
FiatShamir `ScalarResult` (`docs/spec/soundness.md:875-913`).

This transforms a security judgment index about the same Protocol claim. It
does **not** construct a distinct fresh-public-coin Protocol and Fiat--Shamir
Protocol, identify source/target event occurrences, record transcript-prefix
maps, establish a structural construction relation, or separate construction
from a property-specific theorem.

### 9.3 Bound-relation-anchor count mismatch

The FS collision term is specified as scaling with the artifact's
bound-relation-anchor count. The current projection scans every claim but looks
only for an anchor literally named `contract`, projects that value, and counts
matching seal-stage bindings (`lib/Soundness/SoundnessProjection.cpp:657-685`).
Its focused test also exercises only a `contract` anchor
(`test/lib/TestSoundnessProjection.cpp:158-195`).

This corresponds to `opaque_relation`, but not to the relation-domain partition
for `r1cs`, whose relation anchors are `a`, `b`, and `c`. Meanwhile the relation
CLI applies transcript-projection detection to every RelationContract
`relation_anchor` (`tools/zkc-relation/zkc-relation.cpp:317-337`). The phrase
“bound relation anchor” therefore has two incompatible operational extents in
current code. An R1CS relation anchor can be reported transcript-carried by the
relation tool while contributing zero to the soundness projection.

### 9.4 General property transport is absent

Compiler `LEGAL` establishes only the checked structural transition and its
bound relation. A `PreservationClaim` carries an open property reference,
exact family revision, and application index, but the family checker does not
establish the property. Derivation witnesses repeat these claims as
`preservation_obligations`; they are not conclusions
(`docs/spec/compiler.md:675-734`).

Current Soundness and Completeness have their own typed rule systems. Zero
knowledge is not built. There is no general `PropertyTransport` judgment and
no rule connecting a relation correspondence, Protocol transformation, FS
construction, or composition relation to an arbitrary property.

## 10. Composition and verifier descent

### 10.1 Claim-flow composition

LIN gives the claim-flow graph a linear string-diagram reading over exact claim
descriptors. Its cited denotation is a reduction of knowledge, with transcript
interleaving preventing general commutation
(`docs/spec/kernel.md:405-453`). This is meaningful Protocol-local composition
of claim occurrences and reduction contracts.

It is not composition of mathematical relations, RelationContracts, instance
maps, witness maps, or satisfaction predicates.

### 10.2 Static `link`

Current `link(OpenP, OpenP)`:

- splices and namespaces event spines;
- composes exact claim flows and rechecks LIN;
- rechecks imported challenge and domain obligations;
- preserves material references;
- re-runs reduction and terminal closure; and
- namespaces, rewrites, and rechecks construction routes
  (`docs/spec/boundaries.md:279-334`).

The result is a new open Protocol. `link` does not take RelationContracts as
inputs, choose among multiple contracts describing one relation, compose
public-instance correspondence, combine witness interfaces, or establish a
relation between child and composite satisfaction.

Static link is also not a general semantic Protocol-composition judgment. It
records authoring/link structure. The current Soundness Kernel separately
requires exact theorems for interleaved or shared-challenge groups and otherwise
treats them as one composite application or refuses to price them
(`docs/spec/kernel.md:968-1035`). `RoundByRoundPreservation` is narrower still:
it requires guarded contiguous spans and names current occurrence, message,
interactive-only, and round-identity limitations
(`docs/spec/soundness.md:920-967`).

### 10.3 Verifier descent

`descend : SealedP(realized verifier) -> RelationPayload'` is reserved. The
specification fixes only the direction and several requirements:

- child claims and ABI transfer by artifact reference;
- residual/export/assumption routes remain explicit;
- heuristic in-circuit random-oracle assumptions remain visible; and
- self-reference requires a separate identity extension
  (`docs/spec/kernel.md:1037-1084`; `docs/spec/boundaries.md:336-352`).

No carrier, projection rule, execution rule, or security theorem is admitted.
The related bounded `artifact_verify` endpoint effect is also reserved and
requires eleven exact bindings, including child Protocol, relation-contract,
statement/ABI, proof slots, assumptions, claims, provenance, and failure
behavior (`docs/spec/endpoints.md:138-180`). Current status reports only eight
of those eleven facts in a carrier row; both endpoint projections refuse it,
no child is verified, and nothing composes (`docs/status.md:119`).

Verifier-as-relation behavior is therefore a specified seam and partial carrier
shape, not a current relation construction.

## 11. Normative-to-implementation correspondence matrix

| Requirement or behavior | Current implementation | Classification |
|---|---|---|
| Closed RelationContract fields and variants | Enforced by registry loader | Corresponds |
| Tagged canonical RelationContract digest | Computed at load | Corresponds |
| Exact profile-specific anchor partition | Enforced by loader | Corresponds |
| Contract profile pin checked against vocabulary | Enforced by CLI | Corresponds |
| Contract consumed by digest, never resolved by name | CLI requires `--contract=<registry key>` and performs name lookup before judging | **Direct conflict** |
| Contract remains outside seal and Protocol identity | Relation registry absent from ProtocolEnvironment and seal | Corresponds |
| Exact covered claim occurrence | CLI chooses the first relation-anchor match and emits no ClaimRef | **Gap / ambiguity** |
| Optional byte digest and bounded R1CS header facts | Implemented | Corresponds |
| Content/header disagreement is a named refusal | CLI emits a negative report and exit 1 after subject examination | **Direct outcome conflict** |
| Field compared with artifact soundness derivations | CLI compares only optional caller `--expect-field-order` and says so | **Implementation gap** |
| Statement labels checked | Implemented from loaded PIR presentation | Partial; identity instability |
| Relation-anchor material grounding uses transcript projection, not statement wiring | Projection carriage is checked separately, but material-bind loop applies statement-wiring logic to relation and instance anchors alike | **Direct conflict** |
| Instance-anchor grounding uses wired statement label | Implemented when a MaterialRef match and label exist | Partial; no typed runtime instance |
| All relation anchors included in FS collision count | Soundness projection recognizes only anchor name `contract` | **Cross-domain conflict** |
| Witness ports connect to endpoint witness inputs | No comparison with routes/OIR handles/invocation | **Gap** |
| `opaque_bytes` and `commitment` instance encodings bind actual values | Schema only | **Gap** |
| Correspondence output is canonical, digest-cited content | JSON is canonicalized but has no report tag/id/digest or admitting consumer | **Implementation gap** |
| Predicate meaning and relation satisfaction remain external | Kernel, seal, relation report, and prover conformance preserve the nonclaim | Corresponds |
| RelationContract may drive bounded child verification | Digest field is reserved in the future contract only | Reserved, not implemented |

### 11.1 Name lookup versus digest-only consumption

The normative document says registry keys are lookup handles outside the entry
digest and that “no judgment resolves a contract by name -- consumption cites
the digest” (`docs/spec/relations.md:55-61`). The C++ registry repeats that
contract (`include/zkc/Registry/RelationContractRegistry.h:107-132`). The CLI,
however, requires a contract entry name and calls `lookup(contractName)`
(`tools/zkc-relation/zkc-relation.cpp:29-35`, `90-100`). It reports the resolved
digest afterward, but name-based selection is still part of the actual
judgment invocation.

### 11.2 Refusal versus negative judgment

The normative algorithm says a content-digest mismatch, malformed declared
format, and every failed field comparison refuse
(`docs/spec/relations.md:313-341`). Current code and tests deliberately choose
a different model: once comparison has begun, disagreements are accumulated in
the emitted report and return exit 1; exit 2 is reserved for failure to reach
the subject (`tools/zkc-relation/zkc-relation.cpp:52-67`, `175-225`,
`430-434`; `test/Relation/relation-disagreements.test:1-68`).

The implementation's model preserves more negative information, but it is not
the normative outcome algebra currently written. Stage 3.1 records the
conflict without choosing between them.

### 11.3 Relation-anchor grounding conflict

The spec requires different tests for the two anchor partitions. The CLI first
detects any seal-stage value equal to a relation anchor's projection. It then
builds one combined map of relation and instance anchors and, for every
MaterialRef match, requires the bound value's label to occur in
`statement_correspondence` (`tools/zkc-relation/zkc-relation.cpp:317-376`).

For a relation anchor, that second rule is wrong under the current normative
text: the value should equal the fixed transcript projection, and statement
wiring is explicitly not the question. The implementation can therefore
accept a wired but nonprojected relation-anchor binding in this loop or report
disagreement for a correctly projected relation identity whose label is not an
instance label.

### 11.4 Live predicate-spec contradiction

The sharpest authority conflict is between the opacity/evidence-only model and
one live ProtocolVocabulary predicate:

- `vocabularies.md` says `opaque_relation.contract` and `.statement` are
  uninterpreted bytes and neither resolves to a RelationContract, relation
  instance, or application statement (`docs/spec/vocabularies.md:142-148`).
- `relations.md` says a RelationContract is post-seal evidence whose presence
  conditions only the correspondence judgment (`docs/spec/relations.md:25-46`).
- the live “Content-addressed RelationContract application” predicate interprets
  the `contract` semantic parameter as the digest of a canonical
  RelationContract, resolves that contract's “pure relation-decision
  entrypoint,” and uses a witness source declared by its binding
  (`registry/protocol-vocabulary.json:116-136`). The
  `zkc.terminal.relation-direct` rule supplies the `opaque_relation` claim's
  `contract` and `statement` anchors to that predicate
  (`registry/protocol-vocabulary.json:3737-3763`).

The current RelationContract schema has no decision entrypoint, predicate
implementation, witness source, or execution binding, and its loader is closed
against such fields. Seal pins the predicate text as proposition identity but
does not execute it. Thus the checked-in semantic inputs assign an operational
meaning to an anchor that the normative documents forbid and require fields
that the only admitted RelationContract schema cannot express.

This predicate cannot be treated as a hidden completion of the relation model.
It is internally unresolvable under the current schema.

## 12. Test and example evidence

### 12.1 Evidence that was executed during this reconstruction

The current `build/unittests/Relation/ZkcRelationTests` binary completed with:

```text
13 cases, 0 failed
```

Those cases exercise the anchor projection and bounded R1CS header reader.
This is bounded implementation evidence only; it is not evidence for full
relation correspondence or satisfaction.

The two focused lit integration tests were also selected for a live run, but
the local lit runner could not create its multiprocessing fork-server socket in
the execution sandbox. No pass claim is made for that attempted run. Their
checked-in assertions were inspected as repository-declared evidence below.

### 12.2 Repository-declared relation evidence

| Test surface | What it exercises | Important boundary |
|---|---|---|
| `unittests/Relation/AnchorProjectionTest.cpp:31-115` | Exact low-bit mapping, canonical field limbs, packing, determinism, retained-bit distinction, malformed anchors | Does not test the known discarded-bit collisions |
| `unittests/Relation/R1csHeaderTest.cpp:81-163` | Good header facts, public output/input arity, every refusal class, prefix truncation, arbitrary bytes, width bounds | Reads no constraints and proves no relation meaning |
| `test/Relation/relation-contract.test:1-95` | Registry admission, no-bytes asserted result, bytes-backed cross-checks, foreign contract refusal, R1CS malformed cases, profile pin, format/encoding coupling, Python/C++ registry parity | Parity covers registry canonicalization, not correspondence computation |
| `test/Relation/relation-disagreements.test:1-68` | Negative constraint/witness/field/content/readability disagreements, multiple disagreements, exact exit 1 | Explicitly notes missing arity-negative fixture |
| `test/Soundness/r1cs-entry.test:14-79` | Conditional R1CS entry pricing, named constraint-count assumption, re-derivation, tampered grounding refusal | Prices a Protocol claim; does not check R1CS constraints or witness satisfaction |
| `test/Encoding/relabel.mlir:1-35` | PIR id stability under author-label renaming | Exposes the relation report's label-sensitive subject problem when combined with current CLI behavior |
| `test/lib/TestSoundnessProjection.cpp:158-195` | `contract` anchor projection counted as one or zero | Does not cover `r1cs` relation anchors `a`, `b`, `c` |

### 12.3 What the current tests do not establish

No located test establishes:

- a mathematical relation definition or evaluator;
- relation-artifact bytes corresponding to sealed relation anchors;
- constraint-body parsing, non-underconstraint, or source-compiler correctness;
- an actual `RelationInstance` value under any of the three encodings;
- `opaque_bytes` instance hashing or `commitment` instance binding;
- nontrivial statement-correspondence permutations against identity-stable
  interface subjects;
- relation-anchor versus instance-anchor material-binding behavior as two
  separate rules;
- multiple matching relation-claim occurrences;
- RelationContract witness-port correspondence to route/OIR witness handles;
- witness ownership, confidentiality, lifetime, or satisfaction;
- correspondence-report identity, admission, replay, or consumption;
- relation-aware static link composition;
- a fresh-to-Fiat--Shamir Protocol construction relation;
- general property transport;
- child-verifier descent or recursive relation satisfaction; or
- whole-Protocol security from relation correspondence.

## 13. Conflicts, gaps, and unknowns

### 13.1 Direct current conflicts

1. **Evidence-only versus executable RelationContract.** The normative
   RelationContract cannot provide the entrypoint and witness binding demanded
   by the live `relation-direct` predicate.
2. **Digest-only versus name-based selection.** The spec prohibits judgment
   resolution by registry name; the CLI requires it.
3. **Refusal versus negative report.** The spec refuses failed comparisons;
   code and tests emit a negative judgment.
4. **Partition-specific grounding versus one wiring loop.** The implementation
   applies instance-label wiring logic to relation anchors.
5. **All relation anchors versus `contract` only.** The relation CLI and FS
   collision projection operationalize different anchor sets.
6. **Artifact identity versus label-sensitive correspondence.** PIR identity
   erases the labels the report uses, while the report identifies only the PIR
   artifact and contract.

### 13.2 Incomplete current implementation

- relation report lacks its specified identity, exact subject, and admission
  path;
- artifact-derived soundness field compatibility is replaced by caller input;
- claim occurrence selection is first-match and not part of output;
- no relation adapter produces admitted interface facts;
- no typed instance value reaches the correspondence judgment;
- no witness-port-to-route or witness-port-to-invocation relation exists;
- committed-object metadata is not connected to relation instance/witness
  semantics;
- no current consumer uses a correspondence report as an admitted premise;
- no relation satisfaction judgment exists;
- link does not compose relation interfaces, instance maps, or witness maps;
- verifier descent and bounded artifact verification remain reserved; and
- compiler property claims are obligations, not transport results.

### 13.3 Unknowns that current artifacts cannot answer

The current corpus does not determine:

1. what identifies a relation independently of source, artifact bytes,
   RelationContract documents, and Protocol anchor tuples;
2. whether two artifacts or two contracts denote the same mathematical
   relation, a refinement, or unrelated interfaces;
3. what the exact subjects and identities of relation interface, relation
   instance, statement instance, witness interface, and witness assignment are;
4. how an actual invocation binds public values and private capabilities to
   those subjects;
5. who may mint, supply, delegate, consume, or retain a witness capability;
6. which judgment establishes satisfaction, with what evaluator authority,
   evidence, outcomes, and residual trust;
7. how a correspondence result is identified, authenticated, admitted,
   replayed, invalidated, and consumed;
8. how relation refinements, instance maps, witness maps, and Protocol
   composition interact;
9. whether Fiat--Shamir is only an interpretation of one Protocol or an
   explicit source-to-target Protocol construction in the intended final
   model;
10. which properties can transport across which construction or refinement
    relations, and under what theorem/model basis; and
11. how verifier descent represents child relation, interface, instance,
    assumptions, ABI, and satisfaction without widening the child claim.

These are genuine semantic unknowns. They cannot be filled by treating current
anchor names, report prose, construction routes, or status terminology as
latent definitions.

## 14. Exact Stage 3.1 conclusion

The current repository has two strong foundations:

1. an opaque-anchor Protocol core that precisely identifies claim occurrences,
   claim flow, transcript structure, and declared material-reference equality;
   and
2. a useful post-seal RelationContract ledger that distinguishes computed,
   cross-checked, and asserted interface facts and refuses to overclaim relation
   truth.

It does not yet have an integrated Relations semantics. Relation definition,
actual instance values, witness capabilities and assignments, satisfaction,
identified Protocol interfaces, separate prover plans, committed-object
relation semantics, explicit FS construction, general property transport,
relation-aware composition, and verifier descent are absent, fragmented, or
reserved.

Several pieces also cannot simply be promoted unchanged: the live
`relation-direct` predicate contradicts the evidence-only contract model; the
correspondence report is not determined by the identities it emits; its
outcome, grounding, field-source, and consumption behavior drift from the
normative document; and the Soundness and Relations domains disagree about
which relation anchors are transcript-bound.

This reconstruction does **not** decide how those issues should be repaired. It
fixes the current baseline that later Stage 3 alternatives must explain rather
than silently inherit.
