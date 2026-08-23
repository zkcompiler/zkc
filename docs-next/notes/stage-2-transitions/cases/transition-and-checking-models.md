# Transition and checking models

> **Document kind:** Temporary comparative research dossier
> **Document state:** External-case research pass
> **Stage:** Stage 2 — typed transitions and bridges
> **Cases:** CompCert, Alive2, proof-carrying code, LRAT, MLIR dialect
> conversion and Transform dialect, Capsicum, WebAssembly Component Model
> resources, CBOR, OCI descriptors, Protocol Buffers, StableHLO/VHLO, TUF,
> W3C PROV, in-toto/SLSA, and IETF RATS
> **Authority:** None. External source facts, transfer hypotheses, and analogy
> limits are kept distinct. This document neither defines a zkc transition nor
> establishes that any current implementation conforms to a proposed model.
> **Disposition:** Absorb reviewed findings into exact Stage 2 owners and
> durable decisions, then delete this page.

## 1. Scope

This dossier studies external mechanisms only where they illuminate a concrete
question in the
[Stage 2 transition and bridge charter](../../stage-2-transition-and-bridge-charter.md):

- what a successful transition actually establishes;
- whether the claim concerns one subject or a source/target pair;
- which observations define preservation or refinement;
- how an untrusted producer can be separated from a trusted checker;
- which checker failures mean rejection, unsupported input, or inconclusive
  search;
- whether authority survives persistence or only semantic content does;
- how byte identity, schema identity, and semantic identity differ;
- what replay means for mathematical facts versus operational evidence; and
- how provenance, appraisal, and a relying consumer's policy remain separate.

The selection deliberately excludes systems whose similarity is only that they
have an IR, a verifier, a hash, or a signed record. It also avoids importing a
complete external architecture. Each case is used for one narrow transfer.

The recurring conclusion is not that zkc needs one universal transition
framework. It is the opposite:

> A transition result is meaningful only after its relation, exact subjects,
> declared context, checking basis, authority lifetime, and relying policy have
> been named. Those dimensions do not collapse into one generic notion of
> validity.

### 1.1 Reading discipline

The labels below have distinct force:

- **Source fact** reports a mechanism or limitation stated by a primary paper
  or official specification.
- **Design inference** extracts a general consequence from that mechanism.
- **zkc transfer** proposes how the consequence may answer a Stage 2 question.
- **Analogy limit** states what the external case cannot establish for zkc.
- **Pain point** records a cost, failure mode, or difficult boundary exposed by
  the case.

No **zkc transfer** is a ratified contract. No cited external result implies
that current PIR, compiler, OIR, realization, or evidence code already has the
corresponding property.

## 2. Comparative map

| Case | What the mechanism can establish | Principal pain point | Narrow zkc use |
|---|---|---|---|
| CompCert | A proved source/target semantic-preservation theorem for accepted compiler executions | Every pass and intermediate semantics enter the proof architecture | Distinguish verified transformation from checked transformation and choose relations from protected observations |
| Alive2 | Bounded, per-execution refinement validation for LLVM transformations | Undefined behavior, semantic underspecification, solver limits, and loop bounds become validation limits | Make validator scope, unsupported cases, bounds, and inconclusive outcomes explicit |
| Proof-carrying code | A target artifact satisfies a fixed consumer safety policy, checked from an attached proof | Policy and proof logic must already express the property the consumer needs | Separate target-property certificates from source/target correspondence |
| LRAT | A compact trusted checker can validate an expensive producer's unsatisfiability proof with explicit hints | Certificate design trades producer effort, certificate volume, and checker complexity | Keep witnesses unauthoritative and bind checked claims to their exact subjects |
| MLIR conversion | Legality relative to a configured conversion target, with full or partial conversion modes | Configured legality is not semantic preservation; partial conversion deliberately permits residual operations | Use MLIR to organize structural rewrites without treating conversion success as a Protocol relation |
| MLIR Transform dialect | Typed orchestration of transformations with explicit failure propagation and payload handles | Handle validity and mutation effects are operational properties, not semantic proof | Separate transform proposal/orchestration from zkc relation checking |
| Capsicum | Possession and attenuation of unforgeable object-specific authority | Authority is tied to a live kernel object and explicit delegation mechanism | Model admission as an opaque capability, not as a serializable identifier |
| WebAssembly resources | Instance-scoped owned and borrowed opaque handles with lifetime rules | A handle index has meaning only inside its resource table and runtime | Model scoped consumer views and non-portable capability representations |
| CBOR | A deterministic byte profile when an application fixes all relevant choices | Generic CBOR has multiple encodings and application-level validity remains separate | Separate parseability, deterministic carrier encoding, identity, and admission |
| OCI descriptors | Retrieval and byte binding through media type, byte digest, and size | A digest authenticates bytes, not their interpretation or semantic closure | Keep transport/content references distinct from `ProtocolId` |
| Protocol Buffers | Schema evolution with a defined wire-compatibility discipline | Wire-compatible changes can still change application meaning; format conversion can lose unknown fields | Treat schema compatibility and semantic compatibility as separate claims |
| StableHLO/VHLO | An explicit, tested portability window with versioned upgrade/downgrade machinery | Compatibility has feature, time-window, artifact-construction, and bug-behavior exclusions | Introduce durable schema/version machinery only with a named consumer and promise |
| TUF | Detection of rollback or stale signed metadata using trusted local state and expiration | Authentic historical data may still be unacceptable now | Attach freshness only to claims whose relying policy needs it |
| W3C PROV | Structured lineage among entities, activities, and agents | Provenance records derivation but not correctness | Represent origin and execution history without making it semantic proof |
| in-toto/SLSA | Signed, digest-bound predicates followed by explicit policy verification | Authentication and subject binding do not establish the predicate's truth | Layer envelope authentication, claim parsing, subject binding, semantic checking, and policy |
| IETF RATS | Separation of evidence production, verifier appraisal, attestation result, and relying-party decision | Trust and policy remain use-specific even after verification | Preserve observation/evidence/appraisal/reliance as separate transition families |

## 3. Verified compilation, translation validation, and refinement

### 3.1 CompCert: proof over the accepted compiler execution

**Source fact.** CompCert specifies source and target observable behavior and
proves a semantic-preservation theorem for successful compiler runs. Its
account of behavior includes termination, divergence, going wrong, and traces
of interactions with the external world. Because source semantics can be
nondeterministic, preservation is not naively defined as equality of one
execution; the theorem constrains target behaviors by the source behaviors for
source programs that do not go wrong. See Leroy's primary
[CompCert verification paper](https://www.cs.cmu.edu/~15811/papers/compcert.pdf)
and the official [CompCert documentation](https://compcert.org/doc/).

**Design inference.** A preservation relation is downstream of an observation
model. “Equivalent” is empty until termination, failure, external events,
nondeterminism, and permitted target choices have been fixed.

**zkc transfer.** Every checked Protocol transformation should name its
protected observers rather than inherit a generic `equivalent` bit. Depending
on the transition, the relevant claim may be `CoreEq`, `ProtocolEq`, `TraceEq`,
`TraceRefines`, distributional equality or closeness, `FSCompile`,
`ProjectionCorrect`, `PlanRealizes`, or intentional non-preservation. The
relation must say which of transcript, wire, public values, checks, artifacts,
claims, and terminal outcomes it observes.

**Pain point.** A fully verified compiler is not one local theorem around an
otherwise opaque pipeline. Pass composition requires semantics for the
intermediate languages and a relation that composes across passes. Optimizing
or restructuring an IR before its observation model stabilizes can therefore
make the proof boundary much larger than expected.

**Analogy limit.** CompCert's theorem is for the semantics and assumptions of
the particular C-to-assembly compiler. It does not supply a relation for
interactive protocols, random coins, transcript-dependent challenges,
cryptographic assumptions, or probabilistic closeness. zkc must define those
relations independently.

### 3.2 CompCert's translation-validation pattern

**Source fact.** The same CompCert paper distinguishes a verified compiler
from translation validation. In validation, an untrusted transformation
produces a candidate target and a verified validator establishes the specified
source/target relation after the fact. Since the relation is generally
undecidable, a sound validator may reject or decline candidates that are in
fact correct. CompCert uses a posteriori validation in selected passes such as
register allocation.

**Design inference.** Candidate generation and authority issuance can be split:

```text
untrusted or heuristic proposer(source, configuration)
  -> candidate target + optional witness

trusted relation checker(source, target, declared context, optional witness)
  -> checked relation result
```

The candidate and witness may improve speed, but neither is authoritative.
Authority comes from the checker's result under its stated contract.

**zkc transfer.** Translation validation is a strong default candidate for
optimization, linking, normalization, projection, and realization steps whose
search logic is much larger or more volatile than the relation checker. It is
especially attractive where a checker can recompute protected observations or
validate a compact witness without trusting the proposal algorithm.

**Pain point.** `validator returned false` is ambiguous unless the API types
the reason. It can mean an actual counterexample, malformed candidate,
unsupported feature, exhausted resource bound, or inability to prove a true
relation. Treating all of those as “the target is invalid” confuses checker
incompleteness with semantic refutation.

**Analogy limit.** The architecture does not show that every zkc transition has
a small decidable checker. It can fail when preservation is probabilistic,
requires a cryptographic reduction, depends on an open environment, or is as
hard to check as constructing the target.

### 3.3 Alive2: refinement plus explicit validation limits

**Source fact.** Alive2 performs translation validation for LLVM IR
optimizations. Its principal relation is refinement: the target may remove
source nondeterminism but must not introduce behavior unavailable to the
source. Correct handling of poison and undefined behavior is central to the
relation. The primary evaluation reports that formalizing LLVM semantics also
exposed specification ambiguities and disagreements. See the
[Alive2 PLDI paper](https://users.cs.utah.edu/~regehr/alive2-pldi21.pdf) and
the authors' [publication record](https://web.ist.utl.pt/nuno.lopes/pubs.php?id=alive2-pldi21).

**Source fact.** The evaluated checker is deliberately bounded. Loop unrolling,
solver time, memory, unsupported operations, and its intraprocedural scope
limit what it can establish. A clean validation run is therefore a claim under
those limits, not an unbounded proof about every possible transformation
context.

**Design inference.** Building a validator is also a specification audit. The
difficult work often lies in defining exact source and target observations,
partiality, nondeterminism, and environmental assumptions rather than in
encoding the final solver query.

**zkc transfer.** A Stage 2 checker contract should expose:

```text
relation kind
source and target semantic regimes
declared dependencies and configuration
protected observer set
supported feature/profile set
search or proof bounds
checker outcome and refusal reason
counterexample or witness, when available
```

`AcceptedUnderBound`, `Unsupported`, `Inconclusive`, and `RelationRefuted`
must not collapse into one boolean. The exact names remain Stage 2 design work.

**Pain point.** Refinement direction is easy to reverse accidentally. “Target
behaviors are contained in source behaviors” is not interchangeable with
source/target equality, implementation coverage, or preservation of every
claim. A relation must also state how undefined or inadmissible subjects enter
its domain.

**Analogy limit.** LLVM refinement does not automatically preserve a protocol's
challenge distribution, transcript framing, public interface, claim set,
knowledge assumptions, or proof-system security statement. Alive2 transfers
the validation discipline, not its concrete relation.

### 3.4 Stage 2 consequence

The cases support three separate mechanisms rather than a hierarchy where one
is always stronger:

| Mechanism | Trusted basis | Natural use | Characteristic failure |
|---|---|---|---|
| Verified transformation | Transformation implementation plus its proof and semantic model | Small stable passes or an end-to-end compiler with justified proof investment | Proof or model does not cover an implementation path |
| Translation validation | Relation checker, semantic model, and declared inputs | Large heuristic search with independently checkable output | Unsupported or inconclusive candidate, or refuted relation |
| Target-property checking | Property checker and policy, independent of the source | Safety, well-formedness, resource, or target-local claim | Target does not satisfy property or certificate cannot be checked |

“Verified,” “validated,” and “certified” must consequently never be accepted as
standalone result kinds.

## 4. Proof-carrying and certificate-checking models

### 4.1 Proof-carrying code: a property of the target

**Source fact.** In proof-carrying code, a producer supplies executable code
and a proof that it satisfies a safety policy fixed by the consumer. The
consumer checks the proof without trusting the producer or an external
certification service. See Necula's primary
[proof-carrying code paper](https://doi.org/10.1145/263699.263712) and the
[OSDI presentation of the model](https://www.usenix.org/legacy/publications/library/proceedings/osdi96/full_papers/necula/html/node2.html).

**Design inference.** A certificate is useful only relative to a named claim
language and consumer. A proof that a target satisfies `SafeTarget(P)` does not
by itself establish that `P` was derived from source `S`, preserves `S`, or
covers all source behavior.

**zkc transfer.** Stage 2 should keep at least these classes distinct:

```text
TargetPropertyCertificate(target, property, regime)
TransitionCertificate(source, target, relation, regimes, context)
ProjectionCoverageCertificate(protocol_interface, oir, endpoint_role)
RealizationCertificate(plan, supplier_bindings, target, realization_claim)
```

This is a conceptual separation, not a decision to create four serialized
formats. A direct local check may be preferable until an independent consumer
or retention requirement exists.

**Pain point.** The certificate cannot repair a weak policy. If the consumer's
policy omits transcript framing, public-output coverage, or a required
dependency, a valid proof of that policy can still be inadequate for the
consumer's real purpose.

**Analogy limit.** Proof-carrying code addresses target-code safety. It does not
provide a protocol equivalence, a cryptographic reduction, or a proof that an
endpoint realizes its Protocol.

### 4.2 LRAT: producer-friendly evidence and a small final checker

**Source fact.** LRAT was designed so unsatisfiability proofs can be checked by
simple, efficient, formally verified checkers. It adds ordered hints and a
more restrictive proof discipline than producer-oriented DRAT. The paper also
demonstrates a pipeline in which an untrusted fast checker or converter can
produce optimized hints, while a final verified checker validates the result
against the original formula. See the primary
[LRAT paper](https://www.cs.cmu.edu/~mheule/publications/lrat.pdf).

**Design inference.** Witnesses and hints may be generated by arbitrary search
without acquiring authority. A final checker remains sound only if it binds
the witness back to the exact original subjects and claim. Checking a
self-described certificate against no independently identified source merely
proves internal consistency of the certificate.

**zkc transfer.** When a zkc relation is expensive to rediscover but cheap to
check, a certificate may contain proof hints, matched nodes, dependency paths,
coverage maps, or algebraic witnesses. Its durable claim, if any, must bind:

- a typed claim kind;
- exact source and target semantic references;
- both semantic regimes where they differ;
- all declared semantic context and configurations;
- the checker contract or proof system used;
- the checked outcome; and
- any witness or certificate content by authenticated reference.

Execution provenance, signatures, and freshness can be additional fields, but
they do not replace the semantic binding above.

**Pain point.** Certificate design moves cost rather than eliminating it.
Stronger hints can enlarge producer work or certificate size; a more permissive
certificate can enlarge the trusted checker's logic. Storage and schema
stability become obligations if certificates are retained.

**Analogy limit.** LRAT proves propositional unsatisfiability. It does not show
that zkc's interactive, probabilistic, or cryptographic relations admit small
certificates. It supports the producer/checker split only when a particular
relation has an independently justified proof object.

### 4.3 When not to introduce a certificate

The external cases do not justify certificate proliferation. A portable
certificate is warranted only when at least one of these conditions holds:

- a different process or organization must check the result without rerunning
  expensive search;
- the result must survive after the generating capability or environment ends;
- audit, cache, or reproducibility requirements need a stable claim artifact;
- the checker is materially smaller or more stable than the producer; or
- a downstream policy engine needs a typed input independent of the producer.

If the consumer is in the same process and direct recomputation is cheap, an
opaque checked capability is simpler and avoids prematurely freezing a
certificate schema.

## 5. MLIR: structural legality and transformation orchestration

### 5.1 Dialect conversion establishes configured legality

**Source fact.** MLIR's official
[Dialect Conversion documentation](https://mlir.llvm.org/docs/DialectConversion/)
defines conversion relative to a `ConversionTarget`, rewrite patterns, and
optionally a type converter. Operations can be statically legal, dynamically
legal, illegal, or recursively legal. Full conversion succeeds only when all
relevant operations have become legal; partial conversion intentionally
allows operations not marked illegal to remain.

**Design inference.** “Legal MLIR” is parameterized by the target and its
callbacks. Full conversion is stronger than partial conversion only with
respect to that configured legality relation. Neither mode states that a
domain-level semantic relation holds.

**zkc transfer.** MLIR conversion is appropriate for:

- closing a candidate over the canonical PIR operation/type profile;
- driving structural authoring-to-canonical rewrites;
- rejecting operations forbidden by a selected carrier profile; and
- organizing dialect crossings whose semantic checker is separately named.

If a conversion target, dynamic legality callback, type converter, pattern
set, or option affects acceptance, it belongs to the transition's declared
read set or identified checker configuration. It is not harmless ambient
state.

**Pain point.** Recursive legality can deliberately stop inspection beneath an
operation, and partial conversion can deliberately leave unknown structure.
Those are useful compiler tools but dangerous if their result is relabeled as
whole-Protocol admission. The accepted closure must be independently stated.

**Analogy limit.** MLIR does not know zkc's Protocol identity, semantic regime,
dependency closure, challenge interpretation, protected observers, claim set,
or probabilistic semantics. Successful dialect conversion cannot issue
`ProtocolEq`, `TraceRefines`, `FSCompile`, or `ProjectionCorrect` merely because
the resulting operations are legal.

### 5.2 Transform dialect is a controller, not a semantic proof

**Source fact.** The official
[Transform dialect documentation](https://mlir.llvm.org/docs/Dialects/Transform/)
separates transform IR from the payload IR. Transform operations manipulate
payload through typed handles and report success, silenceable failure, or
definite failure. Handle invalidation and payload mutation are part of the
operational contract; some expensive handle-consistency checks are optional
diagnostics rather than a universal semantic theorem.

**Design inference.** Typed handles and explicit failure propagation improve
transformation orchestration, but type-correct orchestration proves neither
semantic preservation nor completeness of a projection. A successful script
means that its operational preconditions were met and its transformations ran
under their implementation contracts.

**zkc transfer.** A future zkc compiler may use Transform dialect or an
equivalent controller to propose candidates, schedule passes, and retain
targeted handles. The authority boundary should still be:

```text
transform orchestration
  -> candidate Protocol, OIR, or realization artifact
  -> domain-specific checker
  -> typed relation result or refusal
```

The checker must consume the exact semantic subjects, not infer them from a
live transform handle whose payload can later mutate.

**Pain point.** Mutation creates temporal coupling. A handle or diagnostic that
was valid before a rewrite may no longer denote the same payload afterward.
Durable evidence must therefore bind immutable subject identities rather than
MLIR object addresses or pass-local handles.

**Analogy limit.** Transform dialect failure categories should inform, not
dictate, zkc's result algebra. A zkc negative analysis judgment can be a valid
successful derivation, while a transform failure describes execution of the
controller. Those are different dimensions.

### 5.3 Verifiers and pass execution

**Source fact.** MLIR's official
[pass-management documentation](https://mlir.llvm.org/docs/PassManagement/)
supports verifier execution around passes and explicit pass failure. These
mechanisms enforce registered IR invariants and prevent a failed pipeline from
being reported as successful.

**zkc transfer.** Four results must remain separate even if one implementation
invokes them in sequence:

```text
MLIR parse success
registered operation/type verification
canonical PIR profile and closure admission
domain relation check for the named transition
```

Each later layer may assume the earlier layer only when the capability or
receipt carrying that assumption is explicit and still live.

**Analogy limit.** An MLIR verifier implements invariants registered by a
dialect. It does not establish any invariant that was omitted, nor does it
turn a local operation verifier into a whole-subject semantic proof.

## 6. Capabilities and process-local authority

### 6.1 Capsicum: designation plus authority

**Source fact.** Capsicum uses file descriptors as unforgeable tokens naming
specific kernel objects and associates them with rights that can be attenuated.
Entering capability mode removes access through ambient global namespaces;
authority is obtained through possessed capabilities and explicit delegation.
See the primary
[Capsicum paper](https://www.cl.cam.ac.uk/research/security/capsicum/papers/2010usenix-security-capsicum-website.pdf).

**Design inference.** A name and the authority to act on its referent are
different things. Possessing a pathname or integer descriptor value outside
the table that interprets it does not recreate the capability. Derived
capabilities can expose fewer operations without changing the underlying
object.

**zkc transfer.** `ProtocolId` can designate semantic content, while an opaque
`AdmittedProtocol` capability can authorize operations that rely on admission
under a particular regime and checked basis. A purpose-specific consumer view
may attenuate that authority by exposing only the operations needed for
analysis, projection, or compilation.

Serialization should preserve a reference or artifact, not silently preserve
authority:

```text
live AdmittedProtocol
  -> persisted canonical artifact + identifiers
  -> transport/storage boundary
  -> decode + authenticate + re-admit
  -> new local AdmittedProtocol
```

Serializing an object address, descriptor number, pointer, or nominal wrapper
must never mint the new capability.

**Pain point.** Process-local capability APIs introduce lifetime and FFI
discipline. If raw carrier objects remain accessible beside the checked handle,
consumers may bypass the intended authority boundary or read fields that were
not authenticated by admission.

**Analogy limit.** Capsicum is kernel-enforced access control over mutable
operating-system resources. A Rust or C++ wrapper is not automatically
unforgeable at that strength, and zkc admission represents epistemic/API
authority over an immutable semantic subject rather than permission to mutate
a resource. Capsicum also supports explicit capability transfer; it does not
prove that all cross-process transfer must be forbidden. Re-admission is a zkc
design choice requiring its own rationale.

### 6.2 WebAssembly Component Model resources: owned and borrowed handles

**Source fact.** The official Component Model
[MVP explainer](https://github.com/WebAssembly/component-model/blob/main/design/mvp/Explainer.md)
and [WIT resource design](https://github.com/WebAssembly/component-model/blob/main/design/mvp/WIT.md)
define opaque resource handles classified by resource type. Owned handles are
uniquely held and dropped; borrowed handles are scoped and cannot outlive the
call. Runtime tables mediate the opaque handle representation.

**Design inference.** Type and lifetime can prevent a temporary view from
silently becoming a durable independent authority. A serialized numeric handle
has no meaning outside the particular live instance and table.

**zkc transfer.** Stage 2 can distinguish:

- an owning admitted capability retaining its immutable admission basis;
- a borrowed, purpose-specific consumer view whose lifetime cannot exceed the
  owner; and
- a durable certificate or artifact with its own schema and identity, created
  only through an explicit checked transition.

A borrowed view must not be made durable merely by encoding its internal
fields.

**Pain point.** Lifetime safety at one language boundary does not automatically
survive C APIs, plugins, asynchronous work, caches, or distributed execution.
The transition contract must state whether retained work holds the owning
capability, copies authenticated immutable inputs, or requires later
re-admission.

**Analogy limit.** The Component Model remains an evolving official design, and
its resources solve ABI ownership rather than semantic verification. Its
drop/borrow rules do not imply that immutable zkc capabilities need destructor
semantics or the same table implementation.

## 7. Persistence, content addressing, schema evolution, and replay

### 7.1 CBOR: deterministic encoding is an application profile

**Source fact.** [RFC 8949](https://www.rfc-editor.org/rfc/rfc8949.html)
permits multiple encodings of the same CBOR data item. Its deterministic
encoding rules form an explicit profile, including shortest forms, avoidance
of indefinite lengths, and deterministic map-key ordering. The RFC also
distinguishes well-formed CBOR from validity and from what an application
expects, and requires protocols to settle choices such as allowed tags and
numeric representations.

**Design inference.** Selecting a serialization family does not select one
canonical byte string or one semantic interpretation. Determinism, accepted
schema, and application validity are additional contracts.

**zkc transfer.** Persisted PIR should expose a layered boundary:

```text
byte framing and parseability
transport-schema validity
zkc deterministic carrier-profile validity
referenced-content authentication
semantic identity recomputation
dependency closure and semantic admission
```

The implementation may fuse layers, but evidence and failure categories should
say which layer accepted or refused the input.

**Pain point.** Round trips through a less expressive representation can lose
types, tags, ordering distinctions, or unknown data. A parse/serialize round
trip is not identity-preserving unless the exact profile proves it.

**Analogy limit.** Deterministic CBOR establishes a byte-level convention. It
says nothing about Protocol meaning, admissible dependencies, or whether two
different encodings should share `ProtocolId`.

### 7.2 OCI descriptors: byte binding is not semantic admission

**Source fact.** The official OCI image
[descriptor specification](https://github.com/opencontainers/image-spec/blob/main/descriptor.md)
uses a media type, digest, and size to describe and verify retrieved content.
Descriptors connect content-addressed artifacts into graphs, while optional
annotations carry additional metadata.

**Design inference.** A digest establishes equality to particular bytes under
an algorithm. It does not establish that the bytes decode as the expected
semantic type, that their referenced graph is closed, or that an interpreter
assigns the intended meaning.

**zkc transfer.** A transport reference can contain:

```text
media or schema identifier
byte digest and digest algorithm
byte size
```

That reference must remain distinct from `ProtocolId`. Admission can verify
both, but a byte digest cannot substitute for semantic identity. Optional
annotations remain non-semantic only if no normative transition reads them.

**Pain point.** Systems often overload one hash as transport integrity,
semantic identity, cache key, and authorization token. The meanings diverge as
soon as canonicalization changes, equivalent encodings exist, metadata is
added, or a resolver supplies a different dependency graph.

**Analogy limit.** OCI's content graph is a distribution mechanism. Its edges
do not confer authority to interpret referenced declarations and do not model
Protocol semantic closure.

### 7.3 Protocol Buffers: wire compatibility is not semantic compatibility

**Source fact.** The official
[Protocol Buffers language guide](https://protobuf.dev/programming-guides/proto3/)
defines wire-safe schema evolution and preservation of unknown fields during
binary parse/serialize. Unknown fields can nevertheless be lost through JSON
conversion or field-by-field reconstruction. Some wire-compatible changes can
also alter application-level behavior, including collection interpretation or
numeric meaning.

**Design inference.** “Old reader can parse new bytes” and “old reader assigns
the intended meaning” are different compatibility claims. Preservation of
unknown data is not authority to interpret it.

**zkc transfer.** A transport envelope may preserve fields unknown to an older
tool, but canonical PIR admission should fail closed when an unknown construct
could affect semantic identity, dependencies, observers, or claims. Any JSON,
text, diagnostic, or compatibility conversion that can lose semantic material
is a named transition with an explicit loss policy, not a transparent round
trip.

**Pain point.** Schema evolvability can conflict with semantic immutability. A
field that was “unknown metadata” cannot later become semantic without defining
how historical identities and old readers are treated.

**Analogy limit.** Protocol Buffers is optimized for evolvable messages. It
does not define immutable Protocol subjects or a semantic-equivalence relation
between schema versions.

### 7.4 StableHLO/VHLO: compatibility as a bounded product promise

**Source fact.** StableHLO defines explicit serialization/deserialization APIs,
a compatibility policy, and a versioned VHLO form for portable artifacts. Its
official [compatibility policy](https://github.com/openxla/stablehlo/blob/main/docs/compatibility.md)
specifies backward and forward compatibility windows and limits the promise to
artifacts produced through named portability mechanisms. Producer downgrades
can fail when a program uses features unavailable in the target version. The
official [VHLO design](https://openxla.org/stablehlo/vhlo) uses versioned,
add-only operations and maintained upgrade/downgrade paths.

**Design inference.** Long-lived compatibility is not a consequence of using
MLIR bytecode. It is a product contract over producer versions, consumer
versions, artifact construction, supported feature subsets, migration logic,
test matrices, retention duration, and explicit exclusions.

**zkc transfer.** Stage 2 should not freeze a portable transition-certificate
or PIR migration schema merely because persistence exists. First name the
independent consumer, required retention window, acceptable downgrade failures,
semantic regime evolution rule, and test obligation. If such a consumer exists,
an add-only compatibility form may be justified outside canonical Protocol
identity.

**Pain point.** Compatibility machinery has permanent carrying cost. New
features require versioned representations and downgrade policies; behavioral
bugs and numerical subtleties may lie outside the compatibility promise.

**Analogy limit.** StableHLO's tensor-operation portability does not establish
Protocol equivalence, preservation of cryptographic claims, or compatibility
between semantic regimes. It demonstrates governance and mechanism, not the
correct zkc version window.

### 7.5 TUF: authentic history can still be stale

**Source fact.** The official
[TUF specification](https://github.com/theupdateframework/specification/blob/master/tuf-spec.md)
requires clients to track trusted metadata versions, check expiration, and
reject rollback or inconsistent snapshots. A previously validly signed object
can therefore be authentic yet unacceptable for a current update decision.

**Design inference.** Replay is not one universal property. A mathematical
relation over immutable subjects can remain true indefinitely under the same
regime and assumptions. An operational observation, supplier statement,
deployment appraisal, revocation-sensitive endorsement, or “latest” policy can
become stale even if its bytes and signature remain valid.

**zkc transfer.** Freshness, expiration, supersession, and trusted prior state
belong only to claim types whose semantics require them. They should not be
global fields that accidentally make timeless semantic correspondence expire.
For replay-sensitive evidence, the relying policy must say which clock,
sequence, version, or prior state it uses.

**Pain point.** Stateless verification cannot detect all replay. Once a claim
requires monotonicity or freshness, the verifier or relying party must retain
trusted state or consult another trusted source.

**Analogy limit.** TUF protects an update workflow. It neither re-admits a
Protocol nor proves a source/target semantic relation. Its role here is only to
separate authenticity from current acceptability.

## 8. Evidence, provenance, appraisal, and reliance

### 8.1 W3C PROV: lineage without truth

**Source fact.** The W3C
[PROV data model](https://www.w3.org/TR/prov-dm/) describes entities,
activities, agents, and relations such as generation, use, derivation,
attribution, and association. Its constraints can detect inconsistent temporal
or structural provenance records.

**Design inference.** Provenance can answer who or what generated an artifact,
which inputs were recorded, and how records derive from one another. It cannot
establish that the producing activity implemented the intended relation or
that an asserted conclusion is true.

**zkc transfer.** Evidence records may use a provenance graph to connect:

```text
identified source and target subjects
checker execution
declared configuration and dependencies
producer, checker, and environment identities
generated result or certificate
later appraisal activity
```

The semantic relation result remains owned by its checker contract. Provenance
must not become a universal fact root that can assert arbitrary semantic facts
without domain checking.

**Pain point.** Rich provenance graphs easily become ambient bags of metadata.
Fields that a normative consumer reads must be promoted to explicit typed
inputs; fields used only for audit or display must not affect semantic identity.

**Analogy limit.** PROV is deliberately domain-general. It does not define
`ProtocolEq`, evidence sufficiency, cryptographic trust, or the authority of a
zkc checker.

### 8.2 in-toto and SLSA: authenticate, bind, then apply policy

**Source fact.** The in-toto
[Statement specification](https://github.com/in-toto/attestation/blob/main/spec/v1/statement.md)
binds a typed predicate to one or more subjects by digest. Its
[Envelope specification](https://github.com/in-toto/attestation/blob/main/spec/v1/envelope.md)
separates the signed envelope from the statement payload. The official
[validation model](https://github.com/in-toto/attestation/blob/main/docs/validation.md)
verifies signatures and subject binding before returning predicates and
recognized attesters to a policy engine. The SLSA
[artifact-verification guidance](https://slsa.dev/spec/v1.2/verifying-artifacts)
then checks provenance fields such as builder identity, subject digest,
predicate type, and build parameters against expectations.

**Design inference.** At least four questions remain independent:

1. Was this envelope authentically issued by a recognized principal?
2. Does it bind to the exact artifact bytes under an accepted digest?
3. Is its predicate a well-formed claim of a recognized type?
4. Does a checker or relying policy accept the claim for this use?

A signature can answer the first and support the second. It does not prove the
predicate's semantic truth.

**zkc transfer.** Durable transition evidence should layer:

```text
envelope authentication, when needed
typed claim-schema parsing
typed semantic subject binding
semantic checker result or independently checkable certificate
execution provenance
consumer-specific appraisal and reliance
```

Byte digests alone are too weak for semantic subject binding: zkc evidence
should also identify the subject type, semantic identity, regime, and claim
kind. The attester identity can be evidence about origin without becoming
semantic authority.

**Pain point.** A valid signature over a self-asserted predicate is easy to
overstate as “verified.” Conversely, a correct semantic certificate may not
answer supply-chain questions about who ran the checker, which binary ran, or
whether the relying consumer trusts that execution environment.

**Analogy limit.** in-toto and SLSA describe supply-chain attestations and
policy verification. They do not prove protocol semantics. Their digest-based
subject model should not replace zkc's typed semantic identities.

### 8.3 IETF RATS: evidence, appraisal result, and relying decision

**Source fact.** [RFC 9334](https://www.rfc-editor.org/rfc/rfc9334.html)
separates an Attester that produces Evidence, a Verifier that appraises the
Evidence against reference values and appraisal policy, an Attestation Result,
and a Relying Party that applies its own policy to decide whether and how to
use the result.

**Design inference.** Verification does not authorize every downstream use.
The verifier decides what follows from evidence under one policy; the relying
party decides whether that result is adequate for its particular action.

**zkc transfer.** The Stage 2 sequence should preserve the same separation at
the semantic level:

```text
operational event or observation
  -> attributed evidence record
  -> appraisal under an explicit evidence policy
  -> typed appraisal result
  -> consumer-specific reliance decision
```

A well-formed negative or noncompliant appraisal can be a successful appraisal
result. Malformed evidence, unsupported evidence type, failed authentication,
and a negative appraisal are different outcomes. A later refusal to rely does
not retroactively invalidate the Protocol, OIR, or observation.

**Pain point.** Combining appraisal and reliance lets a checker authorize its
own use. It also makes one consumer's trust assumptions look like universal
semantic facts.

**Analogy limit.** RATS is a remote-device attestation architecture. Reference
measurements and device trust do not correspond directly to mathematical
Protocol semantics. The transferable result is the role separation, not its
trust anchors or evidence formats.

## 9. Cross-case synthesis for Stage 2

### 9.1 A layered acceptance model

The external cases support the following diagnostic stack:

```text
1. carrier parse
2. transport and schema check
3. deterministic-profile and byte-subject authentication
4. typed semantic subject reconstruction and identity check
5. source and target admission under exact regimes
6. relation, property, coverage, or realization check
7. local capability or durable typed result issuance
8. provenance/envelope validation, where required
9. consumer appraisal and reliance
```

This is not one mandatory pipeline. Authoring may begin before persistence;
local analysis may need neither a signed envelope nor a durable certificate;
appraisal may consume observations rather than a source/target pair. The stack
exists to prevent one layer's success from impersonating another layer's
claim.

### 9.2 Candidate outcome dimensions

One flat `Result<Verified, Error>` would erase important information. Stage 2
should test a product of at least these dimensions:

```text
ExecutionStatus:
  Completed | Refused | FailedOperationally

InputStatus:
  WellFormed | Malformed | Unsupported | Unresolved

CheckStatus:
  Established | Refuted | Inconclusive | NotApplicable

JudgmentValue:
  Positive | Negative | Conditional | NotAJudgment

AuthorityEffect:
  None | BorrowedView | LocalCapability | DurableTypedResult
```

The names and factorization are hypotheses, not selected types. Their purpose
is to preserve distinctions demonstrated by the cases:

- a negative analysis judgment can be successfully derived;
- a valid source can have an unsupported projection;
- a sound incomplete validator can be inconclusive about a correct target;
- malformed evidence differs from evidence appraised as noncompliant;
- a transform can fail operationally after mutation without proving semantic
  invalidity of its original source; and
- a durable record can be authentic yet stale for one reliance policy.

### 9.3 Candidate checker placement by transition family

| zkc transition family | Preferred first mechanism to investigate | Why | What it must not imply |
|---|---|---|---|
| Canonical PIR admission | Direct structural and semantic recomputation producing a local opaque capability | Admission must close over exact bytes, semantic subject, regime, and dependencies | Serialization of the capability or preservation of a pointer-like token |
| Persist/decode/re-admit | Byte/schema authentication followed by fresh semantic admission | Content can cross a process; admission authority is re-established locally | Byte digest equals `ProtocolId`, or decode success equals admission |
| Compiler/link/normalization proposal | Untrusted producer plus relation validator where the relation is independently checkable | Keeps heuristic search outside authority | Every failed validation means the source or target is invalid |
| Property analysis | Direct decision procedure or purpose-specific certificate | Negative conclusions are valid results; evidence needs an exact property | Target-local property implies source/target equivalence |
| Relation correspondence | Pair-bound checker over exact subjects, regime, contract, and observer set | The claim is inherently relational | A certificate about either subject alone establishes correspondence |
| OIR projection | Paired source/OIR capability and source-bound coverage result | Source-relative coverage cannot be recovered from source-free OIR alone | OIR well-formedness establishes projection completeness |
| Supplier binding/realization | Separate plan, supplier, target, and realization checks, followed by observations | Abstract meaning and operational availability fail independently | One successful execution proves general realization correctness |
| Observation/evidence/appraisal | Typed evidence followed by policy-qualified appraisal and reliance | Provenance and trust are consumer-specific | A signed record is semantically true, or appraisal modifies Protocol validity |

### 9.4 Candidate durable result fields

If a named consumer justifies durable transition evidence, the minimum schema
should be tested against the following fields:

```text
ClaimTypeId
SourceSubjectRefs[]
TargetSubjectRefs[]
SemanticRegimeRefs[]
DeclaredContextRefs[]
CheckerContractId
CheckerConfigurationId, when semantically relevant
Outcome
WitnessOrCertificateRef, when independently checkable
ExecutionProvenanceRef, when operational provenance matters
EnvelopeAndIssuerRef, when authentication matters
FreshnessOrSupersessionData, only for replay-sensitive claim types
```

The result's own identity is not the source or target identity. Signing the
record authenticates the issuer; it does not upgrade the checked claim.
Including a witness does not make the witness authoritative; it remains input
to the checker.

### 9.5 Mechanism-selection questions

For each transition, Stage 2 should answer these questions in order:

1. What exact proposition must a downstream consumer rely on?
2. Is it target-local, relational, observational, or policy-qualified?
3. Which immutable subjects and regimes determine that proposition?
4. Can it be recomputed directly and cheaply at the consumption boundary?
5. If not, is candidate search separable from a smaller sound checker?
6. If the checker is incomplete, how are unsupported and inconclusive results
   represented?
7. Does the result need to outlive the checked capability or cross a trust
   boundary?
8. If durable, which schema, compatibility, replay, and authentication promises
   are actually required?
9. Which consumer owns the final adequacy or reliance decision?

Only those answers determine whether the right mechanism is a direct check, a
borrowed view, a local admitted capability, translation validation, a portable
certificate, a verified transformation, or a policy appraisal.

## 10. Concrete design pressures and open questions

The external cases create the following Stage 2 pressures without deciding
their final resolution:

1. **Define relations from observers.** Every preservation or refinement claim
   needs an explicit protected observer set and direction.
2. **Keep proposal outside authority.** Optimizers, converters, solvers, and
   certificate producers may remain untrusted when a sound independent checker
   exists.
3. **Make incompleteness visible.** Unsupported, resource-exhausted,
   inconclusive, and refuted outcomes need different meanings.
4. **Separate target properties from transition relations.** A safe or valid
   target is not necessarily the right target for a source.
5. **Treat MLIR legality as one input layer.** Full conversion, operation
   verification, semantic admission, and relation checking remain distinct.
6. **Do not serialize authority accidentally.** Semantic identifiers and
   canonical artifacts can persist; local admission capabilities and borrowed
   views require explicit reconstruction or re-admission.
7. **Separate byte and semantic identity.** Media type, digest, schema,
   `ProtocolId`, dependency closure, and regime are different axes.
8. **Make compatibility a named promise.** A durable schema requires a consumer,
   version window, migration behavior, exclusions, and tests.
9. **Scope replay by claim type.** Timeless semantic facts and freshness-sensitive
   operational evidence should not share one blanket expiration rule.
10. **Keep provenance, checking, appraisal, and reliance distinct.** An origin
    record, a semantic result, and authorization to act are not substitutes.

Open questions for the owning Stage 2 synthesis include:

- Which relations admit complete decision procedures, sound incomplete
  validators, proof-producing checkers, or only conditional research claims?
- Does `ProtocolEq` require equality of all protected observers, or is it a
  family indexed by regime and observer contract?
- Which compiler transformations intentionally change `ProtocolId`, and which
  representation transitions must preserve it?
- What is the minimal immutable admission basis retained by
  `AdmittedProtocol`, and which consumers currently read carrier-only context?
- Can OIR coverage be checked from `ProtocolInterfaceId` plus role, or does it
  require additional authenticated Protocol material?
- Which results have a real cross-process or long-retention consumer that
  justifies a portable certificate?
- Where do solver bounds, cryptographic assumptions, statistical error, and
  trusted reference implementations appear in result types?
- Which operational evidence types are replay-sensitive, and which semantic
  results are timeless under an exact regime?
- What smallest checker contract can remain stable if producer algorithms and
  MLIR pass pipelines evolve?

## 11. Reversal conditions

The transfers above should be reconsidered if any of the following becomes
true:

- the authoritative semantic subject cannot be reconstructed independently of
  mutable MLIR carrier state;
- every useful transformation relation is as complex to check as to produce,
  eliminating the assumed translation-validation boundary;
- a consumer demonstrably needs admission authority to cross a process rather
  than content plus re-admission;
- a portable certificate has no independent consumer or cannot bind all
  semantic inputs needed by its claim;
- a schema-compatibility promise is required sooner than the named consumer,
  retention window, and semantic migration policy can be stated;
- source-relative OIR coverage can be fully established from independently
  identified interface material, changing the paired-capability tradeoff;
- freshness is shown to be semantic for a relation currently treated as
  timeless; or
- one proposed outcome factorization cannot represent a real checker without
  reintroducing an untyped generic status.

## 12. Primary and official references

### Verified compilation and checking

- Xavier Leroy,
  [Formal Verification of a Realistic Compiler](https://www.cs.cmu.edu/~15811/papers/compcert.pdf),
  primary CompCert paper.
- [CompCert official documentation](https://compcert.org/doc/).
- Nuno P. Lopes et al.,
  [Alive2: Bounded Translation Validation for LLVM](https://users.cs.utah.edu/~regehr/alive2-pldi21.pdf),
  primary PLDI paper.
- George C. Necula,
  [Proof-Carrying Code](https://doi.org/10.1145/263699.263712), primary paper.
- Luís Cruz-Filipe, Marijn Heule, Warren Hunt, Matt Kaufmann, and Peter
  Schneider-Kamp,
  [Efficient Certified RAT Verification](https://www.cs.cmu.edu/~mheule/publications/lrat.pdf),
  primary LRAT paper.

### MLIR

- [MLIR Dialect Conversion](https://mlir.llvm.org/docs/DialectConversion/),
  official documentation.
- [MLIR Transform dialect](https://mlir.llvm.org/docs/Dialects/Transform/),
  official documentation.
- [MLIR pass management](https://mlir.llvm.org/docs/PassManagement/), official
  documentation.

### Capabilities and scoped handles

- Robert N. M. Watson et al.,
  [Capsicum: Practical Capabilities for UNIX](https://www.cl.cam.ac.uk/research/security/capsicum/papers/2010usenix-security-capsicum-website.pdf),
  primary USENIX Security paper.
- WebAssembly Component Model,
  [MVP explainer](https://github.com/WebAssembly/component-model/blob/main/design/mvp/Explainer.md)
  and [WIT resource design](https://github.com/WebAssembly/component-model/blob/main/design/mvp/WIT.md),
  official design documents.

### Persistence, schemas, and replay

- IETF, [RFC 8949: Concise Binary Object Representation](https://www.rfc-editor.org/rfc/rfc8949.html).
- Open Container Initiative,
  [Image descriptor specification](https://github.com/opencontainers/image-spec/blob/main/descriptor.md).
- Protocol Buffers,
  [proto3 programming guide](https://protobuf.dev/programming-guides/proto3/),
  official documentation.
- StableHLO,
  [compatibility policy](https://github.com/openxla/stablehlo/blob/main/docs/compatibility.md)
  and [VHLO design](https://openxla.org/stablehlo/vhlo), official documents.
- The Update Framework,
  [official specification](https://github.com/theupdateframework/specification/blob/master/tuf-spec.md).

### Evidence and reliance

- W3C, [PROV Data Model](https://www.w3.org/TR/prov-dm/), Recommendation.
- in-toto Attestation Framework,
  [Statement](https://github.com/in-toto/attestation/blob/main/spec/v1/statement.md),
  [Envelope](https://github.com/in-toto/attestation/blob/main/spec/v1/envelope.md),
  and [validation model](https://github.com/in-toto/attestation/blob/main/docs/validation.md),
  official specifications.
- SLSA,
  [Verifying artifacts](https://slsa.dev/spec/v1.2/verifying-artifacts), official
  specification guidance.
- IETF,
  [RFC 9334: Remote ATtestation procedureS Architecture](https://www.rfc-editor.org/rfc/rfc9334.html).
