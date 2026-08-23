# IR carrier and schema contracts

> **Document kind:** Temporary Stage 3 primary-source case dossier
> **Document state:** Stage 3.2 research complete; convergence input
> **Research date:** 2026-08-22
> **Authority:** None. This dossier does not select a Protocol grammar,
> canonical PIR schema, encoding, version policy, or composition model.
> **Question:** What should zkc learn from mature IR and interchange systems
> about keeping semantic meaning, schema closure, validation, identity,
> versioning, composition, interfaces, and bytes distinct?
> **Disposition:** Preserve accepted transfer limits and reversal rationale
> through the Stage 3 absorption record and durable architecture owners;
> delete this dossier with the completed package before authority cutover.

## 1. Scope and evidence discipline

This dossier studies five pressure clusters:

1. upstream MLIR as a multi-level carrier and transformation framework;
2. StableHLO and VHLO as a stable portable contract built on MLIR;
3. SPIR-V as a compact binary language qualified by capabilities and execution
   environments;
4. WebAssembly Core and the Component Model as a separation between abstract
   semantics, non-unique encodings, validation, and typed interfaces; and
5. zkInterface as a proof-adjacent constraint and witness interchange
   boundary.

Only primary sources are used: official specifications and documentation,
project design repositories, and the zkInterface specification and source
repository. Moving specifications are identified by the release or revision
visible on the research date. Claims about what zkc should do are explicitly
marked as **Stage 3 inference**; they are not claims made by the source system.

This is not a performance comparison, ecosystem ranking, or argument that one
format should be copied. None of the cases models an interactive proof
Protocol with zkc's exact observation, challenge, occurrence, authority, and
relation boundaries.

## 2. The first distinction: four meanings of “canonical”

The cases expose four different concepts that must not share one predicate:

| Concept | Question | Counterexample from the cases |
|---|---|---|
| Schema closure | Is every meaning-bearing construct drawn from a known finite contract? | MLIR modules may mix dialects; a full conversion can impose closure for one target, but MLIR itself does not. |
| Validated semantic object | Does the decoded object satisfy the rules for one declared regime or environment? | SPIR-V validity is qualified by universal rules plus a client execution environment. |
| Unique physical encoding | Does one semantic object have exactly one admitted byte representation? | WebAssembly explicitly permits multiple binary encodings of the same integer. |
| Optimization normal form | Has a rewrite system selected a preferred program shape? | MLIR states that its canonicalizer is best-effort and has no formally defined canonical form. |

Stable serialization is a fifth, independent property: it asks whether a
producer and consumer separated in time can exchange an artifact. StableHLO
demonstrates that this requires a versioned semantic compatibility layer above
MLIR bytecode; the bytecode format alone cannot provide it for a changing
dialect.

**Stage 3 inference.** A future zkc design must name separate judgments for at
least closed-schema membership, structural well-formedness, regime-qualified
semantic admission, physical canonical encoding, semantic identity, and
transformation correspondence. Passing one must never mint the result of
another.

## 3. Upstream MLIR: powerful carrier, deliberately incomplete semantic policy

### 3.1 What MLIR actually supplies

**Source fact.** The [MLIR Language Reference](https://mlir.llvm.org/docs/LangRef/)
defines a generic operation/region/block/SSA structure and dialect namespaces.
Multiple dialects can coexist in one module, and dialects define operations,
types, and attributes. The framework therefore permits many abstraction levels
and domain meanings without giving them one universal denotation.

**Source fact.** Textual value identifiers are writer-chosen and are not
persisted as part of the IR. Symbol and value scoping are carrier mechanisms,
not durable semantic identity.

**Strength.** This gives zkc a mature structural substrate: nested regions,
typed SSA values, symbols, locations, generic text, extensible operations,
verification hooks, rewriting, and conversion infrastructure can be reused
without forcing every domain into one low-level instruction vocabulary.

**Stage 3 inference.** MLIR is a strong primary workbench for rich authoring
and lowering. Its generic object model is not, by itself, the definition of a
Protocol, its semantic identity, its observations, or the relation it claims
to realize.

### 3.2 Conversion legality is not semantic preservation

**Source fact.** The
[Dialect Conversion framework](https://mlir.llvm.org/docs/DialectConversion/)
defines a target, rewrite patterns, and an optional type converter. Partial
conversion can leave operations that were not marked illegal; full conversion
succeeds only if every input operation is legal for the declared target;
analysis conversion asks what appears legalizable without committing rewrites.
Legality may be static, dynamic, illegal, or unknown.

This is an excellent closure mechanism, but the framework does not define what
the source and target mean or prove that the patterns preserve an external
semantics.

**Stage 3 inference.** A zkc canonical-PIR conversion should use full,
fail-closed target legality. Its result still needs a separate source-to-target
correspondence judgment. “All remaining operations are legal” is not evidence
for `ProtocolEq`, trace refinement, distributional preservation, or property
transport.

### 3.3 MLIR canonicalization is not physical or semantic canonicality

**Source fact.** The official
[Operation Canonicalization documentation](https://mlir.llvm.org/docs/Canonicalization/)
says the pass greedily applies patterns until a fixpoint or a configured limit,
is best-effort, must not be required for pipeline correctness, and has no
formally defined canonical form. The de facto form changes as patterns and
folders evolve.

**Strength.** That policy is appropriate for compiler simplification: local
patterns can improve downstream analyses without freezing the whole ecosystem.

**Hard-to-reverse pressure.** The same freedom makes the standard
canonicalizer unsuitable as a content-addressing or admission boundary. Its
loaded pattern set, iteration limits, implementation release, and evolving
community conventions can affect the output.

**Stage 3 inference.** `mlir-opt --canonicalize` must not define canonical PIR
bytes or `ProtocolId`. If zkc needs a physically canonical representation, it
requires a closed, deterministic, version-bound encoder over an already
admitted semantic object, with no ambient dialect or pass registry in its read
set.

### 3.4 Bytecode stability delegates dialect evolution

**Source fact.** The
[MLIR Bytecode Format](https://mlir.llvm.org/docs/BytecodeFormat/) is versioned
and designed for old-bytecode reading and back-deployment. The documentation
immediately qualifies this promise: compatibility assumes immutable dialects.
A changing dialect must implement its own version payload, decoding, and
post-parse upgrade through `BytecodeDialectInterface`. The bytecode permits
custom dialect encodings and a textual assembly fallback for attributes and
types.

**Strength.** Container evolution, compression, lazy loading, and dialect-local
encoding can change without each project inventing a binary container.

**Hard-to-reverse pressure.** Dialect authors, not the MLIR container, own the
semantic compatibility burden. Custom encodings and textual fallback also
mean that “valid MLIR bytecode” does not imply one stable schema, one closed
dialect set, or one unique encoding.

**Stage 3 inference.** zkc should treat MLIR bytecode as one carrier envelope.
The Protocol regime must identify the exact semantic schema independently of
the MLIR container version. A decoder may produce a candidate; it cannot
silently upgrade that candidate into the same semantic identity or admitted
authority.

### 3.5 MLIR transfer boundary

The transferable mechanism is:

```text
rich mixed workbench
  -> explicit full-conversion closure
  -> closed canonical-PIR candidate
  -> independent semantic admission and correspondence
  -> deterministic physical encoding
```

The non-transferable assumption is that dialect namespaces, SSA names,
registered verifiers, canonicalization patterns, or bytecode decoder success
are Protocol semantics.

## 4. StableHLO and VHLO: stability is a product layer, not a carrier property

### 4.1 A specified closed language over an extensible framework

**Source fact.** The
[StableHLO specification](https://openxla.org/stablehlo/spec) defines program,
operation, and execution semantics and describes StableHLO operations as a
closed set. StableHLO uses some upstream MLIR module and function operations
for interoperability. CHLO and common shape-dialect operations do not receive
the same compatibility guarantee and must be legalized before portable
serialization.

**Strength.** The project does not rely on the fact that an operation can be
represented in MLIR. It names which operations participate in the portable
semantic contract and closes unsupported dialect leakage before the exchange
boundary.

**Hard-to-reverse pressure.** Reusing upstream operations reduced integration
cost but made their continued compatibility part of StableHLO's promise. The
spec says StableHLO equivalents would be added if those upstream operations
changed incompatibly. This is a concrete example of a convenient dependency
becoming a long-lived contract.

**Stage 3 inference.** Canonical PIR should minimize meaning-bearing dependency
on generic or foreign dialect constructs. Reused builtin containers should be
an explicitly frozen subset whose permitted fields and semantics are owned by
the canonical-PIR contract.

### 4.2 Latest semantic dialect versus versioned serialization dialect

**Source fact.** The official
[VHLO documentation](https://openxla.org/stablehlo/vhlo) separates the latest
StableHLO work dialect from an add-only, versioned serialization dialect. A
semantic change to an operation, type, or attribute creates a new VHLO version.
Serialization converts into VHLO and may downgrade to a requested target;
deserialization upgrades supported VHLO to the current StableHLO form.
Unsupported downgrade is discovered at the producer.

This is a particularly important precedent: stable interchange was not
obtained by freezing the ergonomic working dialect or by assuming MLIR
bytecode was enough. It required a second representation and maintained
upgrade/downgrade conversions.

**Strength.** Producers target current semantics, consumers support current
semantics, and compatibility complexity is concentrated at an explicit
serialization boundary.

**Hard-to-reverse pressure.** An add-only history grows with every semantic
change. Each published operation version and every upgrade/downgrade path
becomes maintenance work for the compatibility window. The
[compatibility RFC](https://github.com/openxla/stablehlo/blob/main/rfcs/20230623-compatibility.md)
explains why this cost is accepted: deployed ML models are long-lived and
execution environments, especially mobile ones, often cannot be updated.

**Stage 3 inference.** zkc should preserve the architectural separation but
not automatically copy per-operation VHLO versioning. A small immutable v0
semantic regime may be cheaper and clearer. Any later semantic change should
produce a new regime and an explicit semantic relation, rather than an upgrade
that silently retains `ProtocolId`.

### 4.3 Compatibility is scoped to a construction API

**Source fact.** The
[StableHLO compatibility contract](https://openxla.org/stablehlo/compatibility)
currently promises bounded backward and forward compatibility for *portable
artifacts* created through specific APIs. Pretty-printed StableHLO and raw
StableHLO-dialect bytecode are explicitly outside that promise. Unspecced
features, implementation bugs that contradict the spec, and numerical
accuracy are also outside the stated guarantee.

The same page records that current compatibility tests compare syntactically
identical reconstructed programs and calls that requirement overly onerous;
reference-implementation testing is future work.

**Strength.** The guarantee names its artifact construction, time window,
semantic authority, and exclusions rather than claiming that all parseable
bytes are portable.

**Stage 3 inference.** A zkc artifact contract must name the exact producer,
target regime, closure precondition, and compatibility relation. Round-trip
syntax is useful evidence but is neither semantic equality nor an ideal basis
for Protocol identity.

### 4.4 StableHLO transfer boundary

The transferable pattern is:

```text
specified closed semantics
  != ergonomic current work dialect
  != versioned interchange dialect
  != bytecode container
  != compatibility claim
```

The analogy ends at workload semantics. StableHLO programs are deterministic
tensor computations modulo documented latitude; zkc Protocols must model
roles, causal events, challenges, transcripts, distributions, prover
obligations, terminals, and observer-indexed behavior.

## 5. SPIR-V: validation is qualified, declarations are explicit, bytes are not identity

### 5.1 Module contract and execution environment

**Source fact.** The Khronos
[SPIR-V unified specification](https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html)
defines SPIR-V 1.6 Revision 7 as a binary intermediate language. A module
declares a major/minor version, capabilities, optional extensions, a memory
model, entry points, and execution modes. The full consumption contract is the
SPIR-V specification together with the client API's execution environment,
which may add validation rules, supported capabilities, and limits but cannot
remove universal rules.

**Strength.** Environment-sensitive validity is not hidden in a backend
implementation. Features used by a module are declared as capabilities; a
validator checks declared use, while a client may reject capabilities it does
not support.

**Stage 3 inference.** zkc should distinguish three questions that a single
`valid` flag would blur:

1. is the object structurally and semantically valid in its declared Protocol
   regime;
2. does it declare the semantic facilities it uses; and
3. does a particular consumer policy or environment support those facilities?

The third is not Protocol identity and should not be smuggled into admission
through an ambient registry.

### 5.2 Validity does not imply defined execution

**Source fact.** SPIR-V expressly separates module validity from undefined
behavior. A module is valid when it violates no statically expressed rule; a
valid module may still contain execution that becomes undefined. The
specification also separates universal validation from environment-specific
rules.

**Strength.** This prevents a structural checker from making a stronger
execution claim than it establishes.

**Stage 3 inference.** zkc's whole-Protocol admission may be stricter than
SPIR-V validity, but its judgment vocabulary should retain the same discipline:
well-formed schedule, admitted challenge interpretation, satisfied abstract
prover obligations, realized relation, and transported cryptographic property
are different claims.

### 5.3 Explicit extension and same-spelling discipline

**Source fact.** SPIR-V extensions are declared with `OpExtension` and receive
their semantics from separate specifications. Token ranges are registered so
independent vendors can extend without collision. Word counts let generic
tools skip instructions they are not required to process. The design
principles call SPIR-V “modeless”: after an execution model is selected, the
same spelling should have the same semantics; a semantic change should receive
a different spelling.

**Strength.** Explicit capability and extension declarations make a module's
feature surface inspectable, and different spelling avoids ambient mode bits
changing an instruction's internal meaning.

**Hard-to-reverse pressure.** Extension openness distributes semantic
authority across extension specifications and client environments. A generic
tool's ability to walk or skip an unknown instruction does not imply that it
can admit, transform, or preserve the module's meaning.

**Stage 3 inference.** Rich zkc authoring layers may be extensible. Exact-v0
canonical PIR should instead reject unknown meaning-bearing operations,
attributes, relation kinds, and challenge modes. Skippable content is safe
only in a separately classified non-semantic channel that cannot affect any
protected observation or identity.

### 5.4 Physical order and numeric IDs do not create semantic identity

**Source fact.** A SPIR-V module is a linear word stream with required logical
section ordering. Result IDs are numeric SSA names bounded by a header field;
the specification recommends dense low IDs. A generator identifier is present
but explicitly has no semantic effect. Within several logical sections,
instructions may still appear in more than one legal order.

The specification does not define a unique canonical module encoding.

**Stage 3 inference.** Numeric carrier IDs, source names, generator tags, and
legal instruction order must be excluded or normalized before zkc computes a
semantic identity. Occurrence identity must be defined by the Protocol model,
not inferred from whichever IDs an MLIR or binary printer assigned.

### 5.5 SPIR-V transfer boundary

Transfer explicit regime declarations, layered validation, same-spelling
semantics, and the distinction between semantic and debug/generator data. Do
not transfer open semantic extensions or environment-qualified meaning into a
closed canonical PIR.

## 6. WebAssembly: abstract semantics, non-unique bytes, and an outer interface layer

### 6.1 Abstract module versus text and binary encodings

**Source fact.** The
[WebAssembly Core specification](https://webassembly.github.io/spec/core/)
separately defines structure, validation, execution, binary format, and text
format. The
[binary conventions](https://webassembly.github.io/spec/core/binary/conventions.html)
describe bytes as an encoding of abstract syntax and explicitly state that
some abstract forms have multiple legal encodings. The
[integer encoding rules](https://webassembly.github.io/spec/core/binary/values.html)
permit bounded trailing-zero or sign-extension encodings; for example, one
integer value may have more than one valid LEB128 byte sequence.

**Strength.** Semantics are attached to decoded abstract syntax, not confused
with the convenience of a textual or binary spelling.

**Hard-to-reverse pressure.** A valid WebAssembly byte sequence is not a
unique physical representation. Hashing accepted bytes therefore identifies
an artifact occurrence, not necessarily the abstract module.

**Stage 3 inference.** zkc should either define a unique physical encoding or
state that artifact identity differs from semantic `ProtocolId`. Merely using
a deterministic encoder is insufficient if the decoder accepts alternative
encodings and downstream systems hash the input bytes.

### 6.2 Validation and semantic-free extension space

**Source fact.** Core module validation is defined over the decoded module and
produces its module type. The specification also gives an executable-style
[single-pass validation algorithm](https://webassembly.github.io/spec/core/appendix/algorithm.html)
corresponding to the declarative rules.

**Source fact.** In the
[binary module format](https://webassembly.github.io/spec/core/binary/modules.html),
custom sections are ignored by WebAssembly semantics. Even if an
implementation interprets a custom section, errors in that content or its
placement must not invalidate the module.

**Strength.** The custom-section rule creates a clean extensibility channel:
tools can carry debugging or producer data without silently modifying core
meaning.

**Stage 3 inference.** zkc can permit annotations outside canonical semantic
content only if the contract is equally strong: no annotation may affect
admission, Protocol identity, transcript construction, public wire data,
checks, claims, terminal outcomes, relation correspondence, or later
compilation. Metadata that can affect one of those is semantic and belongs in
the closed model.

### 6.3 Core imports/exports were not a language-level interface

**Source fact.** Core WebAssembly has typed imports and exports for low-level
module entities. The official
[Component Model MVP explainer](https://github.com/WebAssembly/component-model/blob/main/design/mvp/Explainer.md)
adds component and instance types, richer language-independent values, and an
explicit Canonical ABI. `lift` and `lower` wrap core functions across the
component boundary; options such as memory, allocation, string encoding, and
post-return behavior are made explicit and validated.

**Strength.** The abstract interface is separate from its concrete ABI
realization. Multiple lower-level representations can implement one typed
component-level value contract.

**Hard-to-reverse pressure.** The Component Model is an outer layer because
Core's original numeric function boundary cannot directly express the richer
cross-language interface. The official design history states that the model
merged and superseded earlier module-linking and interface-types proposals.
This illustrates how an initially sufficient low-level interface can later
require a new identity-bearing layer rather than incremental fields on the
old module.

**Stage 3 inference.** `ProtocolInterface` should remain a separate subject
from the Protocol and from any concrete wire, plan, or backend ABI. Its typed
ports, observations, and dependency on an exact `ProtocolId` should be fixed
upstream; realization-specific allocation and calling conventions belong
later. A conversion analogous to `lift`/`lower` should be named as a relation,
not treated as representation equality.

### 6.4 WebAssembly transfer boundary

Transfer the abstract-syntax/encoding split, executable validation, strict
non-semantic extension rule, and interface/ABI separation. Do not infer that
WebAssembly's module composition or deterministic execution models
multi-party Protocol schedules, transcript observations, or stochastic
challenge distributions.

## 7. zkInterface: relation interchange is narrower than Protocol semantics

### 7.1 Exact subject and boundary

**Source fact.** The ZKProof community
[zkInterface proposal](https://docs.zkproof.org/pages/standards/accepted-workshop3/proposal-zkinterface.pdf)
and [project repository](https://github.com/QED-it/zkinterface) define a
language-agnostic, message-based boundary between frontends, gadget libraries,
and proving backends. The first revision focuses on non-interactive proving of
NP relations represented as R1CS/QAP-style constraint systems. Messages carry
circuit metadata/connections, R1CS constraints, and witness assignments; the
serialization is defined with FlatBuffers and may be saved or streamed.

**Strength.** Constraint-system construction and witness assignment are not
collapsed into a compiler's internal object. Independent producers and
consumers can exchange a narrow relation artifact and process large objects as
message streams.

**Analogy limit.** The interchange subject is a low-level constraint relation
and assignment, not an interactive Protocol, Fiat--Shamir transcript
construction, observer-indexed trace, proof-system property, or admitted
Protocol capability.

**Stage 3 inference.** zkc Relations should own relation definition, instance,
witness, field regime, and artifact interpretation. Canonical PIR should refer
to exact relation subjects through typed ingress and committed-object seams;
it should not turn a constraint serialization into Protocol semantics.

### 7.2 Composition through a calling convention

**Source fact.** zkInterface supports gadgets using a procedural calling
convention. A caller and gadget exchange read-only messages. Inputs and outputs
are shared by variable IDs; local variables receive consecutive globally
unique IDs from a caller-supplied `free_variable_id`, and the gadget returns
the next unused ID. Instance reduction and witness reduction use related but
distinct message flows.

**Strength.** The design recognizes that reusable constraint construction
needs more than concatenating serialized constraints. It names connection
variables, local allocation, caller/gadget responsibilities, and two reduction
phases.

**Hard-to-reverse pressure.** Global consecutive variable allocation makes
composition order and renaming part of the procedural carrier convention.
Locality is protected by caller/gadget discipline rather than a semantic
occurrence identity embedded in the relation object. A broader relation family
would also need more than the R1CS-specific message set.

**Stage 3 inference.** zkc must model child occurrences, interface maps,
alpha-renaming, committed-object sharing, and allowed interleavings explicitly.
Global wire numbers may be generated after composition, but they cannot be the
identity of a relation variable or Protocol event. Protocol composition is not
graph union, constraint concatenation, or a transition edge.

### 7.3 Statement, witness, and proof-system boundaries

**Source fact.** zkInterface lets a backend consume the circuit description
and constraints for setup while witness messages are used for proof
generation. The project README explicitly calls the code experimental and
limits the first revision to R1CS/QAP-style non-interactive systems.

**Stage 3 inference.** This supports three separations for zkc:

- relation definition and public instance are not a witness;
- witness ingestion is not relation satisfaction; and
- backend acceptance of a constraint artifact is not a Protocol-level or
  cryptographic property claim.

## 8. Cross-case comparison

| Pressure | MLIR | StableHLO/VHLO | SPIR-V | WebAssembly | zkInterface |
|---|---|---|---|---|---|
| Semantic authority | Dialect-defined; framework supplies structure | Written language spec | Unified spec plus declared extension and client environment | Abstract Core spec; Component Model adds outer semantics | Proposal/specification for a narrow R1CS interchange |
| Schema closure | Open mixed dialects by default | Closed StableHLO portable set after legalization | Version/capability/extension qualified | Closed Core grammar; custom sections semantically ignored | Fixed message and R1CS schema in first revision |
| Validation | Dialect verifiers and target-relative conversion legality | Spec/verifier plus portable serialization checks | Universal plus environment-specific rules | Declarative rules plus validation algorithm | Consumer validation of circuit/constraints/witness |
| Physical canonicality | Not supplied by canonicalizer or generic bytecode | Portable construction is controlled, but identity is not defined as bytes | Linear binary with legal naming/order latitude | Explicitly non-unique binary encodings | Precise FlatBuffers messages, not a semantic canonical-identity contract |
| Versioning | Container plus dialect-owned version hooks | Add-only VHLO versions and bounded compatibility windows | Module version, extensions, capabilities, revisions | Spec releases and feature evolution; outer Component Model | Revision-limited experimental format |
| Interface | Generic symbols/regions, dialect-owned meaning | Function boundary for tensor programs | Entry points and environment IO | Core imports/exports; separate typed Component Model and Canonical ABI | Circuit/gadget connections and message calling convention |
| Composition | Generic nesting/symbols; semantics left to dialect | Multiple functions/calls, computation-specific | Multiple entry points/functions in one module | Module/component instantiation and typed linking | Procedural gadget calls with global variable allocation |
| Main zkc warning | Mechanism is not denotation | Stability requires an owned semantic product layer | Validity is qualified and bytes are not identity | Valid bytes need not be unique; interface may need its own layer | Relation artifact and allocation convention are not Protocol semantics |

## 9. Constraints for Stage 3 candidate architectures

Every equal-resolution Stage 3 candidate should be rejected unless it can
answer all of the following without ambient implementation state.

### 9.1 Semantic subject and closure

1. Which exact object has Protocol meaning: abstract semantic value, MLIR
   operation tree, normalized tree, or bytes?
2. What finite set of operations, types, attributes, relation references, and
   challenge interpretations is admitted in one regime?
3. Can unknown dialect operations or attributes survive decoding? If so, prove
   that they are non-semantic for every protected observation; otherwise
   reject them.
4. Which generic MLIR constructs are frozen dependencies of canonical PIR,
   and who owns their subset semantics?

### 9.2 Identity and physical encoding

1. Does `ProtocolId` identify semantic content, a regime-qualified normalized
   value, or exact artifact bytes?
2. Are SSA names, symbol spelling, ordering of unordered collections,
   locations, producer strings, debug metadata, and carrier versions excluded
   from semantic identity?
3. If multiple byte sequences decode to one object, where is physical
   canonicality established and which identity names the original artifact?
4. Can a decoder upgrade an old schema? If yes, does the result retain or
   change Protocol identity, and which named relation justifies the mapping?

### 9.3 Validation and authority

1. Which judgments correspond to decode, closed-schema membership, local
   verification, whole-Protocol admission, consumer support, and
   correspondence?
2. What exact semantic regime and dependency closure is an input to each
   judgment?
3. Can validation depend on an ambient dialect, extension, theorem, resolver,
   or consumer registry? If so, the candidate must make that dependency
   immutable and identity-bound or fail.
4. What negative outcome distinguishes unsupported version, unknown semantic
   content, invalid structure, invalid semantics, missing dependency, and
   checker failure?

### 9.4 Interfaces and composition

1. Is `ProtocolInterface` a separate identity-bearing subject, or can an ABI
   or Plan silently redefine Protocol ports and observations?
2. Are child occurrences and interface maps explicit before global carrier
   IDs or wire numbers are assigned?
3. Can repeated use of one child distinguish semantic identity from occurrence
   identity?
4. Does composition state schedule/interleaving and challenge/transcript
   effects, rather than merely nesting regions, linking symbols, or unioning
   constraints?

### 9.5 Evolution

1. What is immutable within v0: whole schema, individual constructs, or only
   spelling?
2. Does a new feature extend authoring only, extend canonical PIR, or create a
   new semantic regime?
3. What compatibility window is actually required, and which consumers make
   it rational?
4. Is backward reading a representation conversion, `ProtocolEq`, a trace
   refinement, or intentional semantic change?

## 10. Candidate-shaping hypotheses, not decisions

The evidence supports the following hypotheses for falsification in Stage 3.3.

### H1. Semantic core plus bounded carrier profile

Define Protocol meaning independently, then define canonical PIR as a total,
closed, loss-accounted representation of that meaning using a narrowly frozen
MLIR profile. MLIR supplies structure and tooling; the profile supplies closure
and physical canonicalization.

**Falsifier:** a required Protocol concept cannot be represented without
depending on ambient MLIR semantics or without duplicating an independently
owned Relations concept.

### H2. Regime identity instead of silent schema upgrade

Bind `ProtocolId` to a semantic regime and normalized semantic content. Treat
cross-regime reading as construction of a new candidate plus an explicit
relation, never as automatic retention of identity.

**Falsifier:** a meaningful compatibility requirement cannot be met without
stable identity across a representational change that is provably semantic
trivia.

### H3. One closed meaning channel plus a strictly inert annotation channel

Permit extensible tooling metadata only outside semantic content, following a
rule at least as strong as WebAssembly custom sections. Meaning-bearing
extension happens only through a new admitted regime.

**Falsifier:** a required extension must affect a protected observation while
remaining interpretable by consumers that do not know it.

### H4. Interface and occurrence before ABI and numbering

Make `ProtocolInterface` and composition occurrences semantic subjects before
MLIR SSA naming, relation variable allocation, Plan routing, or backend ABI
lowering. Generate global names only as carrier artifacts.

**Falsifier:** two distinct interface or occurrence maps always induce the
same protected observations and no later consumer needs to distinguish them.

### H5. Layered admission without a universal validator

Use domain-owned checks for canonical PIR and Relations under shared closure
and outcome rules. A small executable validator may accompany a declarative
specification, but legality, admission, correspondence, and property transport
remain distinct results.

**Falsifier:** clean-room consumers cannot decide the necessary admission
predicate without an unbounded ambient registry or a second duplicate semantic
model.

## 11. Transfers explicitly rejected

Stage 3 should not copy these precedents without new evidence:

- MLIR's open mixed-dialect state as the canonical Protocol contract;
- MLIR canonicalization as a semantic normal form or identity algorithm;
- bytecode decoder success as semantic admission;
- VHLO's per-operation add-only history before zkc has an installed-base
  compatibility requirement that justifies it;
- SPIR-V's open extension authority in exact-v0 canonical PIR;
- SPIR-V client-environment policy as part of Protocol semantic identity;
- WebAssembly's acceptance of non-unique binary encodings if exact bytes are
  used for authentication;
- Core WebAssembly's low-level import/export boundary as an adequate model for
  `ProtocolInterface`;
- zkInterface's global variable-number allocation as relation-variable or
  occurrence identity; or
- R1CS artifact composition as Protocol composition.

## 12. Primary references

### MLIR

- [MLIR Language Reference](https://mlir.llvm.org/docs/LangRef/)
- [Dialect Conversion](https://mlir.llvm.org/docs/DialectConversion/)
- [Operation Canonicalization](https://mlir.llvm.org/docs/Canonicalization/)
- [MLIR Bytecode Format](https://mlir.llvm.org/docs/BytecodeFormat/)
- [Defining Dialects](https://mlir.llvm.org/docs/DefiningDialects/)

### StableHLO and VHLO

- [StableHLO specification](https://openxla.org/stablehlo/spec)
- [VHLO dialect](https://openxla.org/stablehlo/vhlo)
- [StableHLO compatibility contract](https://openxla.org/stablehlo/compatibility)
- [StableHLO bytecode rationale](https://github.com/openxla/stablehlo/blob/main/docs/bytecode.md)
- [StableHLO compatibility RFC](https://github.com/openxla/stablehlo/blob/main/rfcs/20230623-compatibility.md)

### SPIR-V

- [SPIR-V 1.6 unified specification](https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html)
- [SPIR-V machine-readable grammar](https://registry.khronos.org/SPIR-V/specs/unified1/MachineReadableGrammar.html)

### WebAssembly

- [WebAssembly Core specification](https://webassembly.github.io/spec/core/)
- [Core binary conventions](https://webassembly.github.io/spec/core/binary/conventions.html)
- [Core binary values](https://webassembly.github.io/spec/core/binary/values.html)
- [Core binary modules](https://webassembly.github.io/spec/core/binary/modules.html)
- [Core module validation](https://webassembly.github.io/spec/core/valid/modules.html)
- [Core validation algorithm](https://webassembly.github.io/spec/core/appendix/algorithm.html)
- [Component Model MVP explainer](https://github.com/WebAssembly/component-model/blob/main/design/mvp/Explainer.md)
- [Component Model Canonical ABI](https://github.com/WebAssembly/component-model/blob/main/design/mvp/CanonicalABI.md)

### Proof and constraint interchange

- [zkInterface ZKProof community proposal](https://docs.zkproof.org/pages/standards/accepted-workshop3/proposal-zkinterface.pdf)
- [zkInterface source repository and interface definition](https://github.com/QED-it/zkinterface)
