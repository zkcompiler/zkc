# Canonical PIR carrier and lifecycle

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Target status:** Stage 3.5 durable promotion
> **Provisional owner:** `pir`
> **Authority:** This document specifies the selected target for `docs-next/`.
> It is non-normative until explicit consolidation and cutover. The current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.
> This document makes no implementation, compatibility, or migration claim.

> **K1 transition notice — 2026-08-26:** The candidate/dependency bundles and
> identity equations below retain the historical Stage 3 vocabulary. The
> exact selected substrate is [Executable Semantic Foundations](../foundation/executable-foundations.md).
> K2 must
> replace algorithm dependencies with exact portable-algorithm candidates and
> each candidate's own authenticated `RequiredModuleClosure_B`; direct
> primitive references do not become transitive closure nodes. K2 must also
> replace every legacy `H(...)` equation with an exact
> `SemanticContentId<K>` body under an authenticated prior-meta basis. This
> carrier page is not yet a K1-computable Protocol lifecycle.

> **K2 routing notice:** The language-independent Core and Protocol reconstructed
> by a future canonical carrier are now defined by
> [Interactive Core and Causal Execution](interactive-core.md) and
> [Fiat--Shamir Construction](fiat-shamir.md). This page has not yet been
> reconciled to their exact bodies and remains a pre-K2 carrier candidate; it
> cannot override either semantic definition.

## 1. Scope and invariants

This document specifies the unique physical v0 carrier for the
[Protocol semantic model](protocol-model.md), its exact physical normal form,
the language-independent algebra-to-carrier bijection, and the authority
boundary from raw material to an admitted Protocol.

The selected architecture has one meaning and one production carrier:

~~~text
language-independent Protocol algebra
       <-> one closed canonical MLIR PIR graph

raw graph
  -> structural and dependency authentication
  -> authenticated immutable candidate
  -> semantic Protocol admission
  -> opaque process-local AdmittedProtocol
~~~

The algebra defines meaning; MLIR carries it. There is no parallel canonical
Rust model, carrier-neutral runtime package, compatibility dialect, or second
Protocol representation. Other Stage 3 subjects are finite canonical
algebraic values with lossless transport profiles only.

Three predicates remain distinct:

1. **transport validity** says bytes decode and MLIR parses;
2. **canonical authentication** says the graph has the exact physical form,
   authenticated dependencies, and directly recomputed IDs; and
3. **Protocol admission** says the reconstructed semantic object satisfies
   the complete Core and interpretation laws.

No success at an earlier layer implies success at a later layer.

## 2. Exact MLIR carrier profile

### 2.1 Closed operation allowlist

Canonical PIR is one MLIR operation graph with exactly one `pir.protocol`
root. Its complete v0 semantic operation allowlist is:

~~~text
pir.protocol
pir.core
pir.dependency
pir.role
pir.port
pir.value
pir.object
pir.randomness
pir.event
pir.challenge
pir.claim
pir.reduction
pir.check
pir.failure
pir.terminal
pir.endpoint_obligation
pir.prover_obligation
pir.prover_obligation_failure
~~~

Only a separately fixed minimal allowlist of builtin scalar, array,
dictionary, and type primitives may occur. Locations are absent. No other
dialect operation, unknown attribute, symbol name, source location, comment,
author label, cache, analysis result, Interface, Plan, relation material,
proof, or provenance is legal.

Unknown constructors and fields fail closed. Rich authoring operations cannot
be retained behind an “ignored” marker, and a canonical graph cannot carry an
extension merely because an MLIR parser accepts it.

### 2.2 One-root physical normal form

The `pir.protocol` root contains one Core body and one challenge
interpretation. Root regions and operation groups occur in the field order of
the semantic `InteractiveCore` and `Protocol` products. Each group has exactly
one block. Every semantic declaration occurs exactly once in its owning group
and uses its canonical ordinal.

The physical rules are:

- positional references are typed canonical ordinals;
- there are no semantic SSA names or symbol-table lookups;
- all defaults are explicit;
- sequences retain semantic order;
- sets and maps use canonical semantic-key order and reject duplicate keys;
- all local references are in range and point to the exact declared kind;
- the claimed `ProtocolSemanticRegimeId`, `CoreId`, and `ProtocolId` are
  present at the root and directly recomputed during authentication; and
- no nonsemantic material occurs inside the graph.

SSA values may exist only where a minimal builtin carrier primitive requires
them. Their names are not semantic and alpha-renaming is the only permitted
SSA variation.

For an FS Protocol, the root stores only the exact
`TranscriptConstructionId`. `TranscriptConstruction` is a separate semantic
subject whose canonical preimage and algorithm dependency preimages are
supplied explicitly during authentication. It is never nested as a
`pir.transcript_construction` operation. Consequently the PIR graph denotes
exactly one `Protocol`, while whole-Protocol admission still closes the
external construction dependency.

### 2.3 What is not a canonical form

Textual spelling, MLIR bytecode encoding, attribute insertion order, omitted
defaults, alternative symbol names, source locations, and arbitrary metadata
are not additional canonical forms. Text and bytecode are transport encodings
outside semantic graph identity. A parser may accept transport variation, but
authentication must reconstruct and check the one physical graph normal form.

## 3. Algebra-to-carrier bijection

### 3.1 Domain

For semantic regime `R`, define:

~~~text
IdConsistentCanonicalPirGraph_R =
  physically canonical closed PIR graph whose claimed regime, CoreId,
  TranscriptConstructionId when present, and ProtocolId equal direct
  recomputation from its reconstructed Protocol
~~~

A raw graph with a wrong claimed regime or ID may be parseable and even have
the closed operation vocabulary, but it is outside this domain.

### 3.2 `Lower_R` and `Read_R`

~~~text
Lower_R : Protocol -> IdConsistentCanonicalPirGraph_R
Read_R  : IdConsistentCanonicalPirGraph_R -> Protocol

Read_R(Lower_R(P)) = P
Lower_R(Read_R(G)) = G modulo CarrierTrivia
~~~

`Lower_R` is a total structural encoding of every field and reference in the
language-independent Protocol algebra. `Read_R` is its total inverse over the
ID-consistent canonical graph domain. Neither operation consults a registry,
policy, source program, authoring order, Plan, Interface, relation subject, or
live checker.

The complete trivia relation is:

~~~text
CarrierTrivia =
    MLIR in-memory operation identity
  | SSA alpha-renaming when a builtin carrier requires names
~~~

Nothing else is quotiented. In particular, reordering a semantic sequence,
changing a default between explicit and absent, replacing a reference scheme,
or attaching unknown metadata is not trivia.

An internal diagnostic `ReadUnchecked_R` may reconstruct a tentative semantic
object from a structurally parsed graph. It has no round-trip law, identity
authority, or consumer authority. Only successful authentication establishes
`IdConsistentCanonicalPirGraph_R` and exposes `Read_R`.

## 4. Canonical authentication

### 4.1 Explicit preimages and capabilities

Authentication never treats a content ID as its own evidence. Its complete
external semantic inputs are:

~~~text
CanonicalTranscriptConstructionCandidate =
  unauthoritative canonical algebraic value of TranscriptConstruction

ExactTranscriptConstructionCandidateAndDependencyPreimages = {
  candidate: CanonicalTranscriptConstructionCandidate,
  algorithm_dependencies:
    ExactTranscriptAlgorithmDependencyPreimageBundle
}

ExactProtocolDependencyPreimageBundle = {
  core_dependencies:
    ExactMap<DependencyRef, AuthenticatedDependencyPreimageInput>,
  transcript_construction:
    None
    | ExactTranscriptConstructionCandidateAndDependencyPreimages
}

ExactCoreDependencyAuthenticationCapabilities =
  ExactMap<
    DependencyRef,
    DependencyAuthenticationCapability restricted to the exact kind,
    regime, content identity, ABI, and direct-edge declaration>

ExactProtocolDependencyAuthenticationCapabilities = {
  core: ExactCoreDependencyAuthenticationCapabilities,
  transcript:
    None | ExactTranscriptDependencyAuthenticationCapabilities
}
~~~

The preimage bundle is data, not authority. Checker implementations and live
process capabilities are the exact third input to authentication and do not
enter semantic identity.

Fresh requires no transcript-construction candidate and no transcript
capabilities. FS requires exactly one construction candidate whose recomputed
ID equals the root reference and exactly the authentication capabilities for
its algorithm dependency closure.

The Core preimage map contains every and only member of the candidate Core's
least dependency closure. The Core capability map has exactly the same keys.
Every capability is restricted to the exact dependency kind, contract regime,
content ID, ABI, and direct edges that it authenticates. Missing, extra,
wrong-kind, wrong-regime, wrong-identity, or widened authority is refused.

### 4.2 Ordered authentication operation

~~~text
AuthenticateCanonicalPir_R(
  raw,
  ExactProtocolDependencyPreimageBundle,
  ExactProtocolDependencyAuthenticationCapabilities)
  -> AuthenticatedCanonicalProtocolCandidate
~~~

The operation performs these steps in order:

1. decode the selected transport profile and parse MLIR structurally;
2. check exactly one root and the closed operation/builtin allowlist;
3. check fields, blocks, operation grouping, reference kinds and bounds,
   explicit defaults, and canonical order;
4. run `ReadUnchecked_R` to obtain an unauthoritative tentative Protocol;
5. authenticate every named Core dependency preimage and verify the declared
   least dependency closure;
6. for FS, authenticate the exact construction preimage and every algorithm
   dependency to the root's `TranscriptConstructionId`;
7. recompute the Core and Protocol identities, including the exact
   construction ID in the FS Protocol preimage; and
8. establish `IdConsistentCanonicalPirGraph_R`, then and only then expose
   `Read_R` and the immutable authenticated candidate.

Failure at any step yields no authenticated semantic candidate. Diagnostics
may retain unauthoritative parse facts but cannot expose them as an admitted
view.

Authentication establishes structural form, dependency identity and closure,
and semantic ID consistency. It does not establish `CoreAdmissible`,
`ProtocolAdmissible`, relation truth, security, source-language correctness, or
implementation conformance.

## 5. Admission and live authority

### 5.1 Cross-owner capability contract and inert bindings

Every PIR capability exported across an owner boundary conforms to the
project-wide
[`ExactSourceAuthorityBinding`](../project/analysis-and-compiler-architecture.md#23-capability-neutral-source-bindings).
PIR defines a closed family-indexed contract:

~~~text
PirCapabilityContract<Family> {
  exact exported admitted-subject/view or checked-result family,
  exact capability ABI and operand/result binding schema,
  exact permitted named consumers and typed purposes,
  exact freshness, attenuation, and authority-lifetime rules,
  declares_no_separate_owner_operation_policy = true
}

PirCapabilityContractId<Family> = H(
  "zkc/pir-capability-contract",
  Family,
  CanonicalEncode(exact PirCapabilityContract<Family>))
~~~

The last field is an authenticated affirmative contract clause, never an
omitted policy coordinate. Every exported PIR source binding therefore carries:

~~~text
OwnerDefinesNoOperationPolicy(
  exact PirCapabilityContractId<Family> and capability ABI)
~~~

The contract itself still restricts consumers and purposes, and every
transitive bound source policy remains conjunctive. A consumer must
reauthenticate the exact contract and ABI, obtain fresh PIR admission or
owner-mediated confirmation, and match the separately supplied live capability
to the complete inert binding. No contract, binding, ID, or serialized record
is authority.

An admitted Protocol, Core view, Interface, Plan, or other PIR subject/view uses
`ExactAdmittedSubjectAuthorityBinding`. Its portable semantic coordinate is the
exact subject ID, semantic/admission regime, admission basis and dependency
closure, and `PirCapabilityContractId<Family>`/ABI. This coordinate is not an
admission receipt. The admitted capability retains it, and replay reconstructs
and readmits the subject before requiring complete binding equality.
For an attenuated view, the binding's owner-origin and fact fields additionally
contain the complete concrete view contract, exact read manifest/attenuation,
source subject coordinate, named consumer, and typed purpose. These fields do
not change the underlying subject's semantic ID, but two differently attenuated
views never share an authority binding.

Every completed qualified PIR semantic result exported across an owner boundary
uses the following contract. This includes A/N relations and other explicitly
closed family outcome algebras such as Core execution:

~~~text
PirCheckedResultCoordinate<R> =
    Portable(PirCheckedResultRecordId<R>)
  | OwnerLocal(PirCheckedResultRecordRef<R>)

PirCheckedResultRecord<R> {
  exact PIR owner domain and result-family tag,
  exact operands, question, regime, and prerequisites,
  exact field-factored completed qualified result and polarity when applicable,
  exact checker contract, implementation, ABI, dependency, and read closure,
  exact qualification, assurance, and residual-trust closure,
  exact OwnerDefinesNoOperationPolicy disposition,
  exact canonical total transitive source-operation-policy closure,
  exact OwnerCapabilityRequirement
}

PirCheckedResultRecordBody<R> = {
  exact same completed checked-result fields required above,
  exact PIR owner instance and process generation,
  no PirCheckedResultRecordRef<R>
}

PirCheckedResultRecordAssociation<R>:
  (exact PIR owner instance,
   exact process generation,
   fresh PirCheckedResultRecordRef<R>)
    -> exact PirCheckedResultRecordBody<R>

PirCheckedResultRecordId<R> = H(
  "zkc/pir-checked-result",
  R,
  CanonicalEncode(exact PirCheckedResultRecord<R>))
~~~

The portable branch is selected only when every identity-bearing preimage is
portable and the exact capability contract permits the named retention and
consumer purpose. Otherwise PIR first constructs the complete local record
body, independently allocates a fresh typed reference in the collision-free
domain scoped by the exact PIR owner instance, process generation, and result
family, and atomically installs exactly one immutable association from that
reference to that body before exposing `OwnerLocal(the fresh reference)` as
the result coordinate. The body does not select or contain its reference, and
the reference is not derived from the body. An owner-local lookup is valid
only in the identical owner-instance/process-generation scope and must recover
a body exactly field-equal to the one retained by the checked-result binding;
absence or any mismatch fails closed.

The reference is an opaque typed local name, not a pointer, address, token,
receipt, capability, or authority. Neither the body nor the association
contains or derives live authority. Owner reset, process-generation change,
or process crossing invalidates the reference, its retained association, and
the corresponding live capability; the local coordinate is the fresh
reference itself, never the body or association. The
`OwnerCapabilityRequirement` contains the exact
capability-contract identity, ABI, operand/result binding schema, and
freshness/lifetime requirements, never a capability token or occurrence
identity. The owner creates the inert binding as part of the same completed
operation that mints the live capability, and the capability retains the exact
binding. U/C/R/M/F creates neither. Portable replay reruns the source check,
recreates the complete record, and requires exact binding equality before
minting fresh authority; an owner-local result has no exact cold replay.

### 5.2 Separate checker authority

~~~text
ExactProtocolAdmissionCheckerCapabilities = {
  core: ExactCoreAdmissionCheckerCapabilities,
  transcript:
    None | ExactTranscriptLawCheckerCapabilities
}

AdmitProtocol(
  AuthenticatedCanonicalProtocolCandidate,
  retained exact Protocol dependency views,
  exact ExactSourceAuthorityBinding for every authority-bearing admitted or
    dependency view, with separately supplied fresh capabilities,
  CompositionContextAuthority,
  ExactProtocolAdmissionCheckerCapabilities)
  -> ProtocolAdmissionAttemptOutcome
~~~

`AdmitProtocol` runs the complete semantic predicates in
[Protocol semantic model](protocol-model.md). It internally mints a
transaction-scoped `CoreAdmissionWitness`. For FS, it then admits the retained
authenticated construction by invoking `AdmitTranscriptConstruction` with
that witness, the exact context authority, retained algorithm dependency
views, and an identity-matched transcript-law checker. It finally checks
`ProtocolAdmissible` and discards the witness.

Before either completed outcome, admission matches every authority-bearing
view to its exact source binding and separately supplied fresh capability,
freshly validates every bound policy or explicit no-policy owner contract for
the named admission purpose, and constructs the canonical total transitive
source-policy closure. The admitted-subject or checked-non-admission binding
retains that complete closure and every exact `OwnerCapabilityRequirement`.

Fresh requires `transcript = None`. FS requires exactly the capability for its
referenced construction. Missing, extra, wrong-construction, or widened
checker capabilities are refused. Checker identity and live capability do not
enter `ProtocolId` and are not retained as executable ambient authority.

Standalone Fresh and FS admission use `NoCompositionContext`. A composed FS
construction requires matching scoped formation or affirmative checked
composition authority. Callers cannot supply provisional occurrence maps,
challenge maps, transcript prefixes, failure maps, or identity claims; the
owning construction and admission operations recompute them.

Success constructs the exact admitted-subject source binding and mints an
opaque immutable process-local `AdmittedProtocol` that retains it. The
capability has no serialized form and no independent semantic identity.
`CoreAdmissionWitness`
cannot escape the admission transaction. An `AdmittedCoreView` can be
attenuated from the admitted Protocol but cannot assert an interpretation or
widen back to Protocol authority.

### 5.3 Qualified failures

Boundary operations preserve distinct result classes when applicable:

~~~text
Affirmative
Negative(reason, retained_facts)
Unsupported(exact unsupported construct or question)
CannotAnswer(missing named semantic input or basis)
Refused(missing authority or prohibited invocation)
Malformed(exact framing or structural defect)
CheckerFailure(operational failure with no semantic conclusion)
~~~

Malformed transport or carrier structure is not a negative semantic
admission judgment. Missing authority is refusal. An operational checker
failure yields no conclusion. The exact admission operation returns:

~~~text
ProtocolAdmissionAttemptOutcome =
    CompletedAdmitted(
      exact ExactAdmittedSubjectAuthorityBinding,
      fresh AdmittedProtocol)
  | CompletedNonAdmission(
      exact completed field-factored refutation of the total ProtocolAdmissible
        predicate over the authenticated candidate,
      exact ExactCheckedResultAuthorityBinding<PIR, ProtocolNonAdmission>,
      fresh CheckedProtocolNonAdmission)
  | Unsupported(exact unsupported regime or construct)
  | CannotAnswer(exact missing semantic input or complete decision basis)
  | Refused(exact missing authority or prohibited invocation)
  | Malformed(exact framing or structural defect)
  | CheckerFailure(exact failed operational boundary)
~~~

`CompletedNonAdmission` is available only when the authenticated candidate and
all required inputs are well formed, the exact authenticated target admission
regime defines a total
decidable `ProtocolAdmissible` predicate at this boundary, and the complete
checker establishes its exact semantic negative. Its checked-result binding
uses the exact `PirCheckedResultCoordinate<ProtocolNonAdmission>` selected by
the common portable-or-owner-local rule and retains the candidate, regime,
admission basis and dependencies, exact violated laws and unaffected facts,
checker, assurance/trust, total source-policy closure, and
`PirCapabilityContractId<ProtocolNonAdmission>`/ABI. A parse
failure, missing dependency, unsupported rule, refusal, timeout, or checker
failure never becomes non-admission. Only `CompletedAdmitted` mints
`AdmittedProtocol`; only `CompletedNonAdmission` mints
`CheckedProtocolNonAdmission`. Compiler may use the latter as a conclusive
exclusion fact only with the exact checked-result binding and fresh capability.

## 6. Authoring normalization and pre-erasure audit

### 6.1 Mandatory front-end contract

Rich MLIR authoring, import, synthesis, and source languages remain outside
canonical PIR. Their mandatory boundary is:

~~~text
NormalizeAuthoring(
  AuthoringUnit,
  exact resolved read-closure snapshot,
  AuthoringNormalizerContract,
  ProtocolSemanticRegime)
  -> UnauthoritativeNormalizationBundle<
       CanonicalProtocolCandidate,
       InterfaceCandidate*,
       ProverPlanCandidate*,
       NormalizationAudit<ProtocolAuthoring>>
~~~

`AuthoringNormalizerContract` names one language or profile, its finite
declared syntax quotient, every pre-erasure check, the complete mapping into
canonical Core constructs, and its exact immutable dependency closure. The
operation is deterministic over those named inputs but remains an
unauthoritative producer. It does not authenticate or admit any output.

Two authoring inputs may normalize to the same candidate only through the
contract's finite declared quotient and identical resolved semantics. Unknown
distinctions and changes to protected observations are refused.

### 6.2 Information-loss ledger

Every authoring distinction has exactly one checked disposition:

| Authoring distinction | Required pre-erasure work | Canonical destination |
|---|---|---|
| partial or unspecified order | schedule selection and ambiguity checks | one total `schedule` |
| macros, modules, synthesis requests | elaboration and termination checks | elaborated Core nodes only |
| human and source names | duplicate and binding checks | Interface candidate, source map, or erased diagnostic |
| implicit defaults | default-selection check | explicit canonical field |
| imported symbols | exact resolution-closure check | typed dependency ID and ABI |
| relation descriptions | binding classification | separate Relations candidates or opaque Core declarations |
| prover construction routes | semantic-change classification | separate Plan candidate or Protocol behavior |
| source locations and provenance | diagnostic/provenance capture | nonsemantic side output |
| order claimed observer-inert | proof or exact check before erasure | canonical semantic-key order |
| protected effect or observation | never erased | explicit event, edge, codec, failure, or terminal field |

`NormalizationAudit` records each distinction as retained in Protocol,
extracted into a typed satellite or side output, proved quotient-neutral under
the named contract, or rejected before erasure. The normalizer may emit
several separately typed outputs; success of one neither authenticates nor
admits another.

Admission of a directly supplied canonical graph establishes only the
canonical Protocol subject. It cannot retroactively establish source
well-formedness, provenance, macro expansion, resolution closure, or
information preservation for an absent authoring input.

## 7. Persistence, reopening, and cold replay

### 7.1 Authority never serializes

Official semantic persistence is admission-gated, but persisted bytes remain
raw material. A canonical graph, semantic ID, digest, signature, provenance
record, serialized admission marker, or prior checker result is never a live
capability.

After serialization, FFI, mutation, reopening, or a process boundary:

~~~text
persisted transport
  -> decode and parse
  -> reauthenticate exact dependency preimages with fresh live authority
  -> recompute semantic IDs
  -> rerun Core and Protocol admission with fresh exact checker authority
  -> mint a new process-local AdmittedProtocol
~~~

Workbench caches and proposal packages are unmistakably unauthoritative.
Reopening creates an independent mutable authoring branch and inherits no
output authority. A later canonical candidate must traverse normalization,
authentication, and admission again.

A durable checked-result record is justified only for a named independent
consumer and binds every subject, semantic regime, operation input, checker
identity, qualified outcome, and stated residual trust. Its bytes still carry
no live checked-result or Protocol capability.

### 7.2 Cold Fresh and standalone FS replay

Fresh replay authenticates the Core closure, checks Core and Fresh Protocol
admission, and mints the new Protocol capability.

Standalone FS replay is acyclic despite the Core/construction dependency:

~~~text
authenticate canonical Protocol graph and Core dependencies
  -> check CoreAdmissible
  -> mint transaction-scoped CoreAdmissionWitness
  -> authenticate TranscriptConstruction and algorithm closure
  -> admit construction against witness and NoCompositionContext
  -> check FS Protocol admission and all IDs
  -> mint AdmittedProtocol
  -> discard CoreAdmissionWitness
~~~

The PIR root's `TranscriptConstructionId` locates and binds the construction;
it does not authenticate or admit the construction by itself.

### 7.3 Cold composed replay

A construction with composed context cannot use the standalone path. Replay
must recover exact admitted child Protocol views and the authenticated
composition spec, reconstruct and recheck the target Core, compare it with the
persisted canonical candidate, and mint one fresh same-invocation
`ScopedCompositionFormationAuthority`. It then authenticates and admits the
construction and enclosing Protocol in that closed transaction and reruns
composition finalization. Only an affirmative checked-composition capability
minted after that finalization may authorize later post-formation reuse; it
cannot bootstrap the replay transaction that produces it.

A serialized `CoreComposition` record is not a live
`CheckedCoreComposition`. Child IDs, target IDs, or old result bytes cannot
replace the current admitted child views, reconstruction, or identity-matched
checker authority. The exact semantic transaction is specified by
[Fiat--Shamir and Core composition](fiat-shamir-and-composition.md); its
cross-domain ownership is governed by the
[transition and bridge architecture](../project/transition-and-bridge-architecture.md).

## 8. Residual trust and nonclaims

### 8.1 Residual trust boundary

This specification makes the trusted inputs explicit rather than eliminating
them. A conforming deployment still relies on:

- the concrete collision-resistant hash and byte grammar later selected for
  the structurally fixed identity preimages;
- correctness of transport decoders and the MLIR parser at the boundary, while
  treating their output as unauthoritative until checks complete;
- correctness and identity matching of dependency authentication, admission,
  and execution capabilities;
- faithful evaluation of regime-owned closed finite terms;
- authenticated preimages and ABIs for content-addressed contracts;
- retention of exact immutable dependency views through each operation; and
- correct capability confinement across process and serialization boundaries.

Directly recomputable structural facts should not be replaced by producer
claims or universal registries. A heuristic producer may propose material,
but the owning checker must independently recompute every executable
predicate. Theorem-backed conclusions remain separate relations with their
own assumptions and residual trust.

### 8.2 Clean nonclaims

Canonical form, authentication, normalization, or Protocol admission does not
by itself establish:

- conformance of the current codebase or any particular MLIR dialect
  implementation;
- source-language well-formedness or information preservation without the
  exact authoring input, normalizer contract, resolved closure, and audit;
- provenance, authorship, review, signature validity, or production readiness;
- relation truth, satisfiability, or witness validity;
- soundness, knowledge soundness, completeness, zero knowledge, or
  Fiat--Shamir security;
- compiler transformation preservation, optimization, or target selection;
- Interface preservation, Plan realization, OIR projection, endpoint support,
  or concrete runtime invocation correctness;
- correctness of an external randomness producer beyond a checked explicit
  replay transition;
- compatibility across semantic regimes, transport profiles, MLIR versions,
  or earlier artifact formats; or
- a universal authoring IR, universal fact database, or portable
  carrier-neutral Protocol package.

Those conclusions belong to separately admitted subjects and checked
relations. The [PIR domain index](README.md) and
[Protocol IR architecture](../project/protocol-ir-architecture.md) route those
owners without weakening this carrier boundary.
