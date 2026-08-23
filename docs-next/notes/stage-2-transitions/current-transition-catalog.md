# Current transition catalog

> **Document kind:** Temporary Stage 2 reconstruction dossier
> **Document state:** Observational baseline, 2026-08-22
> **Authority:** None. This page records what the current specification,
> implementation, and tests appear to say. It does not admit a transition,
> resolve a conflict, select a target design, or authorize implementation work.
> **Scope:** Every transition named by the
> [Stage 2 Transition and Bridge Charter](../stage-2-transition-and-bridge-charter.md),
> reconstructed from the current `docs/` corpus first and implementation and
> tests second.
> **Disposition:** Replace with reviewed target contracts and a
> current-to-target gap map, then delete with the temporary Stage 2 package.

## 1. Reading discipline

This catalog uses five evidence labels:

- **Observed -- normative** means an individual document under `docs/spec/`
  defines the semantic contract. Section references are exact owners, not
  merely related reading.
- **Observed -- implementation** means a current type, function, tool, or test
  corresponds to part of the contract. It is evidence of the checkout, not a
  second source of semantics.
- **Inference** means the conclusion follows from named inputs, outputs, or
  reads but is not stated as such by one owner.
- **Conflict** means two current authorities, or an authority and its claimed
  correspondence implementation, expose different contracts. This dossier
  does not silently choose one.
- **Non-claim** names a tempting conclusion that neither the transition nor
  its evidence establishes.

The authority order is the one in `docs/README.md` and
`docs/spec/overview.md`: individual specifications own intended semantics;
`docs/status.md` owns current implementation claims; `docs/architecture.md`
describes non-normative target roles; code and tests are correspondence
evidence. Reserved and architecture-only boundaries are cataloged because the
charter names them, but their presence here is not a support claim.

**Conflict -- documentation map.** `docs/spec/relations.md` declares itself
canonical for the relation domain and `docs/README.md` includes it in the
normative corpus, but the normative-document table in
`docs/spec/overview.md` omits it. This catalog treats the document's own status
and the top-level map as sufficient to identify it as the current owner, while
recording the overview omission rather than normalizing it away.

The selected Stage 1 vocabulary is not projected backward onto the current
implementation. In particular, the current APIs have no explicit
`SemanticRegime`, separately identified `ProtocolInterface`, or separately
identified `ProverPlan`. Where current transitions instead depend on an MLIR
carrier, a retained `ProtocolEnvironment`, author labels, or embedded
construction routes, this page records that dependency literally.

## 2. Current spine at a glance

```text
text or family description
  -> raw pir.protocol proposal
  -> SealEngine + ProtocolEnvironment
  -> raw pir.sealed carrying ProtocolId
  -> bytecode persistence
  -> DecodedPirArtifact                (transport/structure/ID authority only)
  -> AdmittedPirArtifact               (seal recheck under retained environment)
       |-> SealedSoundnessView / proof-read view
       |-> conditional DerivationResult / portable witness
       |-> ProjectedOirArtifact         (new OIR identity, source PIR cited)
       `-> reopen clone -> raw pir.protocol -> transform/link -> seal again

OIR + execution profile -> direct in-process invocation
OIR JSON + emitter binding + runtime path -> generated Rust crate

relation contract + admitted PIR + optional relation bytes
  -> current correspondence report

deployment -> bound invocation -> full run record -> appraisal -> reliance
  = not a current end-to-end path; deployment, appraisal, and reliance are
    target-only, while the full record is normative but not implemented
```

The important authority discontinuities are:

1. `pir.sealed` is an identified carrier, not by its C++ type alone an opaque
   admitted capability.
2. Persistence preserves content identity but ends process-local capability
   continuity.
3. Decode authenticates transport, structure, and identity; admission adds the
   environment-backed seal judgment.
4. A mutable or serialized derivative is raw at its next semantic boundary.
5. OIR mints a different identity and cites the PIR identity as source; it does
   not inherit PIR admission by equality of ids.
6. Current generated code is an operational emission product, not an admitted
   instance of the reserved general `oir-realize` contract.

## 3. Whole-catalog classification

| # | Transition | Current state | Successful relation or result | Exact current owner |
|---:|---|---|---|---|
| 1 | Author or import | Partial operational proposal production; no standalone normative transition | Input text or a family description produces untrusted Open PIR, sometimes with a generated vocabulary | Carrier grammar and container verification: `docs/spec/carrier.md` §§1--5; target authoring role: `docs/architecture.md` §5; implementation status: `docs/status.md` |
| 2 | Resolve for seal | Normative seal-internal phase and implemented; no public result type | Cited symbolic references are resolved to exact content digests and a sealed vocabulary table | `docs/spec/kernel.md` §§7--8; `docs/spec/boundaries.md` §1; `docs/spec/carrier.md` §7 |
| 3 | Seal | Normative and implemented | Open protocol formation plus closure judgments; mints Protocol identity | `docs/spec/kernel.md` §§7--8; `docs/spec/boundaries.md` §1 |
| 4 | Persist | Normative carrier lifecycle and implemented | Representation of the same sealed subject as MLIR bytecode | `docs/spec/carrier.md` §§6, 9 |
| 5 | Decode | Normative and implemented | Bytecode interpretation plus transport, structure, and identity authentication | `docs/spec/boundaries.md` §0 and signature; `docs/spec/carrier.md` §§5, 6, 9 |
| 6 | Admit | Normative and implemented | Re-establishes the seal judgment under one environment and mints an immutable process-local capability | `docs/spec/boundaries.md` §0 and signature; `docs/spec/carrier.md` §§5--7 |
| 7 | Derive consumer view | Normative views principle with purpose-specific implementations | Recomputable, source-bound structural view; no new semantic truth | `docs/spec/kernel.md` §11; each consuming spec owns its additional view judgment |
| 8 | Reopen and discard authority | Normative capability rule; implemented as an internal compiler helper | Immutable admitted source is cloned into a new unauthoritative Open PIR proposal | `docs/spec/boundaries.md` §0; `docs/spec/carrier.md` §6; compiler transform ownership in `docs/spec/compiler.md` |
| 9 | Static link | Normative and implemented for current Open PIR | Two open components become one newly checked Open PIR proposal | `docs/spec/boundaries.md` §3; kernel composition rules in `docs/spec/kernel.md` |
| 10 | Checked Protocol transform | Normative in-memory core; one bounded provider implemented | A family-defined, replay-checked predecessor/successor relation plus claim correspondence | `docs/spec/compiler.md` §§3--7, 12 |
| 11 | Reseal and authenticate successor | Normative composition of kernel and compiler boundaries; implemented inside the PIR provider/core | Mutable candidate becomes a newly sealed, admitted, compiler-authenticated successor | Seal/admit owners plus `docs/spec/compiler.md` §§4.1, 5.2, 6 |
| 12 | Relation-interface ingress | No current pre-seal bridge; architecture-only target role | No admitted current result; closest objects are opaque PIR anchors and a separately loaded post-seal `RelationContract` | `docs/spec/relations.md` says relation compilation is external; target in `docs/architecture.md` §§3, 5 |
| 13 | Post-seal relation correspondence | Normative and implemented, with an outcome-contract conflict | Artifact/contract/optional-byte correspondence report separating computed, cross-checked, disagreed, and asserted facts | `docs/spec/relations.md` §§1--6 |
| 14 | Property analysis | Normative for typed soundness and completeness; implemented for selected rules | Explicit plan derives a conditional notion-indexed `SecurityJudgment` or refuses | `docs/spec/soundness.md` §§1--9 |
| 15 | OIR projection | Normative and implemented for verifier and prover-skeleton | Source-relative `COV_realized`, endpoint program, and new OIR identity | `docs/spec/boundaries.md` §2; `docs/spec/endpoints.md` §§1--3, 6; `docs/spec/carrier.md` §6.1 |
| 16 | Supplier binding | Normative as execution-profile compatibility; operational as an emitter input; no standalone admitted subject | OIR requirements are matched to one closed supplier selection | `docs/spec/endpoints.md` §4; emission role in `docs/architecture.md`; implemented scope in `emit/` |
| 17 | Endpoint realization | General normative boundary reserved; narrow Rust emission operational | Canonical OIR plus suppliers becomes a standalone Rust endpoint crate | Reserved `docs/spec/boundaries.md` §6; operational emission role in `docs/architecture.md` §§3, 5, 8 |
| 18 | Deploy | Architecture-only and not built | Intended physical resolution of emitted roles to resources/topology/policy | `docs/architecture.md` §§4--8, 12; `docs/status.md` |
| 19 | Invoke | Normative direct endpoint execution and partially implemented; general invocation binding absent | Verifier verdict or prover bytes under one execution profile | `docs/spec/endpoints.md` §§4, 6.3; broader target in `docs/architecture.md` §§5, 7 |
| 20 | Record or attribute observation | Normative minimum for attributable endpoint runs; no full first-class current record | Intended executor-attributed observation of one run | `docs/spec/endpoints.md` §§4, 6.3; run role in `docs/architecture.md` §§4, 10 |
| 21 | Appraise evidence | Architecture-only generic role; not built | Intended policy-qualified assessment of typed evidence about exact subjects or transitions | `docs/architecture.md` §§10--12 |
| 22 | Make use-specific reliance decision | Architecture-only admission/reliance role; not built | Intended scoped permission or denial for one consumer use | `docs/architecture.md` §§5, 10--12; `docs/status.md` evidence-admission row |

## 4. Lifecycle and authentication transitions

### 4.1 Author or import

| Field | Current reconstruction |
|---|---|
| Classification and owner | Proposal production. The current carrier owns what an Open PIR container can represent and locally verify; no specification owns a general source-language import or authoring judgment. `docs/architecture.md` describes authoring as a target boundary, and `docs/status.md` calls support partial. |
| Source and authority | Hand-written textual MLIR, or a closed FRI instance description consumed by the family generator. Both are caller material. No input carries Protocol authority. There is no current relation-source importer. |
| Result and authority | Raw `pir.protocol` Open PIR; `zkc-family` additionally emits a generated `ProtocolVocabulary`. Parsing or generator self-check establishes representation shape only. The output remains an unjudged proposal until seal. |
| Reads and ambient inputs | Plain parsing reads dialect definitions and MLIR parser behavior. FRI generation reads its compiled template and the explicit JSON description, then self-checks the emitted vocabulary with the real loader and the spine with the real parser. No `ProtocolEnvironment` is applied to the resulting protocol here. |
| Identity effect | Open PIR has no admitted artifact identity. `zkc-translate --id` can compute/mint an id from raw carrier state, but `docs/spec/boundaries.md` §0 explicitly classifies raw identity minting as authoring diagnostics that confer no acceptance. |
| Outcomes and effects | Malformed text or description, unsupported family/parameter values, internal template failure, and I/O failure are distinct from seal inadmissibility. The ordinary authoring path has no semantic success capability. |
| Capability and replay | Raw, mutable MLIR can be copied or serialized without authority. Independent use must parse and then seal/admit at the relevant boundary. |
| Correspondence evidence | `tools/zkc-family/zkc-family.cpp`; `include/zkc/Family/FriFamily.h`; `lib/Family/FriFamily.cpp`; low-level `pir.protocol` definitions under `include/zkc/Dialect/Pir/`; `test/Family/fri-family.test`; `test/Family/generator-output.test`. |

**Non-claim.** Generator validation does not establish that its template is a
correct protocol construction, that a relation is true, or that the generated
Open PIR will seal under an arbitrary environment.

### 4.2 Resolve for seal

| Field | Current reconstruction |
|---|---|
| Classification and owner | Interpretation/resolution internal to seal, not a separately callable or serializable transition. Kernel §§7--8 and Boundaries §1 own the cited-closure rule; Carrier §7 owns registry admission. |
| Source and authority | Raw Open PIR plus one immutable `ProtocolEnvironment`, containing `ProtocolVocabulary` and optional `ConstructionProfileRegistry`. Symbolic operation ids and construction-route contract ids are not authority before resolution. |
| Result and authority | A resolved `vocab` table of exact `(section, id, content digest)` entries for cited claim/value profiles, check/reduction/hole contracts, terminal rules, and consumed sponge/codecs. In code this table exists as a seal-internal value and then as identified content of the sealed result; there is no `ResolvedSealCandidate` type or capability. |
| Reads and closure | The resolver can search the complete supplied environment, but only the transitive cited closure is permitted to affect the artifact. RelationContract bodies, theorem/signature declarations, relation payloads, SRS material, supplier implementations, and relying policy are not seal inputs. |
| Identity effect | The resolved cited table enters Protocol canonical content. A changed cited preimage changes ProtocolId; an uncited environment entry is specified not to. No separate resolver/configuration identity is minted. |
| Outcomes | Missing ids, invalid preimages, cross-section incompatibility, absent construction profiles, or a cited digest without admitted content cause the enclosing seal to refuse. There is no successful partial table exposed to a caller. |
| Capability and replay | None independently. Re-admission reconstructs and checks the cited closure again under a supplied environment. |
| Correspondence evidence | `registry::ProtocolEnvironment` in `include/zkc/Registry/ProtocolEnvironment.h`; `buildResolvedVocabulary` and `resolveSection` in `lib/Semantics/SealEngine.cpp`; registry loaders under `lib/Registry/`; seal and registry tests including `test/Transforms/pir-seal-no-vocabulary.mlir` and `test/Artifact/fail-closed.test`. |

**Inference.** The current model has an exact identified cited closure but no
stable identity for the broader resolver or semantic regime. An admitted
capability retains the broader environment for later consumers, so “same
ProtocolId” is not by itself a complete capability-comparability statement.

### 4.3 Seal

| Field | Current reconstruction |
|---|---|
| Classification and owner | Authentication/admission of protocol structure. `docs/spec/kernel.md` §7 defines the seal conjunction and §8 identity; `docs/spec/boundaries.md` §1 owns the boundary contract. |
| Source and authority | One raw `pir.protocol`, selected construction profile and `SealPolicy`, and one environment used consistently for every vocabulary-dependent judgment. |
| Result and claimed relation | One immutable-in-meaning `pir.sealed` whose body satisfies `WF`, `LIN`, `BIND`, `COV_obl`, `ReductionClosureOK`, and `TerminalClosureOK`; plus recomputable tables/obligations as views. The relation is structural formation and closure, not cryptographic security. |
| Reads | Full Open PIR content, including policy, construction routes, semantic refs, and authoring selectors used to resolve canonical positions; exact cited protocol/construction vocabulary closure. It deliberately does not read a `RelationContract`, theorem catalog, predicate runtime, backend, execution profile, evidence, or relying policy. |
| Identity effect | Mints ProtocolId as tagged SHA-256 over canonical protocol content, selected policy/profile, and cited closure. Stored id, evidence, theorem choice, backend names, calibration, and derived judgments are excluded. Id-stable author-label renaming is part of the equivalence rule. |
| Outcomes and side effects | Normatively fail closed: diagnostics only, no partial sealed artifact. `SealEngine::seal` leaves the source intact on failure; on success it constructs and verifies `pir.sealed` and erases the source `pir.protocol`. |
| Capability | The returned `pir::SealedOp` is an identified result of this invocation, but its public C++ type remains a mutable/raw MLIR handle. Cross-boundary reuse requires snapshot/decode/admission or an opaque capability; the raw op type is not itself unforgeable authority. |
| Correspondence evidence | `semantics::SealEngine::{seal,recheck}` in `include/zkc/Semantics/SealEngine.h` and `lib/Semantics/SealEngine.cpp`; `pir::runSealBattery`; `semantics::ConstructionGraph`; `tools/zkc-seal/zkc-seal.cpp`; `test/Transforms/pir-seal*.mlir`; `test/Transforms/seal-engine-parity.test`; `test/lib/TestSealEngine.cpp`. |

**Non-claims.** Seal establishes predicate identity rather than predicate
execution. It does not establish relation satisfaction, theorem truth,
soundness, completeness, zero knowledge, endpoint realization, or backend
behavior.

### 4.4 Persist

| Field | Current reconstruction |
|---|---|
| Classification and owner | Representation of one sealed subject. Carrier §§6 and 9 own canonical identity and bytecode lifecycle. |
| Source and authority | A raw `pir::SealedOp` produced or otherwise supplied in-process. The writer does not accept a cached “valid” bit; it recomputes identity before writing. |
| Result and claimed relation | MLIR bytecode containing exactly one sealed protocol, normally named `<id>.mlirbc`, with a producer marker and dialect version blob. The claimed relation is representation of the same identified sealed content, not continued capability possession. |
| Reads | Sealed operation state, canonical encoder, bytecode writer, producer string, destination path. No protocol registry or theorem environment is read. |
| Identity effect | Preserves ProtocolId; mints no persistence identity. Bytecode bytes are not the Protocol identity preimage and are not a stable cross-version surface. |
| Outcomes and side effects | Identity recomputation or mismatch refuses before bytes are accepted as an artifact. `zkc-seal` writes every candidate output before calling `keep()` on any, so a module-level semantic/write failure leaves no kept artifact set, although creating the output directory is an operational side effect. |
| Capability | Serialization ends opaque in-process capability continuity. The byte stream is raw input to the next decoder. |
| Correspondence evidence | `artifact::writeArtifact` in `include/zkc/Artifact/Artifact.h` and `lib/Artifact/Artifact.cpp`; `tools/zkc-seal/zkc-seal.cpp`; `test/Artifact/roundtrip.mlir`; `test/Artifact/lifecycle.mlir`. |

### 4.5 Decode

| Field | Current reconstruction |
|---|---|
| Classification and owner | Representation interpretation plus transport/structure/identity authentication. The consumer rule is `docs/spec/boundaries.md` §0; Carrier §§5, 6, and 9 own the representation. |
| Source and authority | Raw artifact bytes and optional caller-supplied expected ProtocolId. Neither file name nor producer marker is semantic authority. |
| Result and claimed relation | `DecodedPirArtifact`, an immutable, copy-only, private-storage handle to one verified `pir.sealed`. It establishes that the bytes decoded to one structurally verifying carrier whose recomputed id equals the stored and optional expected id. It does not establish registry-backed seal admission. |
| Reads | Bytecode header and producer marker, PIR dialect version, parser/structural verifier, canonical encoder, stored id, optional expected id. No `ProtocolEnvironment` is available. |
| Identity effect | Preserves and reauthenticates ProtocolId; mints no new identity. |
| Outcomes | Unreadable/non-bytecode input, rejected producer/version shape, malformed carrier, not-exactly-one sealed op, structural verification failure, stored/computed mismatch, or expected/computed mismatch all refuse. No repair or upgrade occurs. |
| Capability | Gains a narrow decoded capability. Copies share private immutable storage. It authorizes printing/identity inspection and admission input, not semantic consumers requiring the seal judgment. |
| Correspondence evidence | `artifact::{loadArtifact,snapshotArtifact}` and `DecodedPirArtifact` in `include/zkc/Artifact/Artifact.h`; `decodeArtifact` in `lib/Artifact/Artifact.cpp`; `tools/zkc-artifact/zkc-artifact.cpp`; `test/Artifact/fail-closed.test`; `test/Artifact/roundtrip.mlir`; `test/lib/TestArtifactLifecycle.cpp`. |

### 4.6 Admit

| Field | Current reconstruction |
|---|---|
| Classification and owner | Authentication/admission under semantic authorities. Boundaries §0 and the `admit` signature own the consumer contract; Carrier §6 owns capability behavior. |
| Source and authority | `DecodedPirArtifact` plus one immutable `ProtocolEnvironment`. Decode authority is necessary but insufficient. |
| Result and claimed relation | `AdmittedPirArtifact`, copy-only private storage binding the exact decoded subject to the exact environment used for a successful `SealEngine::recheck`. This is the main current process-local Protocol consumer capability. |
| Reads and closure | Structural sealed carrier, identity, exact cited vocabulary/preimage closure, route graph, and the supplied resolver. Normatively only cited entries may affect the judgment, although the returned capability retains the complete environment for later purpose-specific consumers. |
| Identity effect | ProtocolId is preserved and rechecked. No AdmissionId, AdmissionBasisId, resolver id, or explicit SemanticRegimeId is minted. |
| Outcomes | Any seal-battery, construction-graph, cited-preimage, ABI, or identity failure returns an admission refusal; no weaker admitted handle is produced. |
| Capability and replay | Gains an immutable opaque capability. Copying preserves the same subject/environment authority. Printing, serializing, or producing a mutable clone yields raw input for any later semantic boundary; a new process must decode and admit again. |
| Correspondence evidence | `artifact::{admitArtifact,loadAndAdmitArtifact}` and `AdmittedPirArtifact` in `include/zkc/Artifact/Artifact.h`; `lib/Artifact/Artifact.cpp`; `registry::ProtocolEnvironment`; lifecycle and projection tests under `test/Artifact/`. |

**Inference.** Because no explicit regime or admission-basis identity exists,
the safe comparison key for current capabilities is not merely ProtocolId.
The capability's retained environment and the exact consuming procedure also
matter, even where conformance should make uncited environment differences
observationally irrelevant.

### 4.7 Derive consumer view

| Field | Current reconstruction |
|---|---|
| Classification and owner | Derivation of a purpose-specific view. Kernel §11 says tables are definitions, not new truth; each downstream owner defines the additional facts it is permitted to extract. |
| Source and authority | An `AdmittedPirArtifact` capability. Current public examples are `buildSealedSoundnessView` and the compiler's proof-read extraction. |
| Result and claimed relation | `SealedSoundnessView`, or ordered `VerifierProofReadObservation` rows. The view is owned and source-bound; the soundness view includes `artifactId`, canonical claim/event sites, pinned contract facts, statement labels, material grounding, and construction facts. It contains no MLIR pointer or registry pointer. |
| Reads | The immutable admitted carrier and, while adapting, its retained environment. The proof-read view resolves exact codec ids/digests. The soundness adapter reads canonical positions and pinned vocabulary but also copies selected author labels used by the current statement/relation surfaces. |
| Identity effect | No new semantic identity. The ProtocolId is carried as the view's subject key; exact codec/rule refs are cited. A view cannot be substituted for another artifact even when its shape happens to match. |
| Outcomes | Adapter-specific malformed/inconsistent facts refuse. There is no successful “unknown” view and no semantic property judgment at this step. |
| Capability | The construction function is the trusted bridge from the opaque admitted capability. Returned views are plain owned values accepted by low-level trusted-input evaluators; serialization does not preserve proof of having passed the adapter unless the consumer independently reconstructs/checks it. |
| Correspondence evidence | `soundness::buildSealedSoundnessView` in `include/zkc/Soundness/PirSoundnessAdapter.h` and `lib/Soundness/PirSoundnessAdapter.cpp`; `pir::deriveVerifierProofReads` in `lib/Dialect/Pir/Transforms/ProtocolArtifacts.h` and `lib/Dialect/Pir/Transforms/ProtocolArtifacts.cpp`; `include/zkc/Soundness/SealedSoundnessView.h`; `test/Soundness/soundness-projection.mlir`; `test/lib/TestSoundnessProjection.cpp`; compiler provider tests. |

**Inference -- current closure pressure.** Statement labels copied into
`SealedSoundnessView` and later used by relation correspondence are author
labels that PIR canonical identity erases. Therefore those current views are
functions of the admitted PIR carrier, not functions of ProtocolId alone.

### 4.8 Reopen and discard authority

| Field | Current reconstruction |
|---|---|
| Classification and owner | Proposal/state change that deliberately loses admission on the editable branch. The consumer/capability rule is normative; the concrete helper is compiler-internal. |
| Source and authority | One `AdmittedPirArtifact`. The original capability remains valid and immutable. |
| Result and claimed relation | `MutablePirArtifact` containing a private clone of the original sealed root and a new adjacent `pir.protocol` whose body, kappa, routes, segments, and policy are cloned. The new open proposal is not admitted. Resolved `vocab` is deliberately omitted so the next seal resolves authority afresh. |
| Reads | The admitted subject only; no new registry lookup occurs while cloning. |
| Identity effect | The source ProtocolId is retained only on the cloned sealed source. The open proposal has no artifact identity and does not inherit the source id. Any successor id is minted only by a later seal. |
| Outcomes | Clone/container verification failure returns an error. No partially authorized successor is possible. |
| Capability | Original admission is preserved on the original handle and discarded on the mutable derivative. The internal wrapper is move-only mutable storage, not a semantic capability. |
| Correspondence evidence | `pir::openAdmittedProtocolForTransform` and `artifact::detail::ArtifactAccess::cloneForReopen` in `lib/Dialect/Pir/Transforms/ProtocolArtifacts.h`, `lib/Dialect/Pir/Transforms/ProtocolArtifacts.cpp`, and `lib/Artifact/Artifact.cpp`; exercised through `test/Compiler/pir-compiler-provider.mlir` and `test/lib/TestPirCompilerProvider.cpp`. |

## 5. Protocol construction and checked change

### 5.1 Static link

| Field | Current reconstruction |
|---|---|
| Classification and owner | Proposal-producing checked composition. `docs/spec/boundaries.md` §3 owns the contract; kernel composition rules supply BIND/LIN/closure meaning. |
| Source and authority | Two raw Open PIR protocols, explicit nonoverlapping producer/consumer face prefixes, and one `ProtocolEnvironment`. The inputs need not and cannot carry ProtocolIds as Open PIR. |
| Result and claimed relation | One new Open PIR proposal with namespaced/spliced spine, merged kappa, fused exported/source claim flows, rewritten material/value references, composed construction routes and segments, and rechecked open-protocol judgments. This is structural link correspondence, not semantic equivalence of sealed children. |
| Reads | Both complete open carriers, face prefixes, exact environment entries needed to judge both and the composite, claim descriptors, kappa axes, routes, check/discharge selectors, segments, domains, and policies. RelationContract, theorem catalog, endpoint profile, and evidence remain outside. |
| Identity effect | No identity is consumed or minted. The composite is Open; only its later seal mints a ProtocolId. Prefixes and the resulting canonical content can affect that future id. |
| Outcomes and side effects | Invalid prefixes, invalid operand protocols, kappa conflicts, missing/ambiguous claim-face matches, bad rewrites, route/linearity/closure failures, or invalid composite refuse. Inputs remain intact on every outcome; implementation erases a failed partial composite. |
| Capability | No authority is transferred from the components. The result is raw mutable Open PIR and must seal independently. |
| Correspondence evidence | `semantics::LinkEngine::link` in `include/zkc/Semantics/LinkEngine.h` and `lib/Semantics/LinkEngine.cpp`; pass adapter under `lib/Dialect/Pir/Transforms/PirLink.cpp`; `test/Transforms/pir-link*.mlir`; `test/Transforms/pir-link-routes*.mlir`. |

**Non-claim.** Link does not preserve hypothetical component security,
soundness, completeness, endpoint behavior, or already established admission.
Post-seal derivations must price the composite and any seam obligation.

### 5.2 Checked Protocol transform

| Field | Current reconstruction |
|---|---|
| Classification and owner | Checked semantic transformation inside a finite decision/search core. `docs/spec/compiler.md` owns `DOMAIN -> REALIZE -> VALID -> SCORE -> SELECT -> DECIDE`; the transform family owns its exact predecessor/successor relation. |
| Source and authority | `CompilerRequest` with an owned source artifact; exact `ArtifactSemantics`; immutable compiler semantic context including SoundnessContext, transform/domain providers, objective profile, exact refs/configuration, limits, target plans, and comparison scope. `ArtifactSemantics::authenticateArtifact` authenticates source observations before use. |
| Result and claimed relation | At the transform level, `CheckedTransformTrace` with authenticated source/final artifacts, checked `ClaimCorrespondence` rows, and separately attributed preservation claims. At the whole-core level, candidate/valid/scored candidate and selected ordinal, `no_selection`, or refusal. `LEGAL` establishes the family-defined structural transition and bound relation only. |
| Reads | Authenticated source observations; complete compiler configuration and provider exact refs; transform plan; family-specific carrier data; requested soundness targets/plans; objective inputs; comparison domain and tie-break rules. The complete environment is intentionally part of compiler configuration identity even though only cited closure belongs to Protocol identity. |
| Identity effect | Consumes predecessor ProtocolId. Empty transform plan preserves the original authenticated artifact and id. A content-changing plan may mint a different successor ProtocolId through reseal. Exact provider/configuration refs and CompilerRequest affect compiler comparability but do not enter ProtocolId. No persisted CompilerResult identity or schema is normative. |
| Outcomes | Unknown/mismatched authority, invalid request/domain, failed recognition/realization/authentication/check, malformed correspondence, failed derivation/constraint/objective, `no_selection`, and `DECIDE` refusal remain distinguishable in the core model. Search annotations or producer scores confer no authority. |
| Capability | Each raw successor is authenticated before its family checker or any next application consumes it. The final trace retains an immutable `AuthenticatedCompilerArtifact`; there is no serialized compiler capability. |
| Correspondence evidence | `include/zkc/Compiler/CompilerCore.h`; `lib/Compiler/CompilerCore.cpp`, especially `ArtifactSemantics::authenticateArtifact` and `realizeTransform`; `include/zkc/Compiler/PirCompilerProvider.h`; `lib/Compiler/PirCompilerProvider.cpp`; `test/Compiler/*.mlir`; `test/lib/TestCompilerCore.cpp`; `test/lib/TestPirCompilerProvider.cpp`. |

**Non-claims.** A checked trace does not establish general semantic
equivalence, unrequested property preservation, theorem truth, witness
translation, global optimality, or backend realization. The current
`PreservationClaim` rows are recorded after checking and are explicitly
attributed claims, not `LEGAL` verdicts.

### 5.3 Reseal and authenticate successor

| Field | Current reconstruction |
|---|---|
| Classification and owner | Composition of proposal production, kernel seal, persisted snapshot/decode, admission, representation authentication, and then family checking. It is architecturally distinct even though the current PIR provider fuses most steps inside `realize`. |
| Source and authority | Authenticated predecessor plus canonical transform application and exact PIR `ArtifactSemantics`/`ProtocolEnvironment`; internally, a reopened raw Open PIR modified by the family producer. |
| Result and claimed relation | New sealed PIR, `DecodedPirArtifact` snapshot, `AdmittedPirArtifact`, `OwnedCompilerArtifact`, then generic `AuthenticatedCompilerArtifact`. Only after generic authentication does the transform-family `check` compare predecessor and successor and return correspondences. |
| Reads | Candidate Open PIR; exact seal environment and cited closure; bytecode/canonical identity machinery; complete compiler semantics exact ref; source and successor observations; deterministic family replay inputs. |
| Identity effect | A new ProtocolId is recomputed from successor content. The predecessor id is retained by the trace and checker, not inserted into successor Protocol identity. For the empty plan no successor is manufactured: the source handle/id is reused. |
| Outcomes | Transform production, seal, snapshot/decode, admission, compiler authentication, replay-id comparison, or correspondence checking can each refuse. A raw producer output never enters the checked trace as an authorized successor. |
| Capability | Gains a fresh admitted and compiler-authenticated successor capability. No admission bit is copied from the predecessor. |
| Correspondence evidence | `SamePointKzgBatchTransformFamily::realize` performs reopen, realize, seal, snapshot, admit, and wrap; `CompilerCore::realizeTransform` then authenticates before `SamePointKzgBatchTransformFamily::check`; paths in `lib/Compiler/PirCompilerProvider.cpp` and `lib/Compiler/CompilerCore.cpp`; KZG compiler tests. |

## 6. Cross-domain semantic bridges

### 6.1 Relation-interface ingress

| Field | Current reconstruction |
|---|---|
| Classification and owner | Selected target bridge, absent as a current normative transition. `docs/spec/relations.md` explicitly says relation compilation is external and defines a post-seal contract instead. `docs/architecture.md` names a future relation-adaptation/authoring role. |
| Source and authority | The intended source would be native relation bytes/reference plus an identified adapter/format policy. No current API admits that tuple or produces an authenticated pre-seal interface. Current Open PIR can only author opaque digest-shaped anchors/material bindings; a `RelationContract` is loaded independently after seal. |
| Result and claimed relation | No current `RelationInterface`, `ProtocolInterface`, adapter-attributed fact set, or ingress capability. The closest durable object is content-addressed `RelationContract`, which declares an interface and correspondence for later judgment but does not author or authenticate Open PIR. |
| Reads | No current bridge read set exists. `RelationContractRegistry` reads a closed JSON schema and computes its contract digest; Open PIR authoring reads caller-provided anchors without opening relation bytes. |
| Identity effect | RelationContract has its own content digest. Attaching/changing it deliberately does not move ProtocolId or transcript bytes. No InterfaceId, adapter id, or relation-instance id is currently minted. |
| Outcomes | Registry schema admission can refuse malformed/unknown contract content. That is declaration loading, not ingress correspondence. Relation-source parsing/adaptation outcomes are unspecified. |
| Capability | No ingress capability exists. A loaded contract is ordinary registry data and gains authority only inside the post-seal correspondence judgment that checks it. |
| Correspondence evidence | `include/zkc/Registry/RelationContractRegistry.h`; `lib/Registry/RelationContractRegistry.cpp`; opaque anchors in PIR carrier; family authoring in `include/zkc/Family/FriFamily.h`; `test/Relation/relation-contract.test`; target-only boundary in `docs/architecture.md` §5. |

**Non-claims.** A RelationContract digest does not prove predicate meaning,
source correspondence, relation truth, non-underconstraint, witness-generator
correctness, or that any Protocol is about its bytes.

### 6.2 Post-seal relation correspondence

| Field | Current reconstruction |
|---|---|
| Classification and owner | Correspondence judgment owned by `docs/spec/relations.md` §4, with trust tiers in §3 and permanent non-claims in §6. |
| Source and authority | Admitted PIR artifact; one loaded content-addressed `RelationContract`; optional relation-artifact bytes; ProtocolEnvironment for profile resolution; currently optional caller-supplied expected field order. The tool first derives a `SealedSoundnessView`. |
| Result and claimed relation | Canonical JSON report containing ProtocolId, contract digest, and separate `computed`, `cross_checked`, `disagreed`, and `asserted` lists. It reports exact interface/anchor/byte/header/statement consistency and the asserted remainder; it is not a relation-validity verdict. |
| Reads | Contract anchor partition and interface schema; artifact claim anchors, statement labels, material bindings, seal-stage binds, and selected field facts; exact claim-profile digest; optional byte digest and R1CS header; caller expected field order. Relation constraint bodies and witness data are not read. |
| Identity effect | Consumes/cites ProtocolId and RelationContract digest; may compute a relation-byte content digest. The report carries those references but the current tool defines no explicit correspondence-result id or opaque capability. Contract changes do not remint ProtocolId. |
| Outcomes | Pre-subject I/O/registry failures are “cannot answer”; scope/profile/anchor failures can refuse; once cross-checking begins, the tool can emit a successful negative report with populated `disagreed` and exit status 1; an all-agree report exits 0. Asserted facts are neither refusal nor success evidence. |
| Capability and replay | Output is portable canonical content, not a retained admitted capability. Independent reliance must authenticate the named artifact/contract/bytes and repeat or validate the judgment; a report alone cannot authorize another subject. |
| Correspondence evidence | `tools/zkc-relation/zkc-relation.cpp`; `registry::RelationContractRegistry`; `relation::readR1csHeader`; `relation::anchorProjectionValue`; `soundness::buildSealedSoundnessView`; `test/Relation/relation-contract.test`; `test/Relation/relation-disagreements.test`. |

**Conflict -- result versus refusal.** `docs/spec/relations.md` §4 says every
failed comparison is a named refusal and describes canonical result content
consumed by digest. The current tool deliberately treats post-start
cross-check mismatches and unreadable supplied relation bytes as a negative
`disagreed` judgment, still emits the canonical report, and returns exit 1.
That is a materially different outcome algebra; this catalog does not relabel
the tool result as the specification's refusal.

**Inference -- current closure pressure.** Statement correspondence reads
`view.statementLabels`, which are copied from PIR author labels excluded from
ProtocolId. Therefore the current relation result is not a function of
`(ProtocolId, RelationContract digest, relation-byte digest)` alone.

### 6.3 Property analysis

| Field | Current reconstruction |
|---|---|
| Classification and owner | Derivation/judgment. The current normative domain is the Soundness Kernel's typed soundness and separate completeness tracks, not arbitrary property analysis. |
| Source and authority | Admitted PIR converted to owned `SealedSoundnessView`; immutable `SoundnessCatalog`; selected exact `RuleBinding` refs; resolved external parameters; `SoundnessContext`; exact `DerivationTarget`; caller-supplied explicit `DerivationPlan` and optional typed external judgments. The signature/catalog is theorem authority. |
| Result and claimed relation | `DerivationResult {artifactId, target, root}` whose root conclusion is an exact conditional `SecurityJudgment`, or a typed refusal. `zkc-derive` can encode a portable derivation witness and a judgment digest that another party re-derives from the artifact, signature, and witness. |
| Reads | Only the authenticated structural view exposed by the PIR adapter, exact selected rules/bindings and their preimages, resolved parameters, explicit plan/premises, and admitted notion schemas. It performs no theorem search, provider resolution, optimizer fallback, backend execution, or evidence-policy lookup. |
| Identity effect | ProtocolId is preserved as the judgment subject. Signature/rule/binding revisions and the judgment/witness digest distinguish analyses without changing ProtocolId. The specification does not make the DerivationResult a second Protocol identity. |
| Outcomes | Successful conditional judgment; refusal for malformed context, unresolved or unavailable rule/binding/parameter, wrong subject/site/index, invalid plan/premise, unsupported arithmetic/bound, or failed machine condition. Different valid plans may derive the same target without an artifact-global choice. |
| Capability and replay | The in-memory result is an owned judgment, not a Protocol capability. The encoded witness is independently re-checkable, but it confers only the exact conditional judgment it re-derives under the checker-supplied signature and artifact. |
| Correspondence evidence | `include/zkc/Soundness/SoundnessEvaluator.h`, `include/zkc/Soundness/SoundnessKernel.h`, `include/zkc/Soundness/SealedSoundnessView.h`, and `include/zkc/Soundness/PirSoundnessAdapter.h`; `lib/Soundness/`; `tools/zkc-derive/zkc-derive.cpp`; `test/Soundness/derive-witness.test`; `test/Soundness/derive-refusals.test`; `test/Soundness/two-analyses-one-artifact.test`; completeness fixtures. |

**Conflict with the charter's generic example, not with the current
Soundness specification.** The charter says analysis can successfully derive
a negative property judgment. The current `DERIVE` result is a conditional
notion-indexed security/completeness judgment; unsupported or failed
derivation is a refusal. There is no general Boolean property-analysis type
whose successful result is “property does not hold.” The relation tool does
have a successful negative correspondence report, but that is a different
transition and owner.

**Non-claims.** Acceptance does not prove a cited theorem, assumption,
binding faithfulness, whole-application security, relation satisfaction,
backend behavior, or reliance policy.

### 6.4 OIR projection

| Field | Current reconstruction |
|---|---|
| Classification and owner | Checked semantic projection/correspondence. Boundaries §2 owns `project`; Endpoints owns endpoint meaning; Carrier §6.1 owns OIR representation and identity. |
| Source and authority | Opaque `AdmittedPirArtifact` plus closed `EndpointKind` (`verifier` or `prover_skeleton`). The capability binds an immutable decoded carrier to its retained exact environment. |
| Result and claimed relation | `ProjectedOirArtifact`, an immutable copy-only paired capability holding private PIR backing and one `oir.artifact`. Projection proves `COV_realized` against source obligations, embeds canonical source positions, and for prover endpoints checks route totality and duality/counterparty rows. |
| Reads | Source body and canonical event positions; projection obligations; kappa sponge/IV/codecs/constants; cited check-contract digests; policy/routes; statement author labels; for prover, witness labels, route instances, and exact HoleContract schemas from the retained environment; endpoint kind. No backend target/profile is read. |
| Identity effect | Mints OIR id as tagged SHA-256 over canonical OIR bytes. OIR cites `source_pir_artifact_id`; it does not preserve or reuse ProtocolId. OIR `semantic_id` is a derived source/provenance-erased view, not a second stored id. Statement/witness labels enter OIR id even though PIR author labels do not enter ProtocolId. |
| Outcomes | Raw malformed PIR is rejected before production projection at decode/admit. Projection separately refuses unknown endpoint, unsupported discharge kind, missing kappa axis/codec/sponge/check vocabulary, empty verifier face, incomplete prover route, invalid coverage/duality, or internal identity/container mismatch. Unsupported projection does not invalidate its source. No partial OIR is returned. |
| Capability and replay | In-process result retains paired source/OIR authority. Printing yields a raw textual OIR copy; standalone OIR admission rechecks OIR identity and loaded check/hole ABI/digests, but source-free validation cannot establish source-obligation exhaustiveness or `COV_realized`. |
| Correspondence evidence | `pir::{projectArtifact,ProjectedOirArtifact,admitOirArtifact}` in `include/zkc/Dialect/Pir/Transforms/Projection.h`; `ProjectionEngine` in `lib/Dialect/Pir/Transforms/PirProject.cpp`; `tools/zkc-project/zkc-project.cpp`; `test/Transforms/pir-project*.mlir`; `test/Artifact/project.test`; `test/Oir/standalone-admission.test`; independent reference parity tests. |

**Inference -- identity/interface mismatch.** Because projection reads PIR
statement labels and emits them into OIR identity, two admitted carriers with
equal ProtocolId after id-stable relabeling can produce different OIR ids.
The current transition is thus closed over the full admitted carrier and
retained environment, but not over the advertised semantic pair
`(ProtocolId, endpoint_kind)`. There is no current separately authenticated
`ProtocolInterface` input that makes this dependency explicit.

**Non-claims.** Projection establishes structural source coverage and endpoint
orchestration, not runtime supplier correctness, target implementation
correspondence, Fiat--Shamir security, theorem security, or source coverage of
an independently authored source-free OIR.

### 6.5 Supplier binding

| Field | Current reconstruction |
|---|---|
| Classification and owner | Compatibility/admission of implementations to endpoint requirements. Endpoints §4 normatively owns execution-profile selection and mismatch semantics. The Rust emitter has a narrower operational JSON binding but no ratified standalone SupplierBinding schema. |
| Source and authority | Path A: authenticated OIR plus an in-process `ExecutionProfile`. Path B: canonical OIR JSON plus parsed `emit::binding::Binding`, whose fields name sponge/IV implementation, algebra, class codecs, check adapters, hole fills, construction digests, and binding-file digest. |
| Result and claimed relation | Ephemeral closed supplier selection sufficient for one execution or one emission. In the emitter, `gate_suppliers` checks class routes and construction pins and the subsequent `Walk` checks sponge/algebra/check/hole requirements. No separately returned admitted SupplierBinding artifact or capability exists. |
| Reads | OIR class-to-codec map, `param_digests`, endpoint rows, check/hole contract digests and ABIs, sponge/IV, algebra operations; binding/profile supplier tables. Emitter parsing also reads binding file bytes to compute a provenance digest. |
| Identity effect | OIR identity is unchanged. Runtime profile is a run fact and does not enter OIR id. The emitter bakes binding name and file digest into generated code, but no normative SupplierBindingId or compatibility-result id is defined. Digest equality authenticates selection and ABI, not supplier correctness. |
| Outcomes | Missing/mismatched codec, construction digest, sponge, sampling rule, algebra, check adapter, or hole fill is supplier/profile incompatibility. It is never a verifier proof reject. Unknown binding implementation vocabulary also refuses. |
| Capability and replay | `ExecutionProfile` is a borrowed in-process authority; `Binding` is parsed ordinary data. Neither can be serialized as an admitted current capability. Reuse repeats the gate at execution/emission. |
| Correspondence evidence | `include/zkc/Interpreter/ExecutionProfile.h`; supplier gates in `lib/Interpreter/Interpreter.cpp`; `emit/zkc-emit/src/binding.rs`; `emit/zkc-emit/src/emit/{mod,walk}.rs`; `test/Oir/profile-refusals.test`; `test/Emit/emit-document-gates.test`; binding-specific emit tests. |

### 6.6 Endpoint realization

| Field | Current reconstruction |
|---|---|
| Classification and owner | The general `oir-realize` semantic boundary is explicitly reserved and non-callable in `docs/spec/boundaries.md` §6. The current operational subset is endpoint emission to a standalone Rust crate under `docs/architecture.md` and `docs/status.md`; it must not be presented as the reserved contract already admitted. |
| Source and authority | Canonical OIR JSON bytes, parsed supplier binding, runtime crate path, optional crate name, optional vector corpus, and emitter implementation/version. The parser recomputes OIR id before reading rows and computes `semantic_id`. It does not receive authenticated sealed-source/projection context. |
| Result and claimed relation | In-memory `EmittedCrate {crate_name, lib_rs, cargo_toml, readme, conformance}` and then files for a buildable standalone verifier or prover. Supplier gaps are refused before or during the single semantic walk. The package bakes OIR id, semantic id, source PIR id, binding name, and binding-file digest. |
| Reads | Entire canonical OIR document and row grammar; all endpoint supplier requirements; chosen binding; runtime path and feature requirements; optional vectors and caller crate name; emitter source/version; filesystem paths when writing. |
| Identity effect | Preserves/cites OIR id, OIR semantic id, source PIR id, and binding-file digest. No normative BackendArtifact/EmittedArtifact identity function exists. README claims deterministic emission for its named inputs, but generated bytes are not a current semantic identity. |
| Outcomes and side effects | Malformed/noncanonical OIR, identity mismatch, supplier incompatibility, row/ABI failure, unsafe/unrepresentable generated identifier/text, vector mismatch, or I/O/build failure. `emit::emit` is side-effect free and returns all strings; `zkc-emit` writes output files sequentially, so a late I/O failure has no stated transactional rollback and may leave a partial directory. |
| Capability and replay | Generated source is an operational package, not an admitted opaque endpoint capability. Consumers can rebuild/test it; no current independent `oir-realize` validator consumes source PIR plus projection context and returns the reserved conformance evidence. |
| Correspondence evidence | `emit/README.md`; `emit/zkc-emit/src/doc.rs::Document::parse`; `binding.rs::Binding::parse`; `emit/mod.rs::{gate_suppliers,emit}`; `emit/walk.rs`; `emit/main.rs`; `emit/zkc-rt/`; `test/Emit/*.test`. |

**Conflict -- functional input set.** `emit/README.md` says emission is
byte-deterministic in `(document, binding, emitter version)`, while
`emit::emit` also consumes `rt_path`, optional `crate_name`, and optional
vectors, all of which can affect emitted files. The operational transition's
actual functional inputs are broader than that sentence records.

**Non-claims.** Current emission does not establish supplier correctness,
general backend conformance, source-relative `COV_realized` for source-free
OIR, stable binding/backend schemas, deployment, or the reserved
`BackendArtifact + ConformanceEvidence` result.

## 7. Operational, evidential, and reliance transitions

### 7.1 Deploy

| Field | Current reconstruction |
|---|---|
| Classification and owner | Architecture-only target state change. `docs/architecture.md` defines the role; `docs/status.md` reports wider emission targets and deployment as not built. |
| Source and authority | Intended: emitted endpoint artifact, resources/setup, topology, and deployment policy. No current typed tuple, admitted setup/resource capability, or deployment policy exists. |
| Result and claimed relation | Intended `DeploymentBinding` resolving already authorized semantic roles to physical resources. No current result schema, identity, capability, or checker exists. An emitted crate directory is not a deployment. |
| Reads and identity | Unspecified. Architecture requires separate implementation, setup, deployment, and invocation identities but explicitly says their schemas/identity functions remain unratified. |
| Outcomes and effects | Target prose calls for refusal on substitution or trust-zone mismatch. Current failure, rollback, supersession, and partial-deployment semantics are absent. |
| Correspondence evidence | No implementation/test correspondence located. `docs/architecture.md` §§4--8 and authority map §12; `docs/status.md` architecture-progress table. |

### 7.2 Invoke

| Field | Current reconstruction |
|---|---|
| Classification and owner | Operational execution. Endpoints §§4 and 6.3 normatively own direct verifier/prover semantics. The broader architecture invocation join is not implemented. |
| Source and authority | C++ verifier: `oir::ArtifactOp`, `ExecutionProfile`, statement map, proof bytes. C++ prover: OIR, profile, statement map, witness map. Generated endpoints bake suppliers and expose typed `verify(statement, proof)` or `prove(statement, witness)`. There is no DeploymentBinding, StatementInstance identity, InvocationBinding, provider/session capability, or explicit authorized prover-local randomness input. |
| Result and claimed relation | Verifier `ExecutionResult {verdict, challenges, diag}` where verdict is `accept` or a named reject; prover `ProveResult {proof, challenges}` with no accept verdict. The relation is one execution under one concrete profile, not universal endpoint conformance. |
| Reads | Recomputed OIR identity before semantics; endpoint ABI and program; statement/proof or opaque witness payloads; codecs, sponge, sampling, algebra, check/hole suppliers and construction digests; current in-process runtime behavior. |
| Identity effect | No invocation or result identity is minted. OIR/source identities remain cited by the program; profile and suppliers are run facts. Proof bytes and challenges are invocation outputs, not semantic identities. |
| Outcomes | Verifier accept or named reject classes are distinct from malformed OIR/input, unavailable/mismatched supplier, and execution defect. Prover returns bytes or a fill/profile error and never a verifier verdict. Unknown profile is cannot-execute, not proof false. |
| Capability and effects | The C++ witness surface is a map of opaque hex payloads, not a scoped invocation capability. Generated Rust uses typed move-only `Payload` fields for current witness handles, but no deployment/session/lifetime/revocation policy is represented. Supplier calls may execute during a run; no general external-effect/rollback contract exists. |
| Correspondence evidence | `include/zkc/Interpreter/{Interpreter,ExecutionProfile}.h`; `lib/Interpreter/Interpreter.cpp::{execute,prove}`; `tools/zkc-run/zkc-run.cpp`; generated APIs under `emit/`; `test/Oir/interpreter-identity.test`; `test/Oir/profile-refusals.test`; `test/Oir/prover-round-trip.test`; `test/Oir/*-exec.test`; emitted round-trip tests. |

**Non-claims.** One accept or emitted proof does not establish relation
satisfaction, soundness, completeness, zero knowledge, supplier correctness,
deployment correctness, or behavior outside the exact run.

### 7.3 Record or attribute observation

| Field | Current reconstruction |
|---|---|
| Classification and owner | Observation/evidence boundary. Endpoints §4 requires an attributable execution record with deterministic endpoint observables; prover §6.3 additionally requires exact PIR/OIR/profile/supplier and opaque-input digest bindings. Architecture defines a `Run record` target role. |
| Source and authority | Intended: one bound invocation, executor identity, exact semantic/deployment/runtime inputs, event/transcript/proof-ABI/public-binding/opaque-call/terminal observables, and secret-safe digest policy. The current executor has only the direct invocation inputs above. |
| Result and claimed relation | Current public C++ results expose verdict/proof, ordered challenges, and verifier diagnostics. Tools and vector harnesses can serialize selected observations for tests. No first-class generic `RunRecord`, recorder API, record identity, issuer attribution, or full §4/§6.3 schema was located. |
| Reads | Current narrow result construction reads execution state sufficient for verdict/proof and challenge log. The required full record would also read identities, supplier digests, opaque-input digests, and the named deterministic logs; those are not all exposed by `ExecutionResult`/`ProveResult`. |
| Identity effect | No run/evidence identity is specified or minted. Existing vector files bind an OIR artifact id for test replay, but they are not a generic run-record identity. |
| Outcomes | No generic record success/refusal/partial-record algebra exists. A run can already have invoked suppliers before a later operational error; current docs do not define a general partial-effect observation record for that case. |
| Capability and replay | Challenge logs support a narrow deterministic replay check. They do not authorize the subject or satisfy the required full attributable record by themselves. |
| Correspondence evidence | `ExecutionResult` and `ProveResult` in `include/zkc/Interpreter/Interpreter.h`; `tools/zkc-run/`; `test/Oir/Inputs/*vectors.json`; `test/Oir/Inputs/build-runner-vectors.py`; evaluation records under `evaluation/`. |

**Conflict -- normative observable surface versus current public result.**
`docs/spec/endpoints.md` §4 says an attributable Tier-2 record must expose the
ordered event log, transcript log or semantic digest, proof-ABI log,
public-binding log, opaque-call results, and terminal record; §6.3 requires
identity and opaque-input digest bindings for prover runs. The current public
C++ result structs expose only verdict/proof, challenges, and one verifier
diagnostic. A smaller API is allowed as a diagnostic API, but it is not the
normative attributable record the same section requires.

### 7.4 Appraise evidence

| Field | Current reconstruction |
|---|---|
| Classification and owner | Evidence appraisal is an architecture-only target relation, not a current normative specification surface. |
| Source and authority | Intended typed evidence, exact subject/transition binding, issuer, verification procedure, conditions, residuals, and appraisal policy. No generic current types or policy authority are defined. |
| Result and claimed relation | Intended policy-qualified assessment of what evidence supports and does not support. No generic Assessment/Appraisal result, identity, refusal vocabulary, or capability exists. |
| Nearby but distinct mechanisms | `zkc-derive --check` re-derives one derivation witness; relation reports separate trust tiers; conformance tests compare exact vectors; formalization receipts and evaluation records have domain-specific readers. These are evidence production/checking mechanisms, not one appraisal transition. |
| Identity and replay | Domain-specific artifacts cite their own subjects and pins. There is no generic evidence identity or appraisal cache key. |
| Correspondence evidence | Architecture's five-layer model in `docs/architecture.md` §10; evidence links in `docs/README.md`; formalization/evaluation tests. `docs/status.md` does not claim a generic evidence admission implementation. |

**Non-claim.** A passing test, replay, receipt, witness recheck, or relation
cross-check cannot be promoted by this absent layer into protocol meaning or
universal implementation correctness.

### 7.5 Make use-specific reliance decision

| Field | Current reconstruction |
|---|---|
| Classification and owner | Consumer decision/admission. `docs/architecture.md` defines `Admission(Object, Judgment, Evidence, Policy) -> scoped admission \| refusal`; no current normative reliance specification exists. |
| Source and authority | Intended exact objects, typed judgments, attributed evidence, consumer trust anchors/policy, conditions, intended use, and accepted residual risk. No current relying-policy type or authority registry exists. |
| Result and claimed relation | Intended scoped permission or denial to rely on supplied material for one named use. It must not create semantic truth or remint the subject. No current result, id, capability, supersession rule, or persistence schema exists. |
| Outcomes | Target categories are policy acceptance, appraisal rejection, or reliance denial, distinct from semantic refusal and runtime rejection. Current code has no such generic outcome channel. |
| Correspondence evidence | `docs/architecture.md` §§5 and 10--12; `docs/status.md` marks “Evidence admission policy” not built. No implementation/test correspondence located. |

## 8. Current read-set and closure matrix

Legend: **direct** means the transition reads the material; **resolver** means
the full provider is supplied but only a cited subset is allowed to affect the
semantic result; **embedded** means the input subject already carries the
identified data; **none** means the material is outside the transition. This
matrix records the current design, not the selected Stage 1 target.

| Transition | Protocol/carrier content | Cited seal closure | Complete retained resolver | Carrier-only labels or routes | Interface / ABI | Analysis or compiler configuration | Supplier/runtime closure | External relation, theorem, or relying policy |
|---|---|---|---|---|---|---|---|---|
| Resolve for seal | direct Open PIR | produced from citations | resolver | labels may select canonical facts; routes direct | none separately | none | none | relation anchors opaque; others none |
| Seal | direct Open PIR | embedded in result | resolver | author selectors normalized; routes direct | no separate Interface | none | construction declarations only | relation bodies/theorems/policy none |
| Admit | direct decoded sealed carrier | direct and re-resolved | resolver, then retained | direct where seal checks require | no separate Interface | none | none | none |
| Static link | direct two Open PIRs | re-resolved on operands/result | resolver | direct and rewritten | face prefixes only | none | none | none |
| Consumer-view derivation | direct through capability | direct pins | direct while adapting | statement labels/material labels/routes may be read | current ABI inferred from labels | purpose-specific | construction-profile data for proof reads | theorem authority not yet applied |
| Property analysis | owned view | exact refs in view | none after adaptation | only fields retained by view | current structural sites | SoundnessContext, rules, bindings, plan | none | explicit theorem/rule and premise authority |
| Checked transform | direct through authenticated payload | direct via PIR semantics | complete environment is compiler configuration | family-specific mutable carrier reads | no separate Interface | full request/providers/objectives/SoundnessContext | none | explicit rule authority; no relying policy |
| Relation correspondence | admitted view | profile/anchor pins | resolver for profile and view construction | statement/material author labels direct | current ABI inferred from labels | optional caller field expectation | none | RelationContract and optional bytes direct |
| OIR projection | direct through capability | direct pins | retained resolver | statement/witness labels and routes direct | inferred/built, not separate input | endpoint kind | declarations only, no implementations | none |
| Supplier binding | OIR only | OIR construction/check/hole pins | none | OIR labels/routes already identified | direct OIR ABI | binding/profile configuration | direct suppliers | no relation/theorem/relying policy |
| Endpoint realization | OIR JSON only | OIR pins | none | OIR labels identified | direct | emitter options/vector corpus | binding and runtime path direct | no relying policy |
| Invoke | OIR direct | OIR pins | optional for standalone OIR admission | OIR labels identified | statement/proof/witness direct | none | execution profile and live suppliers direct | no theorem/relying policy |
| Appraise / rely | no current contract | no current contract | no current contract | no current contract | no current contract | intended policy input | intended deployment/run facts | intended evidence issuer and relying policy |

Three current closure conclusions follow.

1. **Observed.** Seal and Protocol identity intentionally close over cited
   vocabulary content, not the complete environment.
2. **Observed.** Compiler comparability intentionally closes over a complete
   compiler configuration, independently of Protocol identity.
3. **Inference.** Projection and relation correspondence close over current
   admitted carrier labels that Protocol identity erases. They therefore need
   either the full carrier as an advertised input or a separately identified
   interface subject; ProtocolId alone is insufficient.

The current corpus has no explicit semantic-regime reference. Specification
revision, exact declaration refs, execution profiles, and provider exact refs
partially serve that role in different domains, but “same bytes under a
different regime” has no one current comparison or migration rule.

## 9. Identity-effect ledger

| Transition | Consumes | Preserves | Mints | Provenance/configuration only | Explicitly excluded or absent |
|---|---|---|---|---|---|
| Author/import | source text/description | none | none | generator/template revision implicit | no ProtocolId authority |
| Resolve/seal | Open content + cited preimages | n/a | ProtocolId | complete resolver outside id | evidence, theorem, backend, calibration, author labels |
| Persist/decode/admit | ProtocolId and carrier | ProtocolId | no semantic id | producer/version and admission environment | no persistence/admission/regime id |
| Consumer view | ProtocolId | subject binding | none | exact refs in view | no independent view id generally |
| Reopen/link | source carriers | source capability remains separate | none until seal | prefixes and source trace | no inherited child/source authority |
| Checked transform | predecessor ProtocolId + compiler config | identity plan only | successor ProtocolId on content change | provider/config refs and trace | no CompilerResult id; claims are not verdict ids |
| Relation correspondence | ProtocolId, contract digest, optional bytes digest | ProtocolId unchanged | no explicit report id | caller expectation and assertions | RelationContract excluded from ProtocolId |
| Property analysis | ProtocolId, signature/rule refs | ProtocolId as subject | judgment/witness digest operationally | plan/context/hypotheses | judgment excluded from ProtocolId |
| OIR projection | admitted PIR + endpoint | source PIR cited, not preserved as OIR identity | OIR id | OIR semantic-id view | backend/profile excluded |
| Supplier binding/emission | OIR id + binding/profile | OIR id cited | no normative binding/emitted id | binding file digest, emitter options/version | supplier correctness absent |
| Invoke/record | OIR id + run inputs | semantic ids unchanged | no invocation/run id | profile/supplier and inputs are run facts | run cannot remint PIR/OIR meaning |
| Deploy/appraise/rely | target-only | target-only | unspecified | unspecified | no current schema or id |

## 10. Capability and serialization ledger

| Object | Current authority | Copy/alias behavior | What serialization or mutation does |
|---|---|---|---|
| Raw `pir.protocol` | None beyond local representation verification | Mutable MLIR handle | Remains raw; must seal |
| Raw `pir.sealed` | Identified carrier; not an opaque public capability by type | Mutable MLIR operation if exposed | Next consumer recomputes identity/judgment or snapshots/admit |
| `DecodedPirArtifact` | Transport, structure, stored/computed id | Copy-only shared private immutable storage | Printed/serialized copy is raw at next boundary |
| `AdmittedPirArtifact` | Exact immutable subject plus retained environment-backed seal admission | Copy-only shared private immutable storage | Original copies retain authority; mutable/serialized derivative does not |
| `SealedSoundnessView` | Trusted only when produced by the admitted adapter for the exact subject | Plain owned aggregate | Portable data alone does not prove adapter provenance |
| `AuthenticatedCompilerArtifact` | Core-owned result of one exact `ArtifactSemantics` authority | Shared immutable handle; direct construction restricted | No persisted capability schema |
| `ProjectedOirArtifact` | Paired source/OIR result of current projector | Copy-only shared private backing | Printed OIR is raw; source-free re-admission cannot recover coverage authority |
| `DerivationResult` / witness | Exact conditional judgment; witness independently recheckable | Owned data / portable canonical document | Requires artifact and checker-supplied signature to regain checked authority |
| Relation report | Attributed canonical answer from current tool, not opaque capability | Portable bytes | Consumer must authenticate named inputs and interpretation |
| `ExecutionProfile` / emitter `Binding` | Ephemeral supplier selection input | Borrowed object / ordinary parsed data | No admitted serialized capability |
| Emitted crate | Operational package with baked references | Filesystem/build artifact | No current semantic admission or deployment capability follows |
| Run/evidence/reliance roles | Not implemented generically | Unspecified | Unspecified |

## 11. Consolidated conflicts, gaps, and non-claims

### 11.1 Observed conflicts

1. The normative overview's owner table omits the self-declared canonical
   Relations specification even though the top-level documentation map
   includes it.
2. Relation §4 specifies failed comparisons as refusals; `zkc-relation`
   deliberately emits negative `disagreed` reports after judgment begins.
3. Emitter documentation's stated deterministic input tuple omits runtime
   path, optional crate name, and optional vector corpus accepted by the
   implementation.
4. The endpoint specification requires a rich attributable run record, while
   current public executor result types expose only verdict/proof, challenges,
   and a narrow diagnostic. The smaller API can be valid as a diagnostic API,
   but it is not the specified record.

### 11.2 Observed missing current subjects or transitions

- no explicit SemanticRegime or stable regime comparison key;
- no separate current ProtocolInterface/InterfaceId;
- no separate ProverPlan/ProverPlanId; construction routes are embedded in
  Protocol content and partially fill that role;
- no pre-seal relation adapter/ingress capability;
- no stable general supplier-binding or backend-artifact schema;
- no admitted general `oir-realize` implementation or validation evidence
  object;
- no DeploymentBinding, InvocationBinding, RunRecord, EvidenceAssessment, or
  scoped RelianceDecision implementation;
- no generic successful-negative property-analysis result in the Soundness
  Kernel; and
- no persisted compiler request/result schema or compiler CLI.

### 11.3 Cross-cutting non-claims

- Content identity is not retained admission authority.
- Same ProtocolId does not imply same carrier labels, interface, retained
  environment, semantic regime, OIR identity, analysis result, runtime
  profile, or behavior.
- Structural seal does not imply cryptographic security or endpoint
  executability.
- Conditional analysis does not imply theorem truth or application security.
- Checked transformation does not imply every property is preserved.
- Relation correspondence does not imply relation truth or satisfaction.
- OIR projection does not imply backend realization or supplier correctness.
- Supplier digest agreement does not prove implementation conformance.
- Emitted source is not deployment, and one invocation is not evidence of all
  executions.
- Evidence cannot flow backward to redefine Protocol/OIR semantics, and
  absent appraisal/reliance machinery cannot be simulated by calling a test
  “admission.”

## 12. Evidence path index

This compact index identifies the strongest current correspondence paths used
above. It is not a test-coverage claim beyond the named boundaries.

| Boundary | Primary implementation | Representative tests |
|---|---|---|
| Seal and resolution | `include/zkc/Semantics/SealEngine.h`, `lib/Semantics/SealEngine.cpp`, seal battery and construction graph | `test/Transforms/pir-seal.mlir`, `test/Transforms/pir-seal-invalid.mlir`, `test/Transforms/seal-engine-parity.test`, `test/lib/TestSealEngine.cpp` |
| Persist/decode/admit | `include/zkc/Artifact/Artifact.h`, `lib/Artifact/Artifact.cpp` | `test/Artifact/lifecycle.mlir`, `test/Artifact/roundtrip.mlir`, `test/Artifact/fail-closed.test`, `test/lib/TestArtifactLifecycle.cpp` |
| Reopen and views | `lib/Dialect/Pir/Transforms/ProtocolArtifacts.h`, `lib/Dialect/Pir/Transforms/ProtocolArtifacts.cpp`, `lib/Soundness/PirSoundnessAdapter.cpp` | `test/Soundness/soundness-projection.mlir`, `test/Compiler/pir-compiler-provider.mlir` |
| Static link | `include/zkc/Semantics/LinkEngine.h`, `lib/Semantics/LinkEngine.cpp` | `test/Transforms/pir-link*.mlir`, route variants |
| Checked transform | `include/zkc/Compiler/`, `lib/Compiler/` | `test/Compiler/compiler-core.mlir`, `test/Compiler/kzg-batch-core.mlir`, `test/lib/TestCompilerCore.cpp`, `test/lib/TestPirCompilerProvider.cpp` |
| Relation correspondence | `tools/zkc-relation/zkc-relation.cpp`, Relation registry/header readers | `test/Relation/relation-contract.test`, `test/Relation/relation-disagreements.test` |
| Analysis | `include/zkc/Soundness/`, `lib/Soundness/`, `tools/zkc-derive/` | `test/Soundness/derive-*.test`, completeness and two-analysis fixtures |
| Projection/OIR admission | `include/zkc/Dialect/Pir/Transforms/Projection.h`, `lib/Dialect/Pir/Transforms/PirProject.cpp` | `test/Transforms/pir-project*.mlir`, `test/Artifact/project.test`, `test/Oir/standalone-admission.test` |
| Supplier binding/emission | `emit/zkc-emit/src/doc.rs`, `emit/zkc-emit/src/binding.rs`, `emit/zkc-emit/src/emit/`, `emit/zkc-rt/` | `test/Emit/emit-document-gates.test`, `test/Emit/emit-schnorr.test`, `test/Emit/emit-schnorr-prover.test` |
| Direct execution | `include/zkc/Interpreter/Interpreter.h`, `include/zkc/Interpreter/ExecutionProfile.h`, `lib/Interpreter/Interpreter.cpp`, `tools/zkc-run/zkc-run.cpp` | `test/Oir/schnorr-exec.test`, `test/Oir/interpreter-identity.test`, `test/Oir/profile-refusals.test`, `test/Oir/prover-round-trip.test` |
| Deployment, generic evidence appraisal, reliance | No current implementation | No current conformance tests |

## 13. Reconstruction boundary

This dossier establishes only the current baseline needed for Stage 2
comparison. It does not decide whether any target transition should use direct
recomputation, an opaque paired capability, a portable witness, translation
validation, a durable transition record, or no artifact. It also does not
resolve the current label/interface closure issue, introduce target identities,
or migrate current APIs. Those are generative and convergence tasks, not facts
about the current system.
