# Current-to-target semantic correspondence and gap inventory

> **Document kind:** Temporary Stage 4A semantic correspondence and gap
> inventory
> **Document state:** Complete against the selected durable target and its
> frozen comparative basis; no migration or implementation authority
> **Authority:** None. Current normative meaning remains in `docs/spec/`.
> The selected target remains non-normative. Its comparative basis is frozen in
> [the integrated target semantic model](target-semantic-model.md); final
> convergence and post-freeze closure refinements are owned by
> [convergence](convergence.md) and the durable owner pages. This inventory does not establish an
> Analysis result, Compiler decision, implementation status, compatibility
> claim, migration plan, feasibility result, or Stage 4B activation.
> **Compared:** 2026-08-22
> **Current inputs:** [current Analysis](current-analysis.md), [current
> Compiler](current-compiler.md), [current history, authority, and
> consumers](current-history-authority-and-consumers.md), and [current-model
> synthesis](current-model-synthesis.md)
> **Target inputs:** the frozen [federated Analysis and validated-decision
> Compiler target model](target-semantic-model.md), final
> [convergence](convergence.md), and the durable
> [Analysis and Compiler architecture](../../project/analysis-and-compiler-architecture.md)
> plus its exact Analysis, Compiler, Relations, and PIR owner pages
> **Disposition:** Absorb reviewed correspondences, selected invariants,
> conflicts, and owner boundaries into durable `analysis/`, `compiler/`,
> `relations/`, `project/`, and exact Stage 4B handoff owners. Then delete this
> page with the temporary Stage 4A package before `docs-next/` authority
> cutover.

## 1. Purpose and reading rule

This page records how the current bounded Soundness--Compiler system
corresponds to the selected ideal Stage 4A model. It is a semantic inventory,
not a statement that the current implementation should be preserved, adapted,
or replaced in any particular order.

The two endpoints are:

```text
current
  admitted PIR-derived Soundness view
  + immutable selected Soundness calculus
  + explicit derivation plans
  -> conditional SecurityJudgments or typed refusal

  finite provider-defined transform/derivation plan domain
  -> construct and admit candidates
  -> rerun Soundness derivations and exact bound constraints
  -> score static proof bytes
  -> select an ordinal or no_selection
  -> same-authority recomputation

target
  exact admitted Stage 3 subjects and source-owned views
  + family-owned question, proposition, model, and hypotheses
  + separately identified semantic and validation bases
  -> family-owned affirmative claim, and an exact negative only where the
     family admits a sound negative schema
  -> qualified Analysis outcome and process-local capability

  exact transform problem and decision policy
  -> unauthoritative production and frozen proposal scope
  -> PIR-owned target admission
  -> independently owned transition qualification
  -> closed semantic candidate and comparison-alternative domains
  -> complete comparison-alternative-indexed assessment ledger
  -> checked decision-sufficiency closure -> scoped qualified decision

  checked DecisionPolicy + any exact reached qualified subset
    + exact reached closure results actually read + audit-relative accounting
    -> independently checked explicitly open report

  preparation/check failure at any reached operation -> outer outcome
```

The word *gap* does not mean defect. A gap may be an intentional split, a new
semantic category, an explicitly deferred owner boundary, or a current
strength retained under a more precise identity and authority model.

## 2. Classification vocabulary

Every inventory row uses exactly one classification.

| Classification | Meaning in this inventory |
|---|---|
| **Retained** | The current semantic invariant remains valid in the target, even if its representation or owner-facing interface is different. |
| **Split** | One current object, operation, or authority carries several meanings that become independently identified and checked in the target. |
| **Replaced** | The target uses a materially different semantic contract; the current construct is evidence about the old model but is not target authority. |
| **New** | The target introduces a semantic category or judgment with no current authoritative counterpart. |
| **Deferred/Outside** | The subject is deliberately outside Stage 4A meaning, remains with another owner, or requires a separately reviewed later decision. |

The classifications describe semantic correspondence only. They imply no
implementation order, code organization, migration mechanism, compatibility
promise, effort estimate, or feasibility conclusion.

## 3. Top-level correspondence

| Current center | Target center | Classification | Exact consequence |
|---|---|---|---|
| The Soundness Kernel is both the executable property architecture and the Compiler's property evaluator. | Analysis is a federation of closed family profiles; Compiler consumes exact qualified Analysis results without owning their meaning. | **Split** | Current Soundness becomes one valid internal Analysis basis profile rather than the universal Analysis payload or a Compiler-local calculus. |
| One `SemanticContext` closes artifact semantics, Soundness, transform families, domains, derivations, and objective profiles. | Upstream admission, Analysis, relation, Compiler-policy, Stage 4B, and Evidence authorities remain independently owned and are associated explicitly. | **Split** | Exact closure remains, but authority and identity are factored by semantic owner. |
| `DOMAIN -> REALIZE -> VALID -> SCORE -> SELECT -> DECIDE` is one checked-search pipeline. | Five Compiler planes separate problem, production, proposal resolution, qualification/assessment, and decision. | **Split** | The useful checked-decision discipline remains while domain declaration, semantic work, and producer search stop being one stage vocabulary. |
| Current products are public owned values or optional ordinals rechecked under the same configured implementation. | Semantic records, checking occurrences, live capabilities, replay bundles, and operational records are different categories. | **Split** | A serializable value or matching ID never substitutes for fresh owner-issued authority. |
| Property, transformation, and decision support are mostly Soundness- and same-point-KZG-shaped. | Family semantics and producer mechanisms are closed or open at explicit extension boundaries. | **Replaced** | The current families remain bounded evidence; they do not define the general target architecture. |

## 4. Analysis correspondence and gaps

### 4.1 Scope and semantic center

| Current Analysis meaning | Target meaning | Classification | Boundary retained or changed |
|---|---|---|---|
| Post-admission analysis over an immutable PIR-derived semantic view. | Analysis begins only from exact admitted Stage 3 subjects and owner-created adequate views. | **Retained** | Carrier bytes, producer claims, and unauthenticated view-shaped values remain non-authoritative. |
| The executable property surface is a Soundness Kernel for admitted Soundness, Knowledge, and Completeness indices. | A closed versioned set of family profiles owns equality, refinement, change, distribution, cost, cryptographic, transport, composition, and coverage meanings. | **Replaced** | Soundness is one family group and basis profile, not the common result type. |
| `SecuritySubject` is a closed union of Protocol claim, consumed-claim vector, and external instance; occurrence sites are separate. | Every family owns an exact subject tuple, occurrence graph, semantic maps, observer/direction coordinates, and model instance. | **Split** | There is no universal optional-field subject. Families contain only coordinates they semantically read. |
| Security notion and notion-indexed result shape prevent a generic scalar security flag. | Each family owns its conclusion, result, negative meaning, valid bases, and quantitative operations behind a thin common lifecycle. | **Retained** | Family indexing is generalized without erasing family-specific semantics. |
| The current conclusion is explicitly conditional under inherited hypotheses. | `AnalysisProposition<F>` is the exact truth-apt goal plus canonical typed hypothesis context. | **Retained** | A successful check establishes the conditional proposition, not its assumptions or a concrete security verdict. |
| Rule and theorem citations are annotations outside the executable catalog. | Evidence, citations, theorem names, and proof artifacts remain non-authoritative until an exact admitted semantic and validation basis checks their use. | **Retained** | Documentation or formalization metadata still cannot mint a property result. |

### 4.2 Question, proposition, request, and identity

| Current object or omission | Target object | Classification | Correspondence |
|---|---|---|---|
| A derivation request names an artifact, exact target, and explicit plan, but there is no separate stable question identity. | `AnalysisQuestionId` identifies the family, exact semantic subject closure, maps, model, experiment, observer, parameters, result schema, and semantic read closure. | **New** | The semantic problem is stable across proof tools, proof bytes, assurance requests, and operational limits. |
| The evaluated root is a `SecurityJudgment`; the current judgment digest combines conclusion content without separating every semantic category. | `AnalysisGoalId` identifies the exact hypothesis-free conclusion and `AnalysisPropositionId` identifies the truth-apt conclusion plus residual hypotheses. | **Split** | Different bounds or residual hypotheses are different propositions even when they answer one question. |
| Request, plan, whole-signature digest, and conclusion digest jointly carry replay-related meaning. | `AnalysisRequestId`, `SemanticBasisId`, `ValidationBasisId`, `BasisQualificationId`, `DerivationId`, `JudgmentRecordId`, and `AnalysisReplayBundleId` are independent identities. | **Split** | A proof, checker, claim, request, result, and replay package are never aliases. |
| Several derivations may derive the same target, but no first-class proposition/basis/derivation identity split exists. | Several semantic bases, validation bases, and derivations may establish one proposition while retaining their exact qualifications. | **New** | Proof multiplicity does not change proposition meaning; assumption or model changes do. |
| The implementation carries identity-bearing static/adaptive quantification that the normative index grammar omits. | Typed parameters and quantifiers enter the exact family question profile when they affect meaning. | **Replaced** | The target rule is semantic-family closure; it does not silently select the current code-only coordinate or its encoding. |
| An application site affects derivation but is omitted from the completed `SecurityJudgment`. | Exact occurrence coordinates enter the question or basis according to whether they affect proposition meaning or only one support path. | **Split** | Occurrence is no longer silently lost, while its identity placement remains semantic rather than class-layout-derived. |

### 4.3 Views, read closure, and catalog authority

| Current object | Target object | Classification | Correspondence |
|---|---|---|---|
| One broad `SealedSoundnessView` supplies the current finite projection vocabulary. | Upstream owners supply purpose-specific view contracts with complete `SemanticReadClosure` and per-basis `BasisReadClosure`. | **Split** | Reads affecting proposition meaning are separated from reads used only to validate one support path. |
| `ArtifactProjection` is intended to be the complete finite read channel. | Family profiles and basis registries declare closed source-owned read vocabularies; hidden reopening or ambient lookup is prohibited. | **Retained** | Exact reviewable reads remain a core invariant. |
| `BoundRelationAnchorCount` and `CommittedArity` are executable projections but are absent from the current normative projection grammar. | Every semantic or basis read is explicitly owned, typed, and included in the appropriate closure identity. | **Replaced** | Neither the incomplete normative list nor the implementation-only extension is imported as target authority. |
| `freezeSoundnessCatalog` closes schemas, rules, bindings, and exact references into immutable executable authority. | `FamilySemanticProfile`, `FamilyBasisRegistry`, `FamilyValidationProfile`, and `FamilyOperationPolicy` close meaning, support, checking, and operation separately. | **Split** | Immutable closed profiles remain, while adding a checker no longer changes semantic question meaning. |
| The current signature separates executable catalog content from editorial annotations. | Semantic bases remain separate from Evidence and annotations; validation bases separately identify checker and translation trust. | **Retained** | Evidence cannot become inference authority by sharing a registry entry. |
| A whole signature digest changes when unused catalog content changes. | Basis identity includes only the exact used family/profile slice, dependency closure, reads, premises, substitutions, and transformers. | **Replaced** | Unused registry content is not proposition or used-basis identity. |

### 4.4 Derivation, checking, and basis lanes

| Current mechanism | Target mechanism | Classification | Correspondence |
|---|---|---|---|
| The recursive `Assume`/`Apply` plan is finite and explicit, and `DERIVE` performs no theorem search. | Internal `DerivationPlan<F>` is a finite acyclic typed graph checked independently from search. | **Retained** | Proof production remains unauthoritative and search failure remains non-semantic. |
| Closed rule bodies, exact bindings, exact substitutions, inherited assumptions, and exact arithmetic define the small checker. | The current calculus becomes one internal semantic-basis profile with a separately identified validation basis. | **Retained** | Its strong discipline survives without becoming the universal Analysis architecture. |
| The native evaluator both gives semantic meaning to the used rule and performs its validation. | `SemanticDerivationBasis` and `ValidationBasis` distinguish inference/theorem/correspondence meaning from checker implementation and trust roots. | **Split** | Same semantics checked by another implementation retain proposition meaning but receive another validation identity. |
| Native witness checking reruns the native evaluator; the Python oracle independently checks only signature and derivation skeleton boundaries. | Same-checker replay, implementation-diverse partial correspondence, and fully independent validation remain explicitly different assurance classes. | **Retained** | No current lane is promoted into a second full `DERIVE` checker. |
| External formalization receipts and surveyed absences are Evidence only. | An external proof basis requires checked external proof, subject/model correspondence, and directional statement adequacy as separately visible results. | **New** | A theorem in another system does not become a zkc proposition without the exact bridge and implication direction. |
| No native certificate or solver-result interpretation lane exists. | Certificate/solver bases bind query, polarity, theory, encoding, certificate semantics, checker, correspondence, and trust qualification. | **New** | `sat`, `unsat`, `unknown`, invalid proof, and operational failure acquire meaning only through a family rule. |
| Tests and measurements do not establish Soundness judgments. | Evidence-derived bases require a family rule connecting exact attributable Evidence records or policy-qualified appraisals, together with their retained producer observation, sampling, environment, and uncertainty contract, to an exact proposition. | **New** | Empirical observations remain epistemically distinct from exact theorems. |
| Primitive-game advantages and resource expressions remain exact and symbolic where unbounded. | A multi-sorted exact quantitative algebra admits only family-meaningful operators and retains a full loss ledger. | **Retained** | No unsupported symbolic form is silently approximated or dimension-coerced. |

### 4.5 Hypotheses, dependencies, and residual trust

| Current meaning | Target meaning | Classification | Correspondence |
|---|---|---|---|
| Premise hypotheses and canonical assumed-judgment markers inherit monotonically; no implicit discharge or Cut exists. | A canonical acyclic typed hypothesis graph records exact inheritance, introduction, discharge, substitution, and direction under family-owned rules. | **Replaced** | Explicit conditionality remains, while the target can represent checked discharge and richer dependency forms without hidden assumptions. |
| An assumed external judgment cannot be the root of a successful Protocol target derivation. | A proposition cannot be established solely by assuming itself; exact unresolved propositions remain residual hypotheses. | **Retained** | Circular self-authority remains prohibited. |
| Rule truth, binding faithfulness, model adequacy, checker correctness, and Protocol-to-concrete correspondence are described as residual trust in prose. | A finite rooted `ResidualTrustClosure` distinguishes every exact trust-root claim and dependency from logical hypotheses. | **New** | Assumptions remain in proposition meaning; checker, encoding, kernel, runtime, and definition adequacy remain in trust qualification. |
| A previously derived judgment is consumed as an evaluator value under the current context. | Established premise capabilities enter `SupportInstantiation`; proposition and semantic facts enter basis meaning, while complete owner-created `ExactCheckedResultAuthorityBinding` values and inert `OwnerCapabilityRequirement` values enter support. Portable result-record coordinates yield portable IDs; owner-local result-record references yield owner-local handles with forward-only taint. | **Split** | Dependency meaning, concrete supporting occurrence, policy authority, capability contract, and portable versus local identity are independently visible. |

### 4.6 Outcomes and negative facts

| Current outcome | Target outcome | Classification | Correspondence |
|---|---|---|---|
| One conditional `SecurityJudgment` or one typed operational refusal. | A completed affirmative or family-owned negative is distinct from `Unsupported`, `CannotAnswer`, `Refused`, `Malformed`, and `CheckerFailure`. | **Replaced** | Operational absence, invalid framing, authority failure, and semantic counterfact are no longer collapsed. |
| Failure to derive the requested judgment is a refusal. | Incomplete proof search or missing offered basis is `CannotAnswer`; it is never a semantic negative. | **Retained** | The target preserves the current refusal to manufacture falsehood from failed search. |
| The current calculus has no semantic negative payload. | A family may mint a scoped negative only from a complete direct procedure or exact checked counter-proposition/refutation relation. | **New** | Families without a sound negative schema omit the negative variant. |
| Public `SecurityJudgment` and `DerivationResult` values are re-checkable but are not opaque live capabilities. | Only a successful current checking occurrence mints a polarity- and assurance-indexed `EstablishedAnalysisJudgment` capability. | **New** | Records and IDs retain meaning but do not carry process-local authority. |

### 4.7 Family and bridge inventory

| Current surface | Target surface | Classification | Exact boundary |
|---|---|---|---|
| Soundness, Knowledge, and Completeness index families in admitted versioned combinations. | Family-owned cryptographic profiles for completeness, plain/knowledge/special/RBR/state-restoration soundness and knowledge, and zero knowledge under exact experiments. | **Split** | Shared infrastructure does not imply inheritance or conversion among property families. |
| No first-class observer-indexed equality or trace family. | `CoreEqUnderMap`, `ProtocolEqUnderMap`, `TraceEq`, and directed `TraceRefines`. | **New** | Exact maps, observer, direction, event/failure/termination model, and negative scope are proposition data. |
| No first-class intentional-change judgment. | An unauthoritative `ChangeContract` plus exact `ChangeConforms` Analysis proposition. | **New** | Declared intent alone proves neither conformance nor desirability. |
| No distributional or general cost question family. | Explicit subdistribution relations and model-indexed `CostValue`/`CostRelation` families. | **New** | Correlation, abort, termination, metric, measurement, units, and epistemic shape remain explicit. |
| The current same-artifact state-restoration-to-duplex-FS rule combines construction facts and property reasoning. | `CheckedFSConstruction` remains Stage 3 structural authority; Stage 4A separately checks theorem applicability and exposes property-specific transport ports. | **Split** | Construction validity alone establishes no cryptographic property. |
| Direct target re-analysis is the normal Compiler lane. | Direct target re-analysis remains valid beside property-specific transport. | **Retained** | Neither lane is assumed to subsume the other. |
| `PreservationClaim` is an unchecked attributed string and does not affect legality. | Exact property preservation requires an Analysis-owned `PropertyTransport` result or direct target proposition. | **Replaced** | The current non-implication is retained; the attribution is not upgraded into truth. |
| No property-composition calculus exists. | `PropertyComposition<P,Op>` consumes admitted children and target, checked structural composition, family theorem, maps, side conditions, and exact loss ledger. | **New** | Child property truth or structural composition alone is insufficient. |
| Current Relations correspondence does not establish witness satisfaction. | `RelationSatisfies` belongs to Relations and returns exact qualified occurrence-local satisfaction. | **New** | Analysis consumes the Relations capability; it does not redefine predicate truth. |
| No current satisfaction-specific capability contract or closed portable/local child-reference algebra exists. | Relations binds satisfaction to a cycle-free capability ABI/contract through the admitted operation policy and uses one closed `ExactRelationSatisfactionRef<T>` family for all localizable identity children. | **New** | Result construction, private association, capability use, disclosure, and replay are explicitly authorized; local taint follows only forward identity edges and never becomes ambient lookup authority. |
| `ArtifactJudgment` and `DerivationCoverage` check implementation-level coverage without a normative owner. | Structural owners export surfaces, Analysis expands and checks proposition coverage, and relying consumers define acceptance manifests. | **Split** | Coverage is factored into surface, proposition, coverage ledger, and reliance policy; it is not global verification. |

### 4.8 Current Analysis disagreements retained as facts

The target does not resolve a current disagreement by treating later code as
normative authority.

| Current disagreement | Target treatment | Classification |
|---|---|---|
| Security quantification is implemented, encoded, and tested but omitted from the normative index grammar. | Family profiles explicitly place every meaning-bearing parameter and quantifier; the current encoding itself receives no target authority. | **Replaced** |
| `BoundRelationAnchorCount` and `CommittedArity` are executable and registry-used but absent from the normative projection grammar. | Exact source-owned semantic and basis read closures replace both the incomplete prose list and hidden implementation extension. | **Replaced** |
| Artifact-global coverage is CLI-visible, tested, and status-used but has no normative semantic owner. | Coverage is split among the structural surface owner, Analysis family, and relying consumer. | **Split** |
| Current relation-correspondence normative and implementation wire shapes disagree. | Stage 3 relation authority and exact target relation bases are consumed; neither old wire shape is selected here. Semantic ownership is nevertheless resolved: Relations owns base satisfaction and correspondence, while Analysis owns derived property judgments and transport. | **Deferred/Outside** only for concrete wire and implementation correspondence |
| Completeness prose reads witness-in-relation meaning, but the current subject omits the exact relation/model operand. | Family-owned completeness questions include every semantically read relation, instance, satisfaction, and occurrence operand. | **Replaced** |
| Application site affects derivation but is absent from the final judgment. | Occurrence enters question or basis identity under the exact family read rule. | **Split** |
| Registry comments report 27 rules while registry and tests assert 30. | This remains minor current source-comment drift and has no target semantic role. | **Deferred/Outside** |

### 4.9 Current Analysis implementation scope

The correspondence evidence is bounded:

- current status reports partial Soundness, partial Completeness, and no
  Zero-Knowledge judgment surface;
- the live registry contains the reconstructed finite set of rules, bindings,
  indices, schemas, games, machine deciders, and proposition schemas recorded
  in [current Analysis](current-analysis.md);
- native evaluation provides exact typed rule checking, derivation witness
  replay, and artifact-level coverage for the exercised families;
- the Python oracle is implementation-diverse only for canonical signature and
  selected structural/typing skeleton boundaries, not numeric bounds or full
  `DERIVE`; and
- inspected tests are bounded examples, not theorem truth, model adequacy,
  cryptographic security, or general family support.

The reconstructed live registry inventory is 30 rules (26 admitted and four
declared), 35 direct bindings (30 reduction and five path bindings), ten
admitted index instances, three subject schemas, five primitive-game
definitions, 26 machine deciders, and 27 proposition schemas. These counts
describe the inspected checkout only; they are not a completeness claim for
Analysis or any cryptographic family.

These facts are **Deferred/Outside** the target semantic selection as
implementation coverage. They neither weaken the ideal target nor establish
that its new families or authority boundaries are implemented.

## 5. Compiler correspondence and gaps

### 5.1 Current judgments to target planes

| Current judgment | Target correspondence | Classification | Exact semantic change |
|---|---|---|---|
| `DOMAIN` validates one request and constructs a canonical finite plan set, already executing transforms, admission, lineage resolution, and derivation enumeration. | `ExplorationSpace`, frozen `ProposalScope`, total `AlternativeResolutionLedger`, semantic `CandidateDomain`, qualification-resolution ledger, and `ComparisonAlternativeDomain` are distinct. | **Split** | Discovery scope, declared alternatives, semantic image, proof-support alternatives, and comparison carrier no longer share one domain identity. |
| `REALIZE` replays a transform plan, authenticates successors, resolves lineage, and runs Soundness derivations. | Production materializes unauthoritative proposals; PIR admits every semantic target/intermediate; peer owners qualify transitions; Analysis independently checks requested properties. | **Split** | Candidate production, target admission, relation qualification, and property analysis become separate authorities. |
| `VALID` combines family legality, exact lineage, allowed Soundness surfaces, derivation success, and typed bound constraints. | Transition qualification, `CompilerLegality`, `AssessmentInputCompleteness`, qualified Analysis/peer-owner inputs, constraints, and assessment outcome are separate. | **Split** | Compiler-local policy no longer recreates relation or property meaning. |
| `SCORE` computes exact static proof bytes from authenticated proof reads and codec profiles. | Typed objective values retain provenance, knowledge shape, subject association, model, units, uncertainty, assumptions, availability, and trust. | **Split** | Static proof bytes remain one possible exact structural objective, not the objective architecture. |
| `SELECT` compares eligible candidates lexicographically and uses domain ordinal as final tie-break. | A declared comparator returns an optimal equivalence class, Pareto frontier, and only then a canonical representative under an explicit policy. | **Replaced** | Provider order, enumeration ordinal, scheduling, and discovery time are not implicit objectives. |
| `DECIDE` recomputes the same in-memory pipeline and compares the optional ordinal. | Exact decision closure, complete ledgers, full Compiler checked-result/output bindings, separately reconstructed result-use and result-minting authority, and fresh foreign owner capabilities support scoped decision checking and optional cold replay. | **Split** | Same-authority recomputation remains useful but is no longer the entire replay or decision contract. |

The current name `REALIZE` collides with the later Realization owner. In the
target, Compiler production materializes unauthoritative proposal carrier
material; Stage 3 PIR authenticates and admits Protocol meaning; Stage 4B
Realization implements fixed OIR under its own authority. The current term is
therefore **Replaced** as the architectural name for the combined Compiler
operation, without making any claim about source-level renaming.

### 5.2 Problem, request, policy, and producer

| Current object | Target object | Classification | Correspondence |
|---|---|---|---|
| `CompilerRequest` combines source artifact, comparison scope, providers, submitted plans, target lineage, Soundness surfaces, constraints, objectives, and limits. | `TransformProblem`, `DecisionPolicy`, and `CompileRunRequest` separately identify transition meaning, comparison meaning, and one operational attempt. | **Split** | Producer choice, limits, seeds, and worker state cannot change transform or policy semantics. |
| Transform-domain and derivation-domain providers determine the candidate plan space. | Replaceable `SearchJob` and recipes produce proposals; exact proposal/domain policies define only the scoped claims they are authorized to make. | **Replaced** | Provider search is operational production, not semantic domain authority by itself. |
| Closed-domain and submitted-frontier modes bound comparison claims to an exact declared scope. | Every target decision or report remains indexed by its exact declared candidate and comparison scope. | **Retained** | No current or target mode implies a global optimum over all legal Protocols. |
| The current Compiler has only closed-provider and submitted-frontier comparison modes. | Submitted-candidate, resolved-proposal, enumerated-closed, certified-symbolic, and open-exploration forms have distinct closure contracts and decision strengths. | **New** | Additional domain forms do not inherit completeness from a producer label. |
| Bounds alter the exact current domain; providers may not silently use them as cost-policy pruning. | Exploration bounds, proposal-scope bounds, candidate-domain closure, constraints, and objective policies occupy explicit planes. | **Split** | Every bound affects only the identity and claim of the plane that declares it. |
| Search and checker behavior are deterministic for the current configured provider. | Production may be heuristic, parallel, interruptible, mutable, nondeterministic, or absent without acquiring decision authority. | **New** | Determinism is required for exact declared scopes and decisions, not for unauthoritative discovery. |

### 5.3 Proposal, admission, relation, and legality

| Current object or operation | Target object or operation | Classification | Correspondence |
|---|---|---|---|
| A transform family combines `recognize`, deterministic `realize`, and `check`. | `TransformIntent`, `ProposalRecipe`, `ProposalOccurrence`, PIR admission, peer-owned transition proposition, and `CompilerLegality` are distinct. | **Split** | A deterministic producer function is not the semantic definition of every valid transition. |
| The same-point KZG provider reopens an admitted predecessor, mutates PIR, seals, snapshots, admits, and wraps the target. | Proposal production emits unauthoritative material; PIR alone authenticates and admits each whole target and semantic intermediate. | **Replaced** | Admission establishes Protocol validity only, not transform relation, eligibility, or selection. |
| The KZG checker independently repeats the transform and compares successor identity. | Each exact predecessor/successor relation is checked by its semantic owner with explicit proposition, polarity, basis, maps, and capability. | **Split** | Current replay remains bounded evidence, while a first-class qualified transition result becomes the target dependency. |
| `ClaimCorrespondence` records exact retained, removed, introduced, split, merged, and surviving lineage. | Typed lineage and occurrence maps remain checked witnesses inside exact semantic paths and transition cases. | **Retained** | A lineage map alone establishes neither relation truth nor property transport. |
| Current `LEGAL` is the accepted family-local transform trace. | Peer-owned transition results establish semantic relations; `CompilerLegality` checks only problem-local policy such as permitted families, path shapes, and parameter ranges. | **Replaced** | `Illegal` is not a negative Protocol relation or property result. |
| `PreservationClaim` is collected after checking and never affects legality. | Eligibility can consume only exact Analysis property transport or direct target result required by policy. | **Replaced** | The current attribution remains a nonclaim and supplies no target capability. |
| A source baseline is tied to the candidate through checked claim lineage. | Every fact used to assess a candidate retains an exact checked subject association to that candidate under the owning policy schema. | **Retained** | Cross-candidate or unrelated facts cannot price or qualify a candidate. |

### 5.4 Alternative resolution and candidate identity

| Current object or behavior | Target object | Classification | Correspondence |
|---|---|---|---|
| One `CompilerPlan` structurally combines transform choices and exact Soundness derivation choices. | Recipe, proposal occurrence, declared alternative, semantic path, transition case, qualification, candidate, comparison alternative, and assessment all have distinct identities. | **Split** | Operational production and proof-basis choices do not silently define semantic candidate identity. |
| Two plans may reach the same artifact but remain separate domain members because their derivation choices differ. | `CandidateId` is transform problem plus exact transition case; qualification multiplicity is represented separately and enters comparison only through explicit policy. | **Replaced** | Proof choice distinguishes qualifications, not semantic candidates, unless policy explicitly compares qualified alternatives. |
| Candidate artifact IDs cannot appear in the request before realization. | Policy names schemas and association rules; concrete candidate-associated qualifications enter a post-candidate qualification-only projection, while other facts enter a separate immutable assessment portfolio. | **Retained** | No future result record is named before the candidate exists, and unrelated assessment inputs cannot alter qualification resolution or `Q`. |
| Domain ordinal is request-local identity and the final tie-break. | Canonical semantic identities cover proposal scope, alternative, transition case, candidate, qualification, comparison alternative, assessment, and decision. | **Replaced** | Ordinal may remain an ordering coordinate inside a scope but is not durable candidate or decision meaning. |
| Domain construction may discard a transform with no derivation alternatives or refuse the whole domain on operational failure. | Every declared alternative receives a total explicit resolution: resolved, duplicate, conclusively excluded, or an exact unresolved outcome. | **New** | Missing or failed semantic work remains visible and blocks a closed originating-scope claim when required. |
| Equal target IDs, equal scores, or provider deduplication can collapse operational work in current provider-specific ways. | Candidate quotienting requires an exact checked proof of irrelevance to every constraint, objective, dependency, replay obligation, consumer, and later input. | **New** | Target equality alone is not a semantic path quotient. |
| Current survivor matching uses descriptor digest plus canonical claim order after replay. | Family-owned exact relations and lineage maps define transition meaning. | **Deferred/Outside** | The current matching rule remains provider-specific evidence; its adequacy for unrelated families is unestablished. |

### 5.5 Candidate and comparison domains

| Current domain fact | Target domain fact | Classification | Correspondence |
|---|---|---|---|
| The provider enumerates a finite canonical closed plan domain or checks a submitted frontier. | `CandidateDomainPolicy` and exact closure proposition identify a canonical finite admitted, transition-qualified semantic candidate set. | **Split** | Producer enumeration and semantic-domain closure become different claims. |
| Domain completeness is trusted through the exact provider contract and checked recomputation. | A `CheckedCandidateDomain` capability requires explicit membership, admission, relation, uniqueness, ordering, image, quotient, finiteness, and coverage facts for the selected domain form. | **New** | A list, digest, solver status, or persisted prior result does not establish closure. |
| One plan domain is also the scoring carrier. | Qualification resolution derives a separate `ComparisonAlternativeDomain` from the semantic candidate domain and policy. | **New** | Basis multiplicity can be resolved or compared without mutating candidate identity. |
| Current derivation alternatives are already members of the plan domain, and there is no separate support-resolution result over semantic candidates. | A checked qualification-only input projection freezes every exact qualification origin/policy/capability requirement; `QualificationResolutionLedger` records one resolution entry for every `CandidateId`, and `ComparisonAlternativeDomain` contains every and only accepted `(CandidateId, CanonicalQualificationSetId)` operands. | **New** | An undetermined or incompletely enumerated support entry blocks a closed decision; an unrelated local assessment input does not localize resolution or `Q`. |
| Current derivation-plan choice is fixed in the exact plan before candidate scoring. | `QualificationResolutionPolicy` is fixed by policy, and each `ComparisonAlternativeId` fixes the exact qualification or corroborating set used by its later assessment. | **Retained** | A convenient proof basis cannot be selected after observing objective values. |
| Current domain equality and recomputation cover the plan domain but do not establish a second qualification-aware comparison carrier. | `ComparisonAlternativeDomainClosureProposition` separately checks total candidate coverage, qualification-policy conformance, canonical expansion, uniqueness, and projection to one semantic candidate. | **New** | Candidate-domain closure, qualification resolution, and comparison-domain closure are independent capabilities. |
| Current closed-domain construction already performs semantic work and later stages rerun it. | Production, total alternative resolution, semantic-domain closure, assessment, and replay are independently identified. | **Split** | Repeated work and cache strategy are operational issues; no cached value becomes authority. |
| Submitted-frontier best means best only in the exact submitted set. | `BestInSubmittedCandidateSet` retains the exact submitted-domain scope and qualification domain. | **Retained** | Submitted scope never implies all legal candidates were considered. |
| There is no current open-search report distinct from a submitted frontier. | `OpenExploration`, feasible-candidate reports, assessed-subset reports, and incomplete-search reports preserve useful partial results without closed-domain claims. | **New** | An empty heuristic search is not `NoEligible`. |
| Symbolic closed domains are not current Compiler semantics. | `CertifiedSymbolicCandidateDomain` may compress exact already materialized, admitted, and transition-qualified finite images under checked denotation and closure. | **New** | It cannot grant ordinary candidate authority over unnamed or unadmitted targets. |
| Lazy universally quantified semantic candidates are not supported by frozen Stage 3 authority. | Such a model requires a separately reviewed Stage 3 reopening. | **Deferred/Outside** | It is not a v0 target claim. |

### 5.6 Assessment, constraints, and objectives

| Current behavior | Target behavior | Classification | Correspondence |
|---|---|---|---|
| Compiler owns Soundness context, derivation domains, allowed rule/game/hypothesis surfaces, and bound expression evaluation. | Compiler forms a qualification-only projection and candidate-indexed `AssessmentInputPortfolio` of complete owner-created admitted-subject and checked-result authority bindings, authenticated policy dispositions/closures, association material, and inert `OwnerCapabilityRequirement` values; required fresh live capabilities remain separate checking inputs. | **Replaced** | Analysis meaning is not reconstructed inside Compiler, and neither inert body carries peer-owner authority. |
| Current request/context fields and realized candidate jointly supply assessment inputs; there is no independently identified immutable portfolio body. | `AssessmentInputPortfolio` content-identifies the exact candidate reference, including its transition case and admitted target, plus exact candidate-associated Analysis/peer-owner, Stage 4B, Evidence, qualification, origin, policy, capability-requirement, and association records supplied for one policy; local inputs produce a nonpersistable Compiler handle. | **New** | The body contains concrete post-candidate records and requirements but neither live capabilities nor a self-asserted completeness fact, and no checker must dereference an ambient candidate ID. |
| Current `VALID` checks the supplied surfaces directly and has no separate completeness proposition over its input collection. | `AssessmentInputCompletenessProposition` binds the portfolio and policy and states exact coverage, uniqueness, association, polarity, assurance, complete source-authority-binding, immediate/transitive policy, inert capability-requirement, and residual-trust acceptance. | **New** | The proposition is distinct from both the portfolio it checks and the later completed result. |
| Current validation has no separately qualified completion result for its input collection. | A completed affirmative `AssessmentInputCompletenessResult` and its live capability satisfy that proposition and become inputs to `CandidateAssessment`. | **New** | Completeness is relative to the exact policy and never a field by which the portfolio authorizes itself. |
| Current lineage-scoped baseline checks associate selected Soundness values inside the monolithic validation stage. | Each concrete independent peer- or later-owner fact whose subject association must be established receives an `AssessmentInputUse` over the exact policy and portfolio references and one canonical typed slot; the check records unique body membership plus exact candidate, target, and policy association. | **Split** | The independent fact retains its own identity and cannot contain or depend on the later `AssessmentId`; an ID or coordinate is never treated as lookup authority. |
| `VALID` reruns `DERIVE` for every target and evaluates exact candidate-versus-lineage-baseline constraints. | Direct re-analysis and property transport may provide the same proposition through distinct qualifications; constraints check claim meaning and accepted basis/trust policy separately. | **Split** | Direct candidate analysis remains a valid lane without being the only lane. |
| Current typed bound algebra covers scalar, extraction-failure, exact-round, and round-maximum projections with exact operations. | Typed constraints cite exact proposition pattern, polarity, model, hypothesis/bound predicate, dimension, assurance, and trust acceptance. | **Retained** | Exact arithmetic remains; unsupported dimensions or coercions remain explicit. |
| Candidate-local derivation, bound, or objective failure becomes one internal `CandidateIneligible`; operational failures abort. | Assessment yields `Eligible`, `DefinitivelyIneligible`, or `Undetermined` with exact facts or blockers. | **Replaced** | Missing data, unsupported analysis, refusal, malformed support, and checker failure cannot become semantic ineligibility. |
| Selection discards per-candidate ineligibility reasons. | `AssessmentLedgerId` covers every comparison alternative and retains decisive results or exact unresolved blockers. | **New** | Closed decisions expose their complete basis. |
| The only objective is exact static verifier proof bytes. | Objectives retain provenance and knowledge shape, including exact values, proved bounds, intervals, symbolic expressions, estimates, and categories. | **Split** | Static proof bytes remain one direct structural value; measured and modeled quantities cannot masquerade as exact values. |
| Missing objective data makes the candidate ineligible. | Missing required objective information is `Undetermined` unless an explicit availability preference is itself policy. | **Replaced** | Missing is not implicit infinity. |
| Lexicographic comparison with an exact final tie rule is total and deterministic. | Every target comparator and representative rule is exact, declared, and deterministic within its supported comparison shape. | **Retained** | Provider scheduling, cache state, and discovery time remain non-authoritative. |
| The current comparator does not retain an optimal equivalence class or Pareto frontier and does not offer weighted or constrained comparison profiles. | Weighted, constrained, Pareto, optimal-equivalence, and separate canonical-representative semantics are explicit policy forms. | **New** | Tied optima and partial orders are not erased by an implicit provider ordinal. |

### 5.7 Decisions and outer outcomes

| Current result | Target result | Classification | Correspondence |
|---|---|---|---|
| `CompilerResult` contains a selected domain ordinal or `no_selection`. | `CompilerDecision` binds problem, policy, closed candidate and comparison domains, resolution and assessment ledgers, comparison result, selected qualification, exact assessment- or certificate-derived member support, derivation basis, and residual trust. | **Replaced** | The inert decision record is content-identifiable and independently reconstructible from its exact replay basis; authority still requires a fresh qualified checking occurrence. |
| The current in-process result can retain its selected target material without a distinct portable handoff contract. | A portable `CompilerDecision` identifies but does not carry the selected target; a separate `CompilerSelectedTargetHandoffBundle<D,Q>` retains the exact decision support, candidate equality path, canonical PIR carrier/reconstruction material, and exact Stage 4B consumer/purpose authorization. | **Split** | Decision replay does not authorize cold handoff, and Stage 4B must still independently readmit the target; local dependencies, missing material, or policy denial yield no bundle. |
| `no_selection` means no member survived the current exact assessment pipeline. | `NoEligibleCandidateIn<D,Q>` requires complete domain and qualification accounting, total assessment accounting, checked sufficiency, and exact qualification- or assessment-derived exclusions or a matching independently checked infeasibility certificate. | **Replaced** | Unsupported, cannot-answer, refusal, malformed input, missing objective, or checker failure cannot establish `NoEligible`. |
| Current compilation has candidate-local ineligibility and otherwise returns success or generic error. | Closed decisions, open reports, and outer `Unsupported`, `CannotAnswer`, `Refused`, `Malformed`, and `CheckerFailure` remain distinct. | **New** | Proposal-local facts and whole-operation outcomes retain their exact scope. |
| Current decision reports one winning ordinal even across equal scores. | A closed best result retains the full optimal equivalence class plus an explicitly selected canonical representative and qualification set. | **New** | Representative choice does not erase other tied optima. |
| Current decision makes no claim beyond closed domain or submitted frontier. | Every best, Pareto, and no-eligible capability is indexed by exact candidate and comparison-alternative domains. | **Retained** | No global optimality claim is introduced. |
| No current Pareto or qualified incomplete-report surface exists. | Complete Pareto frontiers and explicitly subset-relative open reports have separate decision strength. | **New** | Partial orders and incomplete search cannot silently yield one closed optimum. |

### 5.8 Current Compiler configuration conflict

The current normative specification and implementation disagree on an exact
identity preimage:

```text
normative ExactRef
  {"id": "...", "source_revision": "..."}

C++ and Python parity twin ExactRef
  ["...", "..."]
```

The specification also declares generic compiler family/domain tags, while
the C++ implementation and Python twin use the implemented same-point-KZG
family/domain tags. The relevant current surfaces are
[`docs/spec/compiler.md`](../../../docs/spec/compiler.md),
[`lib/Compiler/PirCompilerProvider.cpp`](../../../lib/Compiler/PirCompilerProvider.cpp),
[`reference/oracle/compiler.py`](../../../reference/oracle/compiler.py), and
the [configuration parity test](../../../test/Compiler/compiler-config-parity.test).

The parity test establishes C++/Python agreement, not conformance to the
normative preimage. This is a real current specification/implementation
conflict. Its target classification is **Deferred/Outside**: the repaired
target uses the general Stage 1--3 domain-separated canonical semantic identity
rule, but this inventory neither selects a repaired current encoding nor treats
either conflicting current spelling as target authority.

### 5.9 Current Compiler implementation scope

Current implementation correspondence is limited to:

- an artifact-neutral in-process checked-search library;
- one substantive bounded same-point-KZG transform/domain provider;
- exact static proof-byte scoring;
- same-authority `DECIDE` recomputation;
- test-only Compiler passes rather than an installed production Compiler
  command; and
- a Python twin for configuration-digest parity, not an independent Compiler
  decision implementation.

The focused current Compiler suite passed four of four tests during the
reconstruction. It covers bounded closed/submitted domains, exact derivation
alternatives, typed constraints, lineage, deterministic ties, no selection,
decision recomputation, and one- and two-group KZG fixtures. This evidence is
**Deferred/Outside** target semantics: it does not establish general domain
completeness, Compiler correctness, additional transform families, persistent
replay, Stage 4B integration, or implementation of the target planes.

## 6. Shared authority and trust correspondence

| Current shared boundary | Target shared boundary | Classification | Correspondence |
|---|---|---|---|
| Admitted PIR artifacts or exact `ArtifactSemantics` reconstruct semantic views before evaluation. | Every semantic owner authenticates and admits its subjects, emits only attenuated owner-created views, atomically creates an inert exact admitted-subject or checked-result authority binding for every exported capability, and supplies the fresh live capability separately. | **Retained** | IDs, carrier bytes, snapshots, view-shaped values, and inert bindings do not self-authenticate. |
| Current public Analysis and Compiler results are owned values whose provenance is checked only by rerunning exact inputs. | Semantic values, result records, checking occurrences, live capabilities, replay bundles, and audit records are separate categories. | **Split** | Serialization preserves inert meaning and replay inputs, never authority. |
| One configured evaluator/provider set determines both original result and recomputation. | Semantic basis, validation basis, assurance class, support instantiation, and residual trust are explicit and independently identified. | **Split** | Producer distrust is retained without mislabeling same-checker recomputation as implementation independence. |
| Soundness residual trust is documented but not one canonical result field. | Every completed Analysis result and decisive Compiler result carries an exact finite rooted `ResidualTrustClosure`. | **New** | Trust is not compressed into a project name, assurance rank, or “machine checked” label. |
| Exact assumptions are inherited in the current Soundness result. | Logical hypotheses remain part of proposition identity and cannot be moved into residual-trust metadata. | **Retained** | Consumer trust acceptance never changes the proposition. |
| Provider configuration, objective profiles, and selected contexts are exact inputs. | Every semantic or operational input enters only the identity of the category whose meaning it affects. | **Split** | Search state and checker implementation do not contaminate semantic question or candidate identity. |
| There is no generic current live checked-occurrence capability. | Owner-issued polarity-, family-, assurance-, and scope-indexed capabilities form an explicit dependency chain. | **New** | No erased super-capability permits substitution across property, relation, assurance, or decision classes. |
| Current consumers may receive result-shaped data directly. | Attenuated consumer views preserve exact proposition, polarity, hypotheses, assurance, and trust closure. | **New** | A consumer cannot widen or reinterpret another owner's result. |
| Current Relations results have no complete common permission decomposition for derived records. | The correspondence capability contract independently governs invocation/capability use, completed-result creation and portable identity or private association plus retention/disclosure, attempt-audit creation/identity/retention/disclosure, and reconstruction/replay; each applicable gate also checks every disposition in the transitive source-policy closure. | **New** | Allowing an invocation or audit does not authorize a durable result or replay, and a source policy can prohibit derived stable retention. |

The target Compiler authority chain is consequently factored:

```text
checked TransformProblem + checked DecisionPolicy
  -> optional CheckedCompileRunRequest when a run-request producer lane is used
  -> frozen ProposalScope from run, direct submission, or finite grammar
  -> per-alternative PIR admission + CheckedTransition<F> or terminal accounting
  -> QualifiedCandidate for every affirmatively admitted and transitioned case
  -> checked CandidateDomainPolicy and every required CandidateQuotient
  -> total AlternativeResolutionLedger
  -> CheckedCandidateDomain<D>
  -> CheckedQualificationResolution<D>
  -> CheckedComparisonAlternativeDomain<Q>
  -> CheckedCandidateAssessment<D,Q> for every Assessed entry
  -> CheckedAssessmentClosure<D,Q> when exact decision sufficiency is established
  -> QualifiedCompilerDecision<D,Q>

checked DecisionPolicy
  + any exact reached qualified subset
  + every exact reached closure result the report actually reads
  + audit/not-attempted/blocker accounting for every claimed slot
  -> QualifiedCompilerOpenReport<R>
```

No later capability substitutes for an earlier one. In particular, the final
decision establishes only its exact scoped comparison claim; it does not mint
Protocol admission, transition truth, property truth, Stage 4B facts, or
consumer reliance. A qualified open report establishes only its exact bounded
subset and audit-record-relative accounting statement, never a closed decision.
It does not require `CheckedCandidateDomain<D>`,
`CheckedComparisonAlternativeDomain<Q>`, total qualification resolution, total
assessment accounting, or `CheckedAssessmentClosure<D,Q>` unless it explicitly
reads one of those already reached results as part of its own exact claim.

## 7. Shared outcome correspondence

| Current collapse | Target distinction | Classification | Consequence |
|---|---|---|---|
| Analysis has conditional success or typed refusal. | Family-owned affirmative/negative completion plus unsupported, cannot-answer, refused, malformed, and checker-failure attempts. | **Replaced** | Negative exists only where an exact complete procedure or counter-proposition supports it. |
| Compiler turns several derivation/bound/objective failures into `CandidateIneligible`. | Alternative resolution, qualification resolution, constraint results, and candidate assessments retain conclusive exclusion separately from unresolved blockers. | **Split** | Operational absence is never semantic exclusion. |
| Other Compiler failures abort with generic error. | Proposal-local resolution outcomes and whole-operation qualified outcomes retain location and semantic scope. | **New** | One bad alternative need not be confused with a malformed or failed decision claim. |
| `no_selection` is a successful optional-ordinal result. | Closed `NoEligibleCandidateIn<D,Q>` and open empty/incomplete reports are separate. | **Replaced** | Only complete exact exclusion over both closed domains supports the negative decision. |
| A failed proof or certificate has no independent semantic category. | Invalid support is a fact about that support; it negates the intended proposition only through an exact family refutation rule. | **New** | Checker rejection cannot be cast into property falsehood. |
| Current diagnostics carry useful phase, code, location, and detail. | Operational records retain exact unsupported inputs, blockers, authority failures, malformed fields, and checker boundaries. | **Retained** | Qualification adds semantic separation without discarding exact diagnostics. |

## 8. Replay, persistence, and cache correspondence

### 8.1 Analysis

| Current replay or persistence | Target replay or persistence | Classification | Correspondence |
|---|---|---|---|
| `zkc-derive --check` reloads artifact, checker-supplied signature, request, and plan, reruns the native evaluator, and compares the judgment digest. | Cold Analysis replay reauthenticates subjects, recreates source-owned views, checks correspondence, reruns the exact semantic derivation through the selected validation basis, and mints a fresh capability. | **Retained** | Native witness replay remains a valid same-checker lane, not independent theorem or model assurance. |
| Persisted witness embeds request and plan while using whole-signature and conclusion digests. | Optional `AnalysisReplayBundle` separates question, proposition, request, semantic basis, validation basis, derivation, expected result, trust, disclosure, consumer, and purpose. | **Split** | Unused registry content and checker occurrence do not become proposition identity. |
| Rechecking can report signature mismatch while rederiving an equal judgment under another signature. | Replay requires exact expected proposition and qualified-result equality under the declared bundle and basis identities. | **Replaced** | Claim equality and basis drift remain distinct facts. |
| Cheap derivations may still be persisted by current tooling. | Cheap direct checks are recomputed by default; persistence is justified only by a named consumer, expensive reconstruction, or real trust separation. | **Replaced** | Persistence is optional policy, not proof authority. |
| Secret or sensitive replay policy is not a general current Analysis contract. | Family policy may prohibit public persistence or require a confidential replay owner; public bundle IDs exclude secret equality or witness authority. | **New** | Public content addressing does not create a secret-value oracle. |

### 8.2 Compiler

| Current replay or persistence | Target replay or persistence | Classification | Correspondence |
|---|---|---|---|
| PIR artifacts can be persisted and re-admitted. | Every replay independently reconstructs and reauthenticates targets and intermediates and obtains fresh PIR admission. | **Retained** | Persisted artifact bytes never serialize `AdmittedProtocol` authority. |
| KZG transform replay repeats the same family operation and compares successor identity. | Transition replay restores exact semantic path material and rechecks each peer-owned transition basis. | **Split** | Producer reproducibility, transition truth, and target admission remain different facts. |
| `DECIDE` recomputes only when the same in-memory request, context, provider behavior, and order are supplied. | In the fully portable lane, `CompilerReplayBundle` retains exact problem, policy, proposal scope where read, total resolution, domains, qualification projections, assessments, peer inputs, origins, every bound-policy or explicit no-policy owner capability-contract and ABI preimage, comparison, decision, and trust. | **Replaced** | Cold replay does not rerun a mutable producer or rely on an ordinal; a local confidential lane instead creates fresh handles and has no exact replay. |
| No persistent request, domain, plan, proposal, candidate, assessment, decision, or replay schema exists. | Exact category-specific IDs and an optional consumer-named replay bundle make the scoped decision independently reconstructible. | **New** | Persistence remains optional and never carries live authority. |
| Current result exposes only selected ordinal or none. | Replay retains the selected semantic candidate, qualification set, exact assessment- or certificate-derived member support, optimal class/frontier, derivation basis, and all decisive domain facts. | **Replaced** | The selected object is meaningful independently of provider enumeration order. |

### 8.3 Caches and occurrences

| Current surface | Target surface | Classification | Correspondence |
|---|---|---|---|
| No authoritative persistent cache model is defined. | Producer-search, semantic-replay, Evidence, and process-local authority caches are separate. | **New** | Persistent hits are hints until exact owner revalidation; only same-lifetime memoization may reuse a still-live capability. |
| Process or replay occurrence is not a distinct semantic identity. | `ReplayOccurrenceHandle` is fresh, local, and nonserializable; optional `AuditEventRecordId` is inert. | **New** | Repeated checking does not change proposition or decision identity. |
| Basis or provider drift may prevent current recomputation. | Basis drift makes cached or replay material stale but does not by itself make the underlying proposition false. | **New** | Semantic truth, replayability, and current authority remain separate. |

## 9. Stage 4B, Evidence, and reliance seams

### 9.1 Stage 4B peer boundary

| Stage 4A relationship | Target boundary | Classification | Exact consequence |
|---|---|---|---|
| Current static proof-byte scoring is an exact structural computation over authenticated proof reads and codec profiles; it reads no OIR or endpoint fact. | Static proof bytes remain expressible as `DirectStructural` objective data rather than a `Stage4BOwnedFactOrValue`. | **Retained** | Structural objective provenance is not relabeled as later-owner authority. |
| Current Compiler `REALIZE` means Protocol-semantic candidate construction, while later Realization means OIR implementation. | Compiler production is unauthoritative proposal materialization; Stage 4B owns OIR projection, local validity, realization, target/supplier binding, endpoint feasibility, invocation, and execution. | **Replaced** | Stage 4A defines none of those Stage 4B judgments. |
| No current candidate-indexed Stage 4B association contract exists. | A later-owned fact binds its exact candidate target Protocol and every later-owned operand; `AssessmentInputUse` separately associates it to candidate and policy. | **New** | The later-owned fact contains no `AssessmentId`, avoiding an identity cycle and Compiler-policy dependence. |
| The prospective relation-to-OIR seam previously named only a relation operand, capability, and read set. | A future relation-facing OIR transition must receive the exact admitted `RelationInterface` or exact affirmative correspondence value and complete admitted-subject or checked-result authority binding, inert capability requirement, authenticated owner-policy/no-policy disposition and total source-policy closure, separately fresh matching capability of the same affirmative polarity, and exact OIR consumer/purpose authorization. | **Replaced** | An ID, capability name, negative result, or read set alone cannot authorize OIR consumption; the seam remains dormant until Stage 4B selects its operation contract and result. |
| Current candidate identity is plan/ordinal-relative. | `CandidateId` remains a Protocol-transition identity and is not widened into an OIR, realization, deployment, or endpoint alternative. | **Retained** | Several Stage 4B alternatives require explicit later-owned choice/aggregation or a future product-domain owner. |
| Stage 4B may be consulted as peer pressure during Stage 4A research. | Stage 4B remains unactivated and its exact normative model is not defined here. | **Deferred/Outside** | This inventory records only the seam required to keep Stage 4A semantics independent. |

Projection, realization, and endpoint meaning are invariant under Compiler
history. Two decisions that identify the same admitted target cannot change a
Stage 4B result merely because they used different producers, proposal scopes,
semantic paths, objectives, or selection histories.

### 9.2 Evidence boundary

| Current surface | Target boundary | Classification | Exact consequence |
|---|---|---|---|
| Citations, formalization receipts, tests, benchmarks, traces, and measurements are non-authoritative evidence. | Producing domains retain the meaning of raw observations; Evidence owns their attributable records, provenance, procedure, environment, samples, uncertainty, and policy-qualified appraisal. | **Retained** | Recording evidence never mints an Analysis proposition or Compiler decision. |
| Current Compiler has no general Evidence-derived objective schema. | Analysis may derive an `AnalysisEvidenceDerivedEstimate` through an exact Analysis family rule over qualified Evidence inputs; Compiler may separately consume an Evidence-owned `EvidenceQualifiedEstimate` under declared policy. | **New** | Owner binding, epistemic shape, and candidate association remain visible; the two estimate types are not interchangeable. |
| Static exact and measured values have no shared general target type today. | Objective provenance and knowledge shape distinguish direct structural, Analysis-owned model/Evidence-derived, Evidence-qualified, Stage 4B-owned, and declared-policy values. | **New** | A measured estimate is not relabeled as an exact semantic theorem. |

### 9.3 Reliance boundary

| Current surface | Target boundary | Classification | Exact consequence |
|---|---|---|---|
| Current artifact coverage and Compiler selection can be consumed without a first-class consumer manifest. | A named relying consumer defines exact required proposition patterns, hypotheses, bounds, assurance, trust-root acceptance, and purpose. | **New** | Analysis coverage and Compiler decisions do not themselves establish consumer acceptance. |
| Current status and tests report bounded exercised behavior. | Release readiness, deployment acceptability, security acceptance, and policy reliance remain consumer-owned decisions. | **Deferred/Outside** | Neither a qualified property nor a selected candidate is a global verified/releasable state. |
| Current records may exist without a named durable consumer. | Persistent replay is optional and names its consumer, purpose, and disclosure policy. | **Replaced** | Durability is not introduced solely because a semantic value can be serialized. |

### 9.4 Extension boundary

| Current extension behavior | Target extension law | Classification | Exact consequence |
|---|---|---|---|
| Current Soundness rules and bodies are closed, typed, versioned catalog entries rather than arbitrary callbacks. | Family semantic profiles and basis registries remain closed where meaning or inference changes. | **Retained** | Registration alone cannot introduce a property, model, negative meaning, rule, or capability cast. |
| Current configured providers and families extend one in-process Compiler context and jointly affect its exact behavior. | Producers, search algorithms, proof producers, schedules, and caches are open operational mechanisms when semantic contracts remain unchanged. | **Split** | Operational extensibility does not alter a transform problem, Analysis proposition, candidate, or decision policy. |
| Another checker implementation has no general separate current validation identity. | A checker authenticated against an unchanged contract receives its own `ValidationBasisId` and trust closure without changing proposition meaning. | **New** | Implementation diversity is represented without semantic reinterpretation. |
| Unknown exact references or unsupported current operations refuse under their local APIs. | Unknown semantic family, model, relation, comparator, or certificate tags are `Unsupported` under closed versioned profiles. | **Retained** | Dynamic callbacks cannot acquire semantic authority through lookup. |
| Cross-version semantic reuse has no general current Analysis/Compiler rule. | Reuse across semantic regimes requires an exact checked interpretation or transport proposition. | **New** | Existing identities are never silently reinterpreted after profile revision. |

## 10. Semantic non-correspondences and deliberate deferrals

The following scope boundaries distinguish what Stage 4A now specifies from
what it explicitly leaves outside or deferred:

| Subject | Classification | Boundary |
|---|---|---|
| Truth of cryptographic assumptions, rule bodies, or imported theorems | **Deferred/Outside** | Analysis records exact hypotheses, basis, correspondence, and trust; it does not prove every root. |
| Correctness or completeness of a concrete checker implementation | **Deferred/Outside** | A validation basis and residual-trust closure identify the claim and assurance; this target does not establish it. |
| Implementation organization, APIs, storage format, migration, backward compatibility, and effort | **Deferred/Outside** | They are expressly absent from this semantic inventory. |
| A production Compiler command or general transform-provider implementation | **Deferred/Outside** | Current scope is the in-process library and bounded KZG provider; target semantics report no implementation support. |
| Global optimality over all legal Protocols | **Deferred/Outside** | Every decision remains indexed by one exact closed candidate and comparison domain. |
| A closed negative from incomplete proof search, candidate search, assessment, or solver `unknown` | **Deferred/Outside** | Only a complete exact procedure, closure proof, or checked counter-proposition can support the corresponding negative. |
| Durable semantic-specification ownership for `RelationSatisfies` | **New** | Relations now owns and durably specifies the target operation, occurrence-local confidential semantics, exact capability ABI/contract, and portable/local reference law; Analysis may consume the exact result but does not redefine it. |
| Concrete `RelationSatisfies` implementation, checker profile, and implementation correspondence | **Deferred/Outside** | The durable target reports no implementation support or concrete checker correctness. |
| OIR, projection, OIR validity, realization, target/supplier binding, endpoint feasibility, deployment, invocation, and execution | **Deferred/Outside** | These are outside Stage 4A; Stage 4B owns their meanings after its separate activation. |
| Consumer acceptance, release readiness, and a global `ArtifactVerified` state | **Deferred/Outside** | Exact relying consumers own their policies; no universal approval capability exists. |
| Lazy authority over unnamed or unadmitted symbolic candidates | **Deferred/Outside** | It is outside v0 and requires a separately reviewed Stage 3 authority reopening. |
| Persistence of live capabilities | **Deferred/Outside** | It is excluded by construction: serialization carries only inert values and replay material; fresh owners mint fresh capabilities after rechecking. |

## 11. Complete retained invariant set

Across all splits and replacements, the target retains the following current
semantic disciplines:

1. Analysis operates only after exact upstream admission.
2. Producer reports, attributed preservation strings, theorem names,
   citations, scores, and persisted bytes are never semantic authority.
3. A finite typed and reviewable source-read vocabulary is retained as the
   current intention; complete purpose-specific source-owned semantic and
   basis closures are a target strengthening.
4. Proof and plan production remain separate from small exact checking.
5. Unsupported arithmetic or semantics refuse rather than approximate or
   coerce silently.
6. Subjects, notions, models, occurrences, hypotheses, results, maps, and
   quantitative dimensions remain explicit.
7. Conditional results retain every unresolved hypothesis.
8. Multiple derivations may support one proposition without changing its
   meaning.
9. Every semantic successor is independently admitted before later semantic
   consumption.
10. Immediate predecessor/successor relationships and lineage are checked
    over actual semantic intermediates.
11. Property truth is never inferred from structural relation, construction,
    lineage, or unchecked preservation attribution alone.
12. Comparison scope is finite, exact, and named; no bounded optimum is
    widened globally.
13. Candidate-local exclusion and whole-operation failure remain distinct.
14. Decision derivation--whether deterministic assessment comparison or exact
    certified-payload extraction--never trusts producer-populated scores or
    selection.
15. Selection and nonselection claims never exceed their exact declared
    domain; the target strengthens a negative `NoEligible` claim with complete
    domain and exclusion support.
16. Rechecking reconstructs semantic inputs and never treats a prior record or
    digest as live authority.
17. Same-checker replay, implementation-diverse correspondence, theorem truth,
    model adequacy, and consumer reliance remain different claims.

## 12. Inventory conclusion and absorption contract

The current system is not mapped to the target as a single component. Its
strongest invariants are retained, while its joined roles are separated:

```text
current Soundness Kernel
  -> one internal Analysis family/basis profile
  + exact question/proposition/result lifecycle
  + additional family-owned semantics and checking lanes

current checked Compiler pipeline
  -> exact problem and decision policy
  + replaceable unauthoritative production
  + frozen proposal scope
  + per-alternative PIR-owned admission and peer-owned relation qualification
  + total alternative resolution
  + semantic candidate and qualification-aware comparison domains
  + total assessment accounting, checked sufficiency, and decision ledgers
```

The direct current conflicts remain visible rather than being resolved by
preference for code: Analysis quantification and projection drift, unowned
coverage and occurrence surfaces, relation-correspondence disagreement,
underclosed Completeness subjects, and the Compiler exact-reference/tag
encoding conflict.

The target adds semantic architecture, not implementation claims. In
particular, current tests, tools, the partial Python oracle, and the bounded
same-point-KZG provider establish only the exercised current correspondence
recorded above.

At Stage 4A convergence, reviewed **Retained**, **Split**, **Replaced**, and
**New** conclusions belong in their exact durable semantic owners. Reviewed
**Deferred/Outside** boundaries belong in the appropriate Stage 4B handoff,
Evidence/reliance contract, decision record, or explicit nonclaim. Once those
durable owners account for every selected row, this temporary page and its
source reconstruction package are deleted; this inventory never becomes a
parallel normative specification.
