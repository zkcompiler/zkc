# Redesign candidates

> **Document kind:** Temporary design note
> **Document state:** Draft
> **Provisional owner:** `project`
> **Authority:** None. This page preserves candidates and alignment work for
> research. It does not amend current specifications or make target roles
> current.
> **Disposition:** Move each accepted conclusion to its semantic owner and any
> required decision record, then delete this page.

## Scope

This note records every system-level redesign candidate identified during the
first v0 architecture reconstruction, including proposals that differ from the
current model, incomplete current boundaries, selected target directions that
need normative alignment, and questions whose answer may justify no change.

It deliberately excludes implementation bugs and security review findings.
Concrete specification inconsistencies appear only as `recheck` inputs to an
architectural question; their repair belongs to the owning documents.

The working baseline is the
[Candidate v0 Semantic Architecture](../project/v0-semantic-architecture.md).
That page is a reviewed public design frame. This note is the more expansive,
temporary change ledger behind subsequent work packages.

## Reading the catalog

| Classification | Meaning |
|---|---|
| **Preserve** | Current design survived review; redesign must retain it |
| **Formalize** | Current behavior or semantics exists but lacks one complete first-class model |
| **Align** | Target direction is selected, but some current normative or explanatory surface lags it |
| **Redesign** | A materially different object, boundary, or methodology is proposed |
| **Research** | More than one credible design remains; do not choose yet |
| **Opportunity** | A valuable capability or preserved option whose prerequisites, costs, and latest responsible decision point require study |
| **Split trigger** | Keep the current domain until specified conditions justify separation |

Priority describes dependency, not urgency or defect severity:

- **P0:** required before normative specification migration;
- **P1:** required before the affected domain can be called a complete v0
  design;
- **P2:** preserve as an extension or split trigger, but do not block the core
  object model; and
- **P3:** reconsider only if implementation or ecosystem evidence creates the
  stated pressure.

Passing current scenarios is not a reason to stop. For every material surface,
compare preserving the current design, completing or aligning it, structural
redesign, and a capability-expanding alternative. An opportunity remains
non-normative until its value, prerequisites, costs, interactions, and decision
deadline survive the common research method.

## Summary

| Candidate | Class | Priority | Present recommendation |
|---|---|---:|---|
| Typed artifact-and-transition graph | Redesign | P0 | Adopt as the global architecture backbone |
| Complete Protocol and artifact role model | Formalize | P0 | Define before repartitioning the kernel specification |
| `protocol/` versus `pir/` ownership | Research | P1 | Keep `pir/` until a complete carrier-independent Protocol root exists |
| Relation ingress and correspondence factorization | Redesign | P0 | Separate semantic roles; defer exact serialized artifact count |
| Qualified admission predicates | Redesign | P0 | Replace unqualified global admission language with boundary-specific predicates |
| Common transition contract pattern | Redesign | P0 | Adopt conceptually; do not require one universal record |
| Analysis question, derivation, judgment, and evidence split | Formalize | P1 | Make all four first-class and independently identified where needed |
| Rule authority and theorem correspondence | Redesign | P1 | Call the signature internal derivability authority; model external theorem correspondence separately |
| Compiler semantic result and stage terminology | Align | P1 | Preserve authenticated sealed successor semantics; reconsider ambiguous `REALIZE` naming later |
| Supplier-bound realization | Align | P0 | Narrow or replace the stale broad reserved realization seam |
| OIR observable semantics and realization correspondence | Research | P1 | Define before general target-conformance claims |
| Mode-indexed composition | Redesign | P1 | Separate sequential, product, shared-state, and recursive modes |
| Committed-object grounding | Research | P1 | Add a generic content/opening theory only after testing alternatives |
| Evidence appraisal and consumer reliance | Redesign | P1 | Separate evidence record, assessment, and intended-use decision |
| One definition per semantic owner | Formalize | P0 | Eliminate repeated accepted-set, policy, identity, and authority tables |
| Canonical registry and policy inventories | Research | P1 | Generate or content-address where manual duplication already drifts |
| Independent checker and exchange form | Research | P2 | Keep carrier-independent views; choose an artifact only when checker requirements are clear |
| Realization subdomains | Split trigger | P2 | Keep one umbrella until identities and consumers demonstrably diverge |
| `evidence/` versus `assurance/` | Split/name trigger | P3 | Keep `evidence/` while testing terminology pressure |
| `foundation/` versus `artifacts/` | Split trigger | P3 | Keep foundation narrow until shared artifact semantics form an independent lifecycle |

## 1. Typed artifact-and-transition graph

**Classification:** Redesign, P0
**Current baseline:** The live corpus defines strong local objects and checked
boundaries, but the complete lifecycle is spread across kernel, artifact,
analysis, compiler, endpoint, architecture, status, and roadmap documents.

### Candidate

Use a typed graph of semantic subjects and authority-bearing transitions as the
global architecture backbone:

```text
Relation and interface roles
  -> Open Protocol
  -> Sealed Protocol Content
  -> Persisted Sealed Artifact
  -> Decoded Sealed Artifact
  -> Admitted Protocol Capability
       |-> Property Analysis
       |-> Checked Protocol Transformation
       `-> Endpoint Projection -> OIR
             -> Supplier Binding -> Realized Endpoint
             -> Deployment -> Invocation -> Run Result

Observations and receipts
  -> Evidence Record -> Claim Assessment -> Reliance Decision
```

This replaces neither PIR nor OIR. It replaces the assumption that every arrow
is one kind of lowering or that the directory graph is itself the semantic
architecture.

### Why revisit

- `seal`, `link`, `analyze`, compiler transformation, `project`, realization,
  execution, and evidence appraisal have different correctness relations.
- Later objects currently rely on terminology such as `artifact`, `valid`, or
  `admitted` that is too broad without a subject qualifier.
- Relation ingress, admitted artifact capabilities, and evidence reliance do
  not fit a single linear compilation pipeline.

### Risks and cautions

- Do not turn the graph into one universal serialized `TransitionRecord`.
- Do not require every conceptual role to have stable identity.
- Do not make operational provenance part of protocol meaning.
- Do not model analysis as an object-mutating transition.

### Promotion gate

Every current admitted boundary and every target role can be placed in the
graph with exact source, target, authority, refusal, and non-claim. No role may
exist only because there is a C++ class or documentation directory.

**Destinations:** `project/` system architecture and domain-owned bridge
specifications.

## 2. Complete Protocol and artifact role model

**Classification:** Formalize, P0
**Current baseline:** Protocol is the semantic subject and PIR its current
explicit representation. The compact kernel tuple does not enumerate all
identity-bearing material now carried and checked, while persistence, decoding,
and environment-qualified admission are already distinct normative roles.

**Stage 1 disposition:** The selected
[Protocol IR Architecture](../project/protocol-ir-architecture.md) replaces the
first lifecycle candidate with an ordered `InteractiveCore`, explicit
challenge interpretation, dependent `ProtocolInterfaceId`, separate
`ProverPlanId`, typed semantic regimes, and one distinct small closed canonical
PIR level in MLIR. It retains typed authority and opaque-reference graphs plus
process-local admitted capabilities. Remaining work includes exact normative
algebra, canonical grammar, and transition contracts.

### Candidate

Define complete conceptual types for:

```text
ProtocolDraft
InteractiveCore
TranscriptConstruction
Protocol
ProtocolInterface
ProverPlan
SemanticAuthorityGraph(root)
ReferencedSubjectGraph(root)
CanonicalPirCandidate
PersistedPirArtifact
DecodedPirCarrier
AdmittedProtocol
SemanticRegime
```

The complete Sealed content contract must give one home to at least:

- transcript spine and claim-flow graph;
- check, reduction, terminal, and construction citations;
- seal policy;
- construction and transcript profile;
- exact cited vocabulary closure;
- routes and witness-facing declarations;
- segments and composition structure;
- anchors and material bindings; and
- canonical identity preimage.

Persistence defines a representation. Decoding authenticates carrier shape and
content identity. Admission rechecks the decoded subject under the consumer's
exact environment and grants an immutable capability. These are not aliases.

### Questions

- Which authoring languages have a distinct denotation and transformation law
  that justifies a durable dialect rather than a convenience operation?
- Which environment identities belong in content and which remain external
  authorities cited by content?
- Does an admitted capability identify the checker revision, only the semantic
  environment, or neither beyond its in-process authority?
- What exact field ledger makes canonical PIR, identity encoding, and a narrow
  checker mechanically cross-checkable without creating a second authority?

### Promotion gate

The type decomposition must reproduce current identity and refusal behavior
without silently rotating artifacts. Any incompatible identity change requires
an explicit version and migration decision.

**Destinations:** `foundation/` lifecycle mechanisms and `pir/` or future
`protocol/` semantic specification.

## 3. `protocol/` versus `pir/` ownership

**Classification:** Research, P1
**Current baseline:** Current architecture already distinguishes Protocol from
PIR. The unresolved issue is documentation ownership, not whether the semantic
distinction exists.

### Alternatives

1. **Keep `pir/`.** PIR is the project's stable semantic language name and the
   domain owns Protocol as expressed by that language.
2. **Promote `protocol/`.** Protocol owns the carrier-independent root,
   judgments, and lifecycle; `protocol/pir/` or a carrier section owns MLIR PIR.
3. **Separate `protocol/` and `representation/`.** Use only if several durable
   representations genuinely share one semantic Protocol contract.

### Current recommendation

Keep `pir/` after Stage 1. Rename only if the complete abstract Protocol
contract gains an independent consumer, a second carrier, or a maintained
ownership conflict that a split would actually resolve.

### Caution

Do not use the directory decision to postpone defining Protocol. Conversely,
do not create `protocol/` only because Protocol is conceptually above PIR.

**Destinations:** `project/` information architecture and the selected domain
README; decision record if renamed.

## 4. Relation ingress and correspondence factorization

**Classification:** Redesign, P0
**Current baseline:** The admitted `RelationContract` is post-seal and
evidence-only relative to PIR. The target architecture also needs relation,
public-instance, and witness-interface facts before or during Protocol
construction.

### Candidate semantic roles

```text
RelationDefinitionRef
RelationInterface
PublicInstanceMapping
PrivateWitnessMapping
RelationInstanceBinding
ProtocolRelationCorrespondence
RelationCompilationCorrespondence
```

Use the internal ontology:

```text
Relation R
Public Instance x
Private Witness w
Claim or Proposition
```

Use `statement` only with an explicit local definition or compatibility note.

### Required distinctions

- defining an interface is not compiling a relation;
- mapping a public instance is not mapping a private witness;
- declaring a witness port is not supplying a witness capability;
- a relation identity is not proof that serialized bytes denote it;
- post-seal correspondence cannot retroactively change Protocol identity; and
- relation satisfaction is not implied by any interface contract.

### Questions

- Which relation facts affect Protocol identity directly?
- Can Protocol cite an immutable RelationInterface without importing relation
  semantics into the kernel?
- Are public-instance and witness mappings functions, relations, programs, or
  attributed assertions?
- Which transformations must be executable or independently checkable?
- Where do shape, preimage, and source-language correspondence live?
- Does verifier-to-relation descent produce relation material, a relation
  interface, or a correspondence claim?

### Promotion gate

The model must represent the current post-seal RelationContract without
weakening its non-claims and must explain target pre-seal ingress without using
one contract in two incompatible authority roles.

**Destinations:** `relations/`, with bridge references from `pir/`, `oir/`, and
`realization/`.

## 5. Qualified admission predicates

**Classification:** Redesign, P0
**Current baseline:** Document maturity, normative admission, implementation
support, carrier acceptance, artifact admission, and consumer reliance are
sometimes described with overlapping words.

### Candidate vocabulary

```text
syntax-recognized
carrier-valid
seal-admitted
artifact-admitted under environment E
analysis-derivable under signature S and context C
projection-admitted for endpoint K
execution-supported under profile Q
evidence-appraised under policy A
reliance-approved for intended use U
```

These are independent predicates, not a progressive maturity ladder. A surface
may have a carrier form and seal behavior while projection must refuse it.

### Cautions

- Do not weaken the current meaning of an admitted normative contract.
- Do not encode implementation support inside a semantic artifact.
- Do not call negative execution a failed admission.
- Do not call a conditional judgment admitted unless the exact relying policy
  is named.

### Promotion gate

Every use of `admit`, `valid`, `supported`, and `reserved` in the reconstructed
specification can be assigned an exact subject and authority without ambiguity.

**Destinations:** `foundation/` terminology and each domain's exact predicates;
global implementation state remains under project status.

## 6. Common transition contract pattern

**Classification:** Redesign, P0
**Current baseline:** Individual boundaries define different subsets of the
information required to review a semantic transition.

### Candidate checklist

Every authority-bearing transition should state, where applicable:

```text
source subject kind, identity, and semantic version
target subject kind, identity, and semantic version
authenticated environment and registry closure
preconditions and required capabilities
transition family or implementation identity
deterministic parameters and binding time
success result and typed refusal space
preservation, refinement, correspondence, or derivability relation
coverage or source map
checker and admitting authority
evidence scope, residual trust, and non-claims
```

### Cautions

- `seal` is not lowering.
- compiler transformation may intentionally change Protocol semantics under a
  transform-family contract; it is not automatically equivalence.
- projection is endpoint correspondence, not whole-Protocol equivalence.
- realization is behavioral correspondence, not merely successful code
  generation.
- analysis produces a proposition and derivation, not a successor artifact.
- refusal, malformed input, unsupported surface, negative judgment, verifier
  rejection, and runtime failure remain different results.

### Promotion gate

Apply the checklist to every admitted current transition and at least one
target transition. Remove fields that are not genuinely common before creating
any shared schema.

**Destinations:** `foundation/` common pattern if justified, with exact
contracts owned by producer/result domains.

## 7. Analysis object and authority model

**Classification:** Formalize and redesign, P1
**Current baseline:** Current Analysis is post-seal, notion-indexed,
plan-driven, and conditional. It already separates declarations, bindings,
plans, and results, but the global architecture needs sharper object and
authority language.

### Candidate roles

```text
AnalysisQuestion
PropertyIndex
RuleDeclaration
RuleSignature or RuleAuthority
SemanticContext
RuleBinding
DerivationPlan
EvaluatedDerivation
PropertyJudgment
TheoremCorrespondenceRecord
DerivationRecheckReceipt
```

### Candidate authority statement

The admitted signature is the internal rule and derivability authority. It
determines what the zkc calculus may derive. It does not establish:

- truth of an external theorem;
- faithful formalization of that theorem;
- validity of external assumptions;
- correspondence between the analyzed view and an independently described
  concrete protocol; or
- satisfaction of the analyzed relation.

### Questions

- Does PropertyJudgment identity include its derivation or only the complete
  question and conclusion?
- Is the current witness a portable proof object, a replay request, or a
  receipt from one evaluator?
- Should a result cite the whole signature or the exact transitive rule closure
  consumed by one derivation?
- Which rules are foundational, derived, axiomatic, or externally justified?
- Can soundness, knowledge, completeness, and zero knowledge share a calculus,
  or only an envelope and bound algebra?
- Where does rule-to-paper or rule-to-formal-proof correspondence live?

### Cautions

- `analysis/` must not absorb every domain-local judgment.
- A theorem citation is metadata unless a specified checker consumes it.
- Search and plan synthesis must remain outside the small evaluator.
- A checked proof of a producer-selected question does not establish the
  consumer's intended question.

**Destinations:** `analysis/`, `evidence/` for receipts only, and an eventual
decision on rule extension.

## 8. Compiler semantic result and terminology

**Classification:** Align, P1
**Current baseline:** Compiler Core produces authenticated sealed successors
inside a checked `DOMAIN -> REALIZE -> VALID -> SCORE -> SELECT -> DECIDE`
process. The PIR provider may internally reopen, transform, reseal, admit, and
replay-check, but Open PIR is not the public Compiler Core target. `link` is the
current admitted transition that returns Open PIR.

### Alignment work

- Preserve authenticated artifact-to-artifact Compiler Core semantics.
- Keep producer search and claimed results outside decision authority.
- Keep `Candidate`, evaluated derivations, and `Decision` as checker outputs,
  not generic untrusted proposals.
- State the internal Open/reseal path only as PIR-provider implementation
  correspondence.
- Reconsider the stage name `REALIZE` because it collides with endpoint
  realization; defer renaming until compatibility and document cost are known.

### Questions

- Do CompilerRequest, PlanDomain, CompilerPlan, Candidate, and Decision need
  persisted canonical forms in v0?
- Which of them need identities rather than complete structural equality?
- Is `ArtifactSemantics` a common foundation mechanism or compiler-owned
  interface?
- What preservation relation does each transform family claim: equivalence,
  refinement, claim correspondence, or only construction legality?

**Destinations:** `compiler/` and terminology index; decision record only if
public names change.

## 9. Supplier-bound realization alignment

**Classification:** Align, P0
**Current baseline:** Target architecture selects explicit supplier-bound
emission. A broader general `oir-realize` seam remains reserved in existing
normative prose.

### Selected target model

```text
OIRArtifact
  + explicit SupplierBinding
  -> RealizedEndpoint
  + scoped correspondence obligations
```

Optional layout, scheduling, fusion, or kernel IRs stay implementation-private
unless independent interchange, caching, validation, deployment identity, or
reproducibility requires a canonical subject.

### Alignment work

- Narrow or replace the stale broad reserved boundary.
- Do not reopen a general capability-matching compiler merely because the
  reserved signature exists.
- Define which supplier choices are operational and which must be selected
  upstream as Protocol or OIR semantics.
- Require any meaning-changing choice to return upstream and create a new
  semantic subject; a backend provider never gains semantic authority.

### Promotion gate

The normative boundary, target architecture, emitter model, and future OIR
correspondence specification describe one public semantic direction.

**Destinations:** `realization/`, `oir/`, and correction of current reserved
boundary ownership during migration.

## 10. OIR observable semantics and realization correspondence

**Classification:** Research, P1
**Current baseline:** OIR is a canonical endpoint artifact with protected
effects, typed ABI, source citation, and projection coverage. General target
correspondence is not admitted.

### Required semantic surface

Define verifier and prover OIR observables, including:

- public-instance inputs and exact encoding;
- witness capabilities and secrecy boundaries;
- proof-stream reads and writes;
- transcript state and challenge outputs;
- prover randomness and private state;
- supplier calls and their typed effects;
- verifier accept/reject;
- typed refusal and runtime failure;
- completion, EOF, and unconsumed material;
- resource exhaustion; and
- observable logs or traces used for correspondence.

Prover and verifier are asymmetric dual projections, not inverse programs.
Their semantics may be relations rather than total functions because
randomness, external suppliers, and failure are meaningful.

### Correspondence alternatives

- final-result equality;
- trace refinement;
- bisimulation or observational equivalence;
- ABI and effect correspondence plus separate primitive assumptions;
- per-artifact translation validation; or
- a graded combination with explicit exclusions.

Final-result equality alone is likely too weak because it can miss transcript,
proof framing, supplier, and failure differences.

### Promotion gate

At least one verifier and one prover realization can be specified with exact
allowed behaviors, refusals, resource assumptions, and residual supplier trust.

**Destinations:** `oir/` abstract execution and `realization/` correspondence.

## 11. Mode-indexed composition

**Classification:** Redesign, P1
**Current baseline:** Current `link` composes bounded Open PIR structure under
one environment and returns Open PIR. It does not establish every semantic or
security property associated with composition.

### Candidate modes

```text
sequential reduction composition
independent product composition
shared-challenge composition
shared or interleaved transcript composition
recursion / verifier-as-relation
aggregation with an outer decision
```

Each mode must identify:

- relation and instance transformation;
- witness transformation or equality obligations;
- transcript order and challenge provenance;
- assumptions and property-judgment transport;
- failure and refusal composition;
- proof ABI and endpoint projection;
- child identity and provenance; and
- the exact theorem or open obligation justifying the composition.

### Cautions

- Shared challenges do not imply witness equality.
- Product composition is not arbitrary temporal interleaving.
- Structural `link` does not imply property preservation.
- Recursion is not ordinary endpoint realization; verifier semantics becomes
  outer relation material through a new correspondence boundary.

**Destinations:** `pir/` structural link, `analysis/` property composition,
`relations/` descent, and project-level composition architecture.

## 12. Committed-object grounding

**Classification:** Research, P1
**Current baseline:** Value profiles now state origin, arity, content class, and
construction route. The kernel deliberately does not inspect committed
content, and declarations alone do not establish what a commitment actually
binds.

### Missing relations

- commitment to logical object;
- logical object to declared profile and domain;
- opening or query answer to committed object;
- construction route to binding assumption;
- relation-derived or preprocessed material to externally grounded preimage;
- terminal consistency to a generic commitment/opening closure; and
- quantitative analysis fact to the structure that grounds it.

### Alternatives to research

1. **Profile plus external correspondence obligation.** Keep the kernel
   structural and make all content grounding an explicit post-seal condition.
2. **Generic committed-object contract.** Add a sealed object/opening relation
   vocabulary without evaluating cryptography.
3. **Relation-owned object semantics.** Let relation interfaces define object
   preimages while PIR cites them opaquely.
4. **Construction-owned object semantics.** Let binding routes define the
   content/opening proposition, with relation adapters grounding source data.

### Cautions

- Do not repeat the old claim that value profiles are absent; they exist.
- Do not make a producer-declared arity authoritative when understating it can
  understate a bound.
- Do not add protocol-family-specific attachment fields before testing a
  generic model.
- Do not import predicate truth into structural sealing.

**Destinations:** likely `pir/` value/object semantics, `relations/` origin
grounding, and `analysis/` conditional obligations.

## 13. Evidence appraisal and consumer reliance

**Classification:** Redesign, P1
**Current baseline:** Evidence is correctly separated from semantics, but the
complete future admission/reliance lifecycle is not specified.

### Candidate lifecycle

```text
RawObservation or Receipt
  -> EvidenceRecord
  -> appraisal under EvidencePolicy
  -> scoped ClaimAssessment
  -> consumer applies IntendedUsePolicy
  -> RelianceDecision
```

### Required distinctions

- logical derivation versus assurance evidence;
- record validity versus truth of the observed claim;
- evidence appraisal versus project status;
- project status versus release or user reliance;
- bounded execution versus family-wide conformance; and
- formalization receipt versus external theorem truth.

### Cautions

- Evidence cannot authorize its own use.
- A release policy may require evidence without making that evidence semantic
  content.
- Removing an evidence record cannot change Protocol or OIR identity.
- An appraisal result must bind exact policy, subject, scope, issuer, and time.

**Destinations:** `evidence/`, global status derivation, and consumer-owned
release or reliance policy outside semantic domains.

## 14. One definition per owner and generated inventories

**Classification:** Formalize and research, P0/P1
**Current baseline:** Several current documents repeat normative counts,
accepted sets, policy descriptions, domain tags, and authority maps. Working
review found concrete drift that must be rechecked before repair.

### Candidate methodology

- One page and domain own each type, transition, policy, identity preimage,
  accepted-set definition, and judgment.
- Overview, architecture, guides, and boundary maps link to owners rather than
  copy complete schemas.
- Derive inventories from machine-consumed data when the generated result can
  remain readable and reviewable.
- If generation would hide semantics inside code, keep one normative table and
  validate code/data against it instead.
- Make domain tags, diagnostic allocations, manifest entries, and closed
  registry sections machine-checkable where their semantics are already exact.

### Questions

- Is SealPolicy best represented by one fixed normative table or immutable
  content-addressed declarations?
- Which vocabulary summaries can be generated without making the data file the
  undocumented semantic owner?
- Should identity domain tags share one registry across artifact families?
- Can the document manifest consume page headers without adding a second
  metadata schema?

### Caution

Generation eliminates transcription drift only when the generation source is
itself an explicit, reviewed authority.

**Destinations:** owning specifications, `foundation/` extension/versioning,
and `project/` manifest tooling.

## 15. Independent checker and carrier-independent exchange

**Classification:** Research, P2
**Current baseline:** PIR and OIR use MLIR as carrier, canonical identities use
custom semantic encodings, and Analysis already consumes an owned MLIR-free
view. Current derivation witnesses are rechecked by the producing semantic
implementation rather than established as universally portable certificates.

### Candidate direction

Retain MLIR for authoring and compiler engineering, and use the restricted
closed canonical PIR level for full admission without the optimizer, search,
authoring dialects, or backend stack. Design smaller semantic views or
certificates only for named consumers.

Possible artifacts include:

- canonical Protocol bytes;
- canonical OIR bytes;
- an explicit analysis question and derivation object;
- a minimal transition witness or coverage map; and
- exact semantic-environment closure.

### Trigger

Do not freeze a new exchange format until there is a named independent
consumer, stable semantic root, and clear validation claim. A second encoding
without a consumer creates another parity obligation rather than assurance.

**Destinations:** `foundation/` representation, domain canonical encodings,
`analysis/`, and evidence for independent-checker results.

## 16. Conditional domain splits and renames

### Realization subdomains

Keep one `realization/` umbrella until at least two of emitted artifact,
supplier binding, deployment, invocation, session, or runtime result have
independent normative identities, consumers, and change cadence. Likely future
children are `emission/`, `deployment/`, `invocation/`, and `runtime/`, but
pre-creating them would be architecture by anticipation.

### `evidence/` versus `assurance/`

Keep `evidence/` while the main subject is evidence records. Rename or split if
the durable domain becomes primarily appraisal, assurance cases, and reliance
policy, or if `evidence` repeatedly attracts logical derivations and informal
supporting prose.

### `foundation/` versus `artifacts/` or `representation/`

Keep foundation narrow. Split only if carrier-independent artifact lifecycle,
representation, encoding, admission, and evolution form a coherent independent
subject used by multiple semantic domains without redefining their meanings.

### Common rule

Directory size and code namespaces are not split triggers. Independent subject,
authority, identity, lifecycle, and consumers are.

## 17. What is explicitly not being redesigned

The following remain preservation constraints unless later research produces a
specific counterexample:

- Protocol, not relation source or backend code, is the primary compiled
  semantic subject.
- PIR's transcript spine and claim-flow graph remain distinct geometries.
- Native v0 scope remains explicit public-coin protocols with sealed transcript
  structure.
- Seal remains structural closure, contract resolution, and identity—not a
  cryptographic property verdict.
- Property Analysis remains post-seal, notion-indexed, explicit-plan, and
  conditional.
- Compiler search remains outside authoritative recomputation.
- Compiler transformation successors remain authenticated sealed artifacts.
- Prover and verifier OIR remain asymmetric projections from one admitted
  Protocol.
- OIR remains endpoint semantics, not a backend recipe.
- Concrete suppliers never acquire authority to change fixed endpoint
  semantics.
- MLIR remains a carrier and engineering substrate, not semantic authority.
- Evidence remains one-way support for claims and never changes artifact
  meaning.

## 18. Absorption map and deletion trigger

| Section | Durable destination or disposition |
|---|---|
| Typed graph and global lifecycle | `project/` system architecture |
| Complete Protocol and artifact roles | `foundation/` plus `pir/` or future `protocol/` |
| Relation factorization | `relations/` specifications and architecture |
| Qualified admission and transition pattern | `foundation/` plus domain-owned boundaries |
| Analysis model | `analysis/` specifications and decisions |
| Compiler alignment | `compiler/` specifications and terminology decision |
| Realization alignment and OIR semantics | `oir/` and `realization/` |
| Composition and committed objects | `pir/`, `relations/`, and `analysis/` |
| Evidence/reliance | `evidence/` and consumer policy |
| Generated inventories | each semantic owner plus project tooling |
| Independent checker | deferred architecture/roadmap until a consumer exists |
| Split triggers | domain READMEs until triggered or rejected |

Delete a section as soon as its complete reviewed conclusion is represented in
the destination and any semantic change has an accepted decision. Delete this
file when the table contains no unresolved candidate.
