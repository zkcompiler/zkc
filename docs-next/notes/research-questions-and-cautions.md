# Research questions and design cautions

> **Document kind:** Temporary design note
> **Document state:** Draft
> **Provisional owner:** `project`
> **Authority:** None. This page is a research and falsification ledger. It
> neither changes the current specification nor establishes that an observed
> mismatch is a defect.
> **Disposition:** Resolve each item in its exact owner, preserve only durable
> conclusions and rationale, then delete this page.

## Scope

This note collects the cross-cutting questions, specification seams, and
methodological traps that could otherwise be lost while the v0 object model is
rebuilt. It complements the [redesign catalog](redesign-candidates.md): that
page asks what might change; this page records what must be checked before a
change can be trusted.

The ledger is deliberately broader than an issue list. Some entries are likely
to end in a decision to preserve the current design. A `recheck` names a
specific seam whose owners must be read together; it is not a finding, a
support claim, or permission to repair one document in isolation.

Implementation defects, exploit analysis, and security-review material are
out of scope. Cryptographic claims appear only to keep specification authority
and non-implications precise.

## 1. Non-collapses the final model must preserve

| Do not collapse | Reason |
|---|---|
| Relation definition and Protocol | A relation states what witnesses and instances satisfy; a Protocol is one interactive or Fiat--Shamir construction intended to establish a claim about it |
| Protocol and PIR carrier | Protocol is the semantic subject; PIR is its current explicit representation and authoring surface |
| Structural seal and a property judgment | Seal establishes admitted structure and identity; analysis derives a qualified conclusion under an immutable context/catalog and explicit plan, retaining typed assumptions as hypotheses |
| Judgment and derivation | A judgment is a conclusion; a derivation is the replayable route by which one evaluator reached it |
| Derivation and evidence | A derivation can be a subject of evidence, but its existence does not establish theorem truth, implementation conformance, or external assumptions |
| Artifact admission and evidence appraisal | Admission grants a consumer capability under an exact semantic environment; appraisal evaluates observations under an assurance policy |
| Evidence appraisal and reliance | An appraisal characterizes support; a consumer decides whether it is adequate for a named use |
| OIR and realization | OIR defines endpoint-observable behavior; realization binds that behavior to suppliers and an emitted target artifact |
| Successful execution and conformance | A run is one observation; correspondence over a declared input and environment class requires a separate claim and evidence plan |
| Status and roadmap | Status reports the checkout; the roadmap orders intended work |

These distinctions should become typed boundaries rather than warnings repeated
throughout prose.

## 2. Research discipline

Use the durable [Design Research Method](../project/design-research-method.md)
for every bounded package. This ledger adds cross-cutting cautions; it does not
replace the generative, evaluative, and convergence work defined there.

For every design question, reconstruct sources in this order:

1. the current authority map and the exact normative owner;
2. all other normative owners that consume or constrain the subject;
3. architecture, status, roadmap, and evidence, each only for its own claim;
4. implementation and tests as correspondence, feasibility, and drift
   evidence;
5. primary research and official external specifications as design-space and
   evaluation input;
6. prior design notes as historical rationale, never as current authority.

Before promoting a conclusion:

- state the current model in terms its owner would recognize;
- identify the exact ambiguity, missing role, duplication, failed use case, or
  unexplored capability and option value;
- construct a portfolio spanning preservation, completion or alignment,
  structural redesign, and capability-expanding design;
- state what each alternative newly enables, simplifies, forecloses, or makes
  expensive;
- construct at least one counterexample to the proposed abstraction;
- compare a meaningful alternative when identity or authority changes;
- classify compatibility, migration, implementation, and evidence impact
  separately;
- state what would falsify the recommendation; and
- name the durable specification, architecture, decision, roadmap, or evidence
  destination.

External research can justify a design constraint, reveal an alternative, or
make a previously invisible capability plausible. It cannot prove that zkc's
implementation satisfies its specification, that a cryptographic theorem's
hypotheses hold for an artifact, or that a local abstraction is complete.

## 3. Concrete recheck ledger

The following observations are inputs to owner-level review. None is a
standalone correction instruction.

### R1. Complete Protocol root

**Recheck:** The compact Protocol Kernel presentation and the carrier/artifact
contract must be reconciled into one complete conceptual Protocol root. The
current identity and admission path visibly consults policy, construction
profile, cited vocabulary content, routes, anchors, segments, and other
material not conveyed by a naive reading of a small kernel tuple.

**Why it matters:** A partial root would make the specification easy to read
but impossible to use as a carrier-independent contract. Duplicating the full
MLIR schema into a second hand-maintained Protocol schema would create a
different failure.

**Required result:** One owner for complete semantic content, one owner for its
MLIR representation, and an explicit correspondence between them.

**Stage 1 disposition:** Selected as ordered `InteractiveCore` plus Fresh or
Fiat--Shamir challenge interpretation, with a dependent
`ProtocolInterfaceId`, separate `ProverPlanId`, and one distinct small closed
canonical PIR level in MLIR. The durable result is the
[Protocol IR Architecture](../project/protocol-ir-architecture.md). Exact
normative field ownership and byte grammar remain later work; the subject and
interface identity boundaries are no longer open Stage 1 questions.

### R2. Environment and registry closure

**Recheck:** Secondary authority maps should enumerate every registry and
semantic environment that a consumer authenticates, including relation
contracts where applicable. A compact list must not be read as exhaustive if
the boundary specification requires more.

**Why it matters:** An omitted authority can make admission appear portable
across environments when it is not. A merely human-readable registry name must
not substitute for required content identity.

**Stage 1 disposition:** Separate regime-qualified semantic identities,
semantic authority and opaque-reference graphs, retained resolver or compiler
environments, local admission policies, and execution supplier closure. Stage
2 must assign the exact read set and comparison rule per transition when it is
explicitly resumed.

### R3. Relation ingress versus post-seal correspondence

**Recheck:** Current `RelationContract` use is post-seal and evidence-oriented,
while the target architecture needs relation interface and public/witness
mapping facts during Protocol authoring and later realization. Determine
whether these are distinct contract kinds, distinct roles of one immutable
object, or a factored family.

**Why it matters:** One contract cannot safely be both identity-bearing
construction input and a post-hoc annotation unless its fields, authority, and
timing make that dual role explicit.

### R4. `BindingSchema`

**Recheck:** [`boundaries.md`](../../docs/spec/boundaries.md) refers to a
`BindingSchema` body as a semantic membrane, but the current normative corpus
does not obviously route the reader to a complete definition.

**Why it matters:** A named but unowned schema can conceal whether the binding
is public-instance mapping, witness-interface mapping, realization ABI, or
evidence-only correspondence.

### R5. Seal policy as an exact contract

**Recheck:** Assemble the complete normative `SealPolicy` table from the
kernel, vocabularies, carrier, and implementation correspondence. Confirm its
closed modes, permitted sinks, identity impact, refusal behavior, and relation
to `COV_obl` and presentation as a closed artifact.

**Why it matters:** Policy is identity-bearing semantics, not runtime
configuration. Distributed partial descriptions risk accidental alternate
accepted sets.

### R6. Reserved `artifact_verify`

**Recheck:** `artifact_verify` has carrier representation while remaining a
reserved protocol-vocabulary event surface with bounded endpoint semantics.
Specify the exact line between syntactic carrier availability, seal admission,
projection behavior, and future imported-artifact verification.

**Why it matters:** “Representable” and “admitted” are independent. The final
documentation must make this a deliberate staged extension, not an apparent
contradiction or current general recursion claim.

### R7. Endpoint realization boundary

**Recheck:** The broad reserved `oir-realize` signature should be compared
against the selected supplier-bound emission architecture and current
operational Rust path. Decide whether to narrow, replace, or factor the
reserved surface.

**Why it matters:** A generic target/capability parameter can imply that target
selection is allowed to alter endpoint semantics. The selected architecture
instead requires semantic choices upstream and concrete supplier binding
downstream.

### R8. Compiler `REALIZE` terminology

**Recheck:** The Compiler Core's internal `REALIZE` stage constructs a candidate
Protocol transformation; realization elsewhere means binding OIR to a target
artifact and suppliers.

**Why it matters:** The operations have different source and target kinds,
authority, and preservation claims. Retain the stable implementation term if
necessary, but give the architecture unambiguous role names.

### R9. Rule-body and judgment-form inventories

**Recheck:** Summary prose, schema inventories, and implementation enums must
remain synchronized with the closed `RuleBody` variants and the separately
described judgment-form taxonomy.

**Why it matters:** The count of executable body variants, the number of
conceptual forms, and the number of theorem families answer different
questions. A summary that merges them can misstate extensibility authority.

### R10. Lookup and LogUp terminology

**Recheck:** Use `lookup` for the general relation and `LogUp` or `logup` only
for the admitted logarithmic-derivative construction and its concrete
profiles. Check overview, status, rules, carrier types, and examples together.

**Why it matters:** A construction-specific derivation does not establish a
generic lookup compiler, endpoint, or pricing theorem.

### R11. ProtocolVocabulary section inventories

**Recheck:** The seven jointly admitted source sections, the conditionally
embedded cited subsets, and transitive predicate-spec admission are different
inventories. Every summary must name which inventory it is counting.

**Why it matters:** A source envelope, a sealed artifact projection, and the
set of independently addressable semantic authorities are not interchangeable.

### R12. Content-identity domain tags

**Recheck:** Compare the exhaustive domain-tag table in
[`versioning.md`](../../docs/spec/versioning.md) with every hashing call,
registry encoder, and artifact encoder. Treat any missing or differently
spelled tag as an identity-contract issue, not editorial drift.

**Why it matters:** Domain tags define durable names. Coordinated code changes
can remain internally self-consistent while rotating every identity.

### R13. OIR identity and provenance

**Recheck:** OIR currently makes projection provenance and source citation part
of artifact identity and does not define a separate provenance-independent
semantic digest. Decide whether this remains the final v0 contract before
adding exchange or caching layers.

**Why it matters:** Removing provenance from identity can permit one program to
claim several sources; retaining it may limit cross-source deduplication. The
choice must follow intended consumers, not storage convenience.

### R14. Standalone OIR validation

**Recheck:** Standalone OIR structural verification does not reconstruct
`COV_realized` without the cited Protocol. Define which capability is granted
by carrier verification alone and which requires paired projection admission.

**Why it matters:** “Valid OIR” is otherwise ambiguous between well-formed
endpoint syntax and a complete projection of one exact admitted Protocol.

### R15. Current and target role mixing

**Recheck:** Architecture pages sometimes need to mention current operational
paths, selected target roles, and still-reserved normative surfaces together.
Every such statement must label its axis locally rather than relying on the
page title.

**Why it matters:** A coherent future graph can be mistaken for implemented or
admitted support even when each component is individually qualified elsewhere.

## 4. Domain research questions

### 4.1 Foundation

- What is the smallest carrier-independent identity interface shared by PIR,
  OIR, registries, derivations, and evidence records?
- Is environment-qualified admission one generic capability pattern with
  domain-owned predicates, or do materially different refusal and lifetime
  rules require separate mechanisms?
- Which version facts are semantic content, carrier gates, producer metadata,
  or ecosystem compatibility policy?
- Can refusal taxonomies share a common envelope without erasing domain
  meaning?
- When does a shared artifact lifecycle become strong enough to justify an
  `artifacts/` domain rather than a narrow foundation mechanism?

### 4.2 Relations

- What exactly is a relation definition, relation interface, public instance,
  private witness, and relation instance in zkc's ontology?
- Which facts are authored, computed, asserted, or independently checked?
- Which relation facts enter Protocol identity, and which are cited through an
  immutable reference?
- Are public-instance and witness mappings functions, relations, programs, or
  correspondence claims?
- Can one interface support R1CS, Plonkish systems, AIR, and native algebraic
  protocols without collapsing their witness models?
- Which direction owns each bridge: source-to-Protocol ingress,
  Protocol-to-relation correspondence, OIR descent, and realized witness ABI?

### 4.3 Protocol and PIR

- What is the complete carrier-independent Protocol content type?
- Is Open Protocol a partial state of the same object, a proposal language, or
  an authoring capability over mutable PIR?
- Which facts are intrinsic content, resolved environment, derived view, or
  evidence?
- Can transcript spine and claim-flow graph composition be specified without
  assuming one universal monoidal operator?
- Which composition modes are admitted now: sequential splice, product,
  shared state, imported challenge, recursion, or none?
- What immutable capability does each of persistence, decoding, seal, and
  consumer admission grant?

### 4.4 Analysis

- Which objects need stable identity: question, plan, derivation, judgment,
  signature, context, and external bindings?
- Is the current rule signature internal derivability authority, theorem
  correspondence metadata, or both? If both, how are the claims separated?
- How are theorem truth, faithful formalization, hypothesis discharge, artifact
  correspondence, and evaluator conformance represented without one
  certificate implying all five?
- Which calculi remain notion-specific, and which derivation constructors can
  be genuinely shared?
- Can analysis views remain fully MLIR-free without manually duplicating the
  Protocol definition?

### 4.5 Compiler

- What is the exact semantic relation between predecessor and successor for
  each transform family: equality, refinement, preservation under hypotheses,
  or merely separate admitted artifacts plus a checked family relation?
- Should transform applications or decision records be persisted artifacts,
  reproducible requests, or evidence-only traces?
- Which producer reports are untrusted proposals, which core values are
  recomputed, and which external judgments remain assumptions?
- How are optimization objectives separated from legality and property
  constraints?
- Does a common transition contract help review all families without imposing
  a universal serialized transform record?

### 4.6 OIR

- What is OIR's complete observable semantics independent of its MLIR ops?
- Which program transformations preserve those observables, and under what
  effect discipline?
- What does paired Protocol/OIR admission grant beyond standalone carrier
  verification?
- How do prover and verifier projections relate: dual views, two programs with
  a correspondence, or one parameterized endpoint semantics?
- What completion property is established by `COV_realized`, and what remains
  a realization or supplier obligation?

### 4.7 Realization

- Which supplier properties are authenticated by digests, checked by ABI,
  tested by conformance evidence, or assumed?
- What is the exact realized artifact identity, and does it include target,
  toolchain, suppliers, configuration, and source OIR identity?
- Which failures are unsupported capability, invalid binding, compilation
  refusal, deployment failure, invocation failure, or endpoint rejection?
- When do emission, deployment, invocation, and runtime deserve separate
  internal subdomains with independent identities and consumers?
- How can an independent checker validate the OIR-to-target correspondence
  without importing the full compiler stack?

### 4.8 Evidence and reliance

- What is the common evidence-record envelope, and which observation schemas
  remain domain-local?
- Is a claim assessment a durable artifact, a reproducible view, or a policy
  decision over evidence?
- Who owns acceptance criteria: the evidence domain or the relying consumer?
- How are negative results, exclusions, environmental drift, and supersession
  represented?
- Which exact use cases need reliance decisions before v0, rather than a more
  modest evidence record plus global status claim?

## 5. Cross-cutting design traps

### Authority traps

- Do not treat code, tests, registry files, or generated schemas as intended
  semantic authority.
- Do not let an architecture page override an owning specification.
- Do not let evidence authorize its own intended use.
- Do not make a decision effective without updating the affected owner.
- Do not resolve normative conflicts by recency, detail, or implementation
  behavior.

### Modeling traps

- Do not mirror source directories or MLIR operations into the domain model.
- Do not create one universal artifact, transition, result, or error type before
  proving that the participating subjects share identity and lifecycle.
- Do not assign stable identity to every conceptual role merely because the
  architecture names it.
- Do not make transport bytes, MLIR locations, operational provenance, or
  mutable object identity part of meaning without an explicit need.
- Do not model analysis as mutation of the Protocol it studies.
- Do not infer general composition from the current `link` operation.

### Claim traps

- Do not use `valid`, `verified`, `supported`, `complete`, or `admitted`
  without the subject, environment, and authority.
- Do not turn conditional analysis into unconditional security language.
- Do not turn execution success into family-wide backend correspondence.
- Do not turn reference parity into an independent implementation proof.
- Do not turn a reserved carrier form into an admitted semantic surface.
- Do not let target architecture wording become a current status claim.

### Extension traps

- Do not grow an enum, registry, or rule body without identifying whether the
  change extends data, a judgment, a transformation recipe, or the kernel.
- Do not add provider-specific behavior to the semantic core to simplify one
  backend.
- Do not permit a realization supplier to select transcript, codec, challenge,
  proof ABI, or acceptance semantics that should have been sealed upstream.
- Do not promise stable exchange through raw MLIR text or bytecode.
- Do not split domains based only on file volume; split when identity,
  authority, lifecycle, and consumer boundaries diverge.

## 6. Exploration, evaluation, and promotion checklist

A candidate is not ready for a durable owner until reviewers can answer:

1. What exact current contract would remain, change, or disappear?
2. Which identity preimages or stable names move?
3. Which authorities, capabilities, and refusal paths change?
4. Can the proposal represent all current admitted examples without weakening
   their non-claims?
5. What valuable capability, conceptual simplification, or future option could
   a different design make possible even if the current cases already pass?
6. What would a clean-room designer build from the intended semantics and
   consumer requirements alone?
7. What counterexample breaks the simplest version of the proposal?
8. Which credible alternative was compared, and why was it rejected or
   deferred?
9. Does the proposal make independent implementation or checking easier?
10. Does it create a second schema or duplicated accepted set?
11. What implementation correspondence is known, absent, or experimental?
12. What new evidence would be required before a status or reliance claim?
13. Is the result a normative rule, architecture explanation, decision,
    roadmap item, evidence record, or guide?
14. Which choice can remain open, and what is its latest responsible decision
    point?
15. What result would cause the team to reverse the decision later?

## 7. Absorption map and deletion trigger

| Material | Durable destination |
|---|---|
| Shared identity, admission, version, and refusal mechanics | `foundation/` specifications |
| Relation ontology and bridge answers | `relations/` specifications and architecture |
| Complete Protocol root and PIR correspondence | `pir/`, or a ratified successor domain |
| Analysis object and authority distinctions | `analysis/` specifications |
| Transformation relations and decision semantics | `compiler/` specifications |
| Endpoint observables and projection admission | `oir/` specifications |
| Supplier binding and operational lifecycle | `realization/` specifications |
| Evidence, appraisal, and reliance rules | `evidence/` plus consumer-owned policies |
| Cross-domain rationale and accepted alternatives | `project/` architecture and decisions |
| Intentionally deferred work | One global roadmap |

Delete a section when every recheck and question it contains has an owned
answer, rejected rationale, or explicit roadmap destination. Delete this page
when the table above is the only content left; the table itself is not durable
documentation.
