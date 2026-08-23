# Current Analysis and property-calculus reconstruction

> **Document kind:** Temporary Stage 4A current-model reconstruction
> **Document state:** Complete for Stage 4A.1; target-neutral
> **Authority:** None. Current normative meaning remains principally in
> [`docs/spec/soundness.md`](../../../docs/spec/soundness.md), with exact seams
> in the Protocol, Relations, and Compiler specifications. Code, registry,
> tests, examples, and status are correspondence evidence only. This page does
> not repair disagreement, select a target, prove a property, or authorize
> implementation or migration.
> **Reconstructed:** 2026-08-22
> **Disposition:** Retain current strengths, conflicts, and unknowns in the
> Stage 4A gap record; delete this page with the temporary package after
> reviewed conclusions have durable owners.

## 1. Reading result

The current property system is a post-admission **Soundness Kernel**, not yet a
general Analysis architecture:

```text
admitted PIR-derived sealed view
  + immutable typed rule catalog and selected bindings
  + exact external parameters and assumptions
  + explicit caller-supplied derivation plan
  -> conditional notion-indexed SecurityJudgment | refusal
```

Its strongest idea is worth preserving: a small evaluator checks an explicit
proof object through closed rule bodies and exact artifact projections; it does
not search for a theorem, accept a provider's claimed bound, or let citation
metadata affect derivability. Soundness, knowledge, and completeness are
notion-indexed, exact hypotheses are inherited, and quantitative loss remains
symbolic where a primitive game is unbounded.

Its principal Stage 4A limitation is scope and factorization. The current
calculus is centered on claim-local security derivations inside one admitted
artifact. It has no first-class question/result families for observer-indexed
equality, trace refinement, distributional relations, intentional change,
cost, relation satisfaction, structural-FS-to-theorem correspondence, general
property transport, or property composition. The result surface also has no
successful semantic negative, unsupported, cannot-answer, malformed, or
checker-failure variants.

## 2. Authority and supported scope

| Surface | Current role | Exact limit |
|---|---|---|
| `docs/spec/soundness.md` | Normative current property calculus | Typed Soundness/Knowledge/Completeness derivation, not general Analysis |
| `docs/spec/kernel.md` | Structural Protocol facts and the stated Binding Lemma boundary | Does not prove the cryptographic FS hop |
| `docs/spec/relations.md` | Current relation artifact/interface correspondence | Does not establish predicate truth or witness satisfaction |
| `docs/spec/compiler.md` | Current Soundness consumer and bound constraints | Does not own property meaning |
| `docs/formalization.md` | Attributed formalization readings and nonclaims | Receipts are not theorem correspondence or zkc property results |
| `docs/status.md` | Exercised checkout snapshot | Tested examples, not general family support |
| `registry/soundness-signature.json` | Native signature content loaded into the executable calculus | Rule authoring plus cited assumptions, not theorem truth |
| `include/zkc/Soundness/`, `lib/Soundness/` | Implementation correspondence | Cannot silently extend normative meaning |
| `test/Soundness/`, Soundness unit tests | Bounded behavior and refusal evidence | No general correctness or cryptographic proof |

The status snapshot reports partial Soundness, partial Completeness, and no
Zero-Knowledge judgment surface. This is an implementation statement, not a
restriction on the ideal Stage 4A target.

## 3. Current subjects, sites, and indices

### 3.1 Subjects and occurrence sites

The current `SecuritySubject` is a closed sum:

```text
ProtocolClaim {
  artifact_id,
  claim_ref
}

ConsumedClaimVector {
  artifact_id,
  consumer_claim_ref,
  ordered_source_claim_refs
}

ExternalInstance {
  subject_schema,
  typed_arguments
}
```

The application occurrence is separate:

```text
ReductionOccurrence {
  artifact_id,
  owner_claim_ref,
  transformer_position,
  output_index
}

PathOccurrence {
  artifact_id,
  claim_ref
}
```

`APPLY` constructs the conclusion subject from the admitted view and exact
site. A binding validates but cannot replace that subject. Direct application
therefore concludes about one exact Protocol claim. Consumed vectors and
external instances are premise subjects in v0.

This separation prevents a caller from choosing a convenient conclusion
subject. It does not provide the exact multi-subject tuples required by Stage
4A relations or property transports.

### 3.2 Security indices

The normative index families are:

```text
SpecialSoundness(track)
ComputationalSpecialSoundness(track)
RoundByRound(track, variant)
StateRestoration(track, variant)
FiatShamir(track, model, variant)
Completeness
```

Admitted tracks are Soundness, Knowledge, and Completeness in only the
versioned combinations the schema admits. The computational regime is derived
from exact primitive-game support in the result; neither a rule, context, nor
caller may author or weaken it.

The implementation additionally carries an identity-bearing quantification
coordinate:

```text
Static | AdaptiveInstance | AdaptiveIndex
```

and lets a rule pattern preserve an exact quantified value through a typed
variable. The normative index grammar omits this coordinate. Shipped registry
indices are static, while widened tests exercise adaptive carry. This is a
confirmed current specification/implementation drift, not a target decision.

## 4. Result and judgment semantics

There is deliberately no generic scalar payload. Result shape is indexed by
the notion:

```text
ExtractionResult {
  nonempty ordered extraction coordinates,
  optional failure bound
}

RoundResult {
  nonempty ordered rounds {
    round_index,
    challenge_space,
    bound,
    optional state_predicate
  }
}

ScalarResult { bound }
```

Information-theoretic special soundness has no decorative zero failure bound.
Computational special soundness has an exact closed failure expression.
Round-by-round results retain each round separately; a maximum is a later
explicit projection. Completeness uses a scalar result but remains a different
property with honest-prover rather than adversarial meaning.

One closed judgment is:

```text
SecurityJudgment {
  exact subject,
  exact SecurityIndex,
  notion-indexed result,
  typed resource-variable declarations,
  kernel-derived hypothesis set
}
```

It means that for every nonnegative well-typed resource valuation, if all
qualitative hypotheses hold, the notion-specific predicate holds for the
subject and result. Primitive-game advantages remain symbolic leaves unless
another exact rule supplies their bound.

For Completeness, the specification says an honest prover holding a witness in
the subject's relation is accepted except with the scalar failure probability.
The current `SecuritySubject` contains no relation operand, current PIR
analysis does not establish relation satisfaction, and current Relations
permanently refuses that inference. The exact relation/model lookup behind
`Holds_Completeness` is therefore external and underrepresented in the current
question.

## 5. Hypotheses and assumptions

Qualitative hypotheses are typed proposition instances. Every rule
application inherits monotonically:

- all specialized premise hypotheses;
- all locally instantiated external hypotheses; and
- one canonical `AssumedJudgmentHolds` proposition for each explicit assumed
  premise.

An assumed external judgment must be marker-free and closed. `DERIVE` alone
adds the canonical marker, and all dependent conclusions retain it after
resource specialization. An assumption leaf cannot be the root of a successful
Protocol target derivation.

The v0 derivation algebra has no qualitative-hypothesis discharge and no Cut.
This keeps conditionality visible but also means the current engine cannot
represent all proof styles as native derivations.

## 6. Exact quantitative layer

Rule templates and completed runtime expressions are distinct categories.
Typed quantity templates include exact rational arithmetic, rule parameters,
artifact facts, contract-round facts, premise coordinates, and declared
resources.

Bound templates distinguish:

- exact statistical quantities;
- typed projections of admitted premise results; and
- exact primitive-game instances with total resource substitutions.

The v0 executable normal form is:

```text
ground rational
  + sum(nonnegative rational coefficient * exact primitive-game advantage)
  + sum(nonnegative rational coefficient * resource monomial)
```

Symbolic products, unsupported symbolic maxima, negative coefficients,
inexact powers, partial substitutions, and unresolved exact instances refuse.
No approximation is silently introduced.

This exact monotone algebra is a strong reusable mechanism. It cannot be
treated as the sole result algebra for trace equality, counterexamples,
distributional couplings, zero knowledge, or cost observations.

## 7. Rule, binding, and context model

### 7.1 Rule declaration

A current `SoundnessRule` declares:

- exact revision and admitted/declared status;
- typed parameters and resources;
- typed premise and artifact-fact ports;
- machine-condition and external-hypothesis slots;
- exact parameter pins;
- conclusion index; and
- one closed rule-body variant.

The ten implemented body families cover:

- special-soundness, native RBR, computational, and completeness entries;
- special-soundness and RBR preservation;
- selected-round scaling;
- special-soundness to RBR;
- RBR to state restoration; and
- state restoration to duplex Fiat--Shamir.

These are not arbitrary callbacks. `RULE_WF` checks a closed syntax and exact
body-signature table.

### 7.2 Rule binding

A `RuleBinding` maps one rule to exact Protocol structure:

- application anchor;
- subject schema;
- premise subject relations;
- artifact-fact projections;
- parameter and machine-condition arguments; and
- local external hypotheses.

One premise port consumes exactly one judgment under an exact subject
relation, index/result schema, resource schema, and total substitution. Whether
that premise is recursively derived or explicitly assumed is orthogonal.

The `ArtifactProjection` vocabulary is intended to be the finite complete read
channel from the admitted view. Callers cannot inject an arbitrary resolver.
Two executable projection kinds, `BoundRelationAnchorCount` and
`CommittedArity`, are missing from the normative projection grammar even
though registry rules use them and normative FS prose relies on the anchor
count. This is both internal normative inconsistency and code/spec drift.

### 7.3 Catalog, signature, and context

`freezeSoundnessCatalog` owns schemas, rules, and bindings, resolves every
exact reference, re-runs `RULE_WF`, and produces one immutable
registry-independent executable authority.

The surrounding `Signature` separates:

- the executable catalog; from
- annotations containing statements, citations, source anchors,
  formalization receipts, and surveyed absences.

Kernel judgments receive the catalog, never the annotations. An editorial
change or receipt cannot mint a rule or discharge a premise.

`SoundnessContext` owns the immutable catalog, exact selected binding refs, and
resolved external parameters. Selection makes only named bindings executable;
it cannot alter a rule, choose a plan, or weaken arithmetic.

## 8. Explicit derivations

The plan and evaluated witness share one recursive shape:

```text
DerivationPlan =
    Assume(exact external judgment)
  | Apply {
      site,
      binding_ref,
      premise plans by exact port
    }
```

The caller supplies the plan. `DERIVE` performs no theorem search, provider
resolution, cheapest-path selection, fallback, or implicit assumption.

`RULE_WF` checks syntax and typing only. `APPLY` checks exact occurrence,
binding, claim coverage, premise subjects, result schemas, substitutions,
machine conditions, artifact projections, quantities, rule-body evaluation,
regime, and inherited hypotheses. `DERIVE` checks the finite rooted plan and
exact target.

Several valid plans may derive the same target. The current runtime result has
artifact, target, and evaluated root but no distinct question, basis,
derivation, or conclusion identity.

The persisted witness records the whole-signature digest and a conclusion-
judgment digest while embedding the request and plan separately. Consequently
several derivations of one conclusion may share the judgment digest, and a
signature with different unused content changes the signature identity. The
current checker may rederive an equal judgment under another signature while
reporting the signature mismatch. Stage 4A must not infer a final identity
policy from this behavior.

## 9. Exact current guarantee and residual trust

Successful `DERIVE` establishes the exact interpretation of:

- the encoded rule bodies and bindings;
- admitted-view facts;
- external premise inputs;
- exact parameters and conditions; and
- the explicit derivation plan.

The intended cryptographic conclusion still depends on:

- truth and faithful encoding of every used rule;
- faithfulness of each binding to its Protocol occurrence;
- truth of all residual hypotheses;
- adequacy of the admitted security-notion and primitive-game definitions; and
- correspondence between the admitted Protocol model and the concrete
  protocol of interest.

`RULE_WF`, signature loading, tests, receipts, and source drift checks establish
none of those propositions by themselves.

## 10. Current relation, FS, and Compiler seams

### 10.1 Relation satisfaction is absent

Current relation compilation and predicate meaning remain external. The
current correspondence tool can compare contract, artifact, anchor, header,
and selected interface facts. Its negative report can retain agreements and
disagreements. It does not prove intended predicate meaning, absence of
underconstraint, witness-generator correctness, bytes-to-anchor preimage
correspondence, or satisfaction by an occurrence-local private witness.

There is no current `RelationSatisfies`. R1CS property examples retain
relation-dependent facts as external hypotheses.

### 10.2 Current FS path fuses construction and property reasoning

The current duplex path rule applies inside one artifact/claim calculus:

```text
StateRestoration premise
  + exact duplex artifact projections
  + local assumptions and loss expression
  -> FiatShamir SecurityJudgment
```

The current Protocol Kernel Binding Lemma remains a stated proof obligation;
its bounded security clause depends on a selected Soundness rule. The FRI
fixture exercises RBR, grinding scaling, state restoration, duplex loss,
challenge coverage, and refusal when required duplex facts are absent.

There is no current separately admitted Fresh Protocol, FS Protocol,
`CheckedFSConstruction`, `FSCompile` applicability result, or general
property-specific `PropertyTransport`. Stage 3 intentionally selects that
factorization for the target.

### 10.3 Compiler embeds this calculus

Current Compiler requests contain Soundness contexts, derivation domains,
allowed bindings/games/hypotheses, and Soundness bound expressions. `VALID`
re-runs `DERIVE` for every target. The shared evaluator prevents a second
pricing semantics but does not provide an independent qualified Analysis input.

Current `PreservationClaim` is an unchecked open attribution collected after
transform checking. It never establishes property transport.

## 11. Artifact-global coverage seam

The implementation introduces `ArtifactJudgment`, `DerivationCoverage`, and
`judgeArtifact` to check whether a family of derivations covers the Protocol's
required claim and round surface. The CLI reports this result, tests say it
closes a previously unstated final-sequent gap, and status relies on the
behavior.

No normative specification page names this operation or result. It is unclear
whether the final target should classify it as:

- structural Protocol obligation accounting;
- an Analysis question over a set of derivations; or
- another exact bridge owner.

The current implementation cannot decide that ownership question.

## 12. Formalization and external theorem evidence

Every rule annotation records either a formalization receipt or a surveyed
absence. Receipt checking can pin external revision, printed theorem type, and
axiom profile. This is valuable attributed Evidence.

It remains deliberately outside the executable catalog. The current external
reading reports missing or incomplete links for the desired end-to-end chain,
including several entry theorems, special-soundness-to-RBR, RBR-to-state
restoration, and state-restoration-to-duplex-FS. A concrete bridge from exact
PIR subject to formal subject and external theorem remains future work.

Therefore:

```text
source citation or proof artifact
  != checked theorem correspondence
  != model adequacy
  != exact zkc property judgment
```

## 13. Exercised implementation correspondence

The native implementation provides:

- registry-free owned declaration and runtime values;
- a PIR adapter that accepts only `AdmittedPirArtifact` and emits an owned
  MLIR-free view;
- immutable catalog freezing and exact signature digests;
- typed refusal phases and codes;
- exact rule-body and bound evaluation;
- explicit plan encoding and witness rederivation; and
- one shared evaluator used by the Compiler.

The Python reference oracle is implementation-diverse but partial. It checks
canonical Soundness signature content and the structural and typing skeleton of
selected derivations, including sites, bindings, edges, subjects, indices,
resources, and inherited hypotheses. It intentionally stops before numeric
bound evaluation and therefore is not a second full `DERIVE` implementation.
Native `zkc-derive --check` instead re-runs the same native evaluator across a
process boundary and compares the conclusion digest. These assurance lanes and
their exact limits are reconstructed in [current history, authority, and
consumers](current-history-authority-and-consumers.md).

The live registry inventory is:

| Item | Count |
|---|---:|
| Rules | 30 |
| Admitted rules | 26 |
| Declared rules | 4 |
| Direct bindings | 35 |
| Reduction bindings | 30 |
| Path bindings | 5 |
| Admitted index instances | 10 |
| Subject schemas | 3 |
| Primitive-game definitions | 5 |
| Machine deciders | 26 |
| Proposition schemas | 27 |

Six completeness rules exist. FRI, LogUp, and Sigma forms are admitted;
EvalOpen, R1CS batch, and Sumcheck forms are declared. Registry and tests also
exercise soundness/knowledge chains, computational KZG, RBR/SR/duplex-FS, and
KZG preservation.

Inspected tests cover catalog well-formedness and mutation refusals, exact rule
application, adaptive quantification in a widened schema, persisted witnesses,
two signatures over one artifact, separate completeness, artifact-level
coverage, FRI/grinding/FS chains, relation positive/negative reports, and
compiler consumption. These are bounded assertions. This reconstruction did
not rerun the Soundness suite.

## 14. Confirmed current conflicts and unowned surfaces

| Item | Current fact | Classification |
|---|---|---|
| Security quantification | Implemented, encoded, tested, and identity-bearing; omitted from normative index grammar | Spec/code drift |
| Two artifact projections | Required by executable rules and code; omitted from normative projection grammar | Internal spec inconsistency plus drift |
| Artifact-global judgment | Implemented, CLI-visible, tested, and used by status; no normative owner | Unowned semantic surface |
| Relation correspondence basis | Specification expects derivation-linked field agreement and canonical result identity; CLI accepts optional caller field order, reads no derivation, and emits no report ID | Normative/implementation gap |
| Completeness relation | Normative meaning refers to subject relation; exact relation and satisfaction basis absent from the subject | Underclosed semantic model |
| Site in completed judgment | Site is used during application but omitted from `SecurityJudgment`; documented preservation/interleaving limitations result | Known model limitation |
| Derivation identity | Result and witness do not distinguish proposition, used basis closure, and exact derivation identity | Unowned identity split |
| Live authority | `SecurityJudgment` and `DerivationResult` are public owned values, not opaque checked-occurrence capabilities | Missing target authority boundary |
| Qualified outcomes | Kernel returns result or refusal; no semantic Negative/Unsupported/CannotAnswer/Malformed/CheckerFailure result | Underclosed outcome algebra |
| External formal proof bridge | Receipts and absences exist; theorem/model/subject correspondence does not | Deliberate evidence-only boundary |
| Relation anchor grounding | Broad Soundness view, first-match heuristics, and special projections remain in current tool path | Conflicts with Stage 3 typed grounding/read closure |
| Preservation | Open attributed string, never checked property transport | Deliberate current nonclaim and missing target seam |
| Registry comment count | Source comment says 27 rules while registry/test assert 30 | Minor source-comment drift |

## 15. Current strengths to preserve

1. Protocol admission and property analysis are separate.
2. A rule is a typed conditional transformer, not a theorem name plus opaque
   callback.
3. Subjects, sites, notions, results, hypotheses, resources, and games are
   independently typed.
4. The evaluator reads an immutable purpose-built admitted view, not mutable
   MLIR or an ambient registry.
5. Artifact projections form a finite reviewable read vocabulary.
6. Rule search and plan choice stay outside the small checker.
7. Exact assumptions remain visible and inherit monotonically.
8. Computational advantages remain symbolic and instance-specific.
9. Unsupported quantitative forms refuse rather than approximate.
10. Annotations, citations, receipts, and status do not affect derivability.
11. Several derivations may support one target without creating artifact-global
    property authority.
12. Compiler reuses the same evaluator rather than restating Soundness, while
    `DECIDE` remains same-authority recomputation rather than implementation-
    independent checking.

## 16. Current-to-frozen seam map

| Current model | Frozen Stage 3 pressure | Classification |
|---|---|---|
| Claim-local SecuritySubject | Exact property-specific Protocol/Core/Interface/Plan/relation/occurrence tuples | Generalize with family types |
| Soundness/Knowledge/Completeness indices | Equality, trace, distribution, intentional-change, cost, and later property families | Add without universal payload |
| One broad `SealedSoundnessView` | Source-owned purpose-specific views with complete declared read closure | Split and attenuate |
| Whole catalog plus selected bindings | Exact model/rule/theorem and transitive used dependency basis | Re-factor identity |
| `Assume`/`Apply` tree | Direct checks, internal derivation DAGs, external proofs/certificates, and exact correspondence | Federate basis lanes |
| Result or refusal | A/N/Unsupported/CannotAnswer/Refused/Malformed/CheckerFailure | Expand and qualify |
| Same-artifact SR-to-FS rule | Admitted Fresh and FS Protocols, checked construction, theorem applicability, property-specific transport | Replace/factor |
| No property-composition calculus | Property-specific composition after checked structural composition | Add |
| No `RelationSatisfies` | Exact occurrence-local satisfaction owner and result | Resolve ownership |
| Conclusion digest plus whole signature | Separate proposition, basis, derivation, judgment, and replay identities | Redesign |
| Formalization annotations | Checked statement/model correspondence plus external proof lane | Retain evidence; add semantic bridge |

## 17. Open questions preserved for redesign

- Which family schemas genuinely share a common judgment lifecycle but not a
  common result calculus?
- What exact semantic proposition remains stable across several proof engines
  and several derivations?
- What is the smallest explicit subject tuple for each equality, trace,
  distribution, property, cost, FS, transport, and composition question?
- Which owner constructs each purpose-specific view, and how is adequacy
  checked when a rule introduces a new read?
- What exact model, adversary, oracle, state, initialization, auxiliary-input,
  termination, abort, and resource fields enter each property identity?
- How are external statement matching, model correspondence, proof checking,
  and zkc inference kept independently visible?
- Which finite relations have complete direct decision procedures capable of
  producing successful negative results?
- Does artifact-global coverage belong to PIR structural accounting or
  Analysis over a derivation family?
- Does `RelationSatisfies` belong to Relations because it defines predicate
  truth, or to Analysis because it is a semantic judgment service?
- What semantic content does `FSCompile` establish before a particular source
  property is transported?
- Which property-composition rules are valid for sequential, interleaved,
  shared-challenge, repeated, and failure-capturing compositions?
- What exact Zero-Knowledge experiments and result forms fit the target without
  treating all probabilistic properties as one calculus?
- Which named consumer justifies persisting a proof object or Analysis result?

## 18. Reconstruction conclusion

The current Soundness Kernel is a strong seed: typed, exact, post-admission,
conditional, plan-driven, independently re-checkable in its intended scope,
and honest about theorem and model trust. It should become one Analysis basis
profile rather than be stretched into the whole Analysis domain.

Stage 4A must preserve the small-checker discipline while introducing a
zkc-native semantic proposition layer, family-indexed subjects and results,
federated direct/internal/external checking bases, exact model and theorem
correspondence, full qualified outcomes, and property-specific transport and
composition. Neither a proof-assistant theorem nor the current class hierarchy
should define that architecture.
