# Evidence and assurance records

> **Document kind:** Domain index
> **Document state:** Scaffold
> **Target alignment:** Boundary-aligned to the selected Stage 2 architecture
> **Provisional owner:** `evidence`
> **Authority:** None during the transition. Existing status, formalization,
> test, and evaluation records retain their current bounded roles.

## Purpose

`evidence/` owns how exact producer observations, external receipts, and
comparison results become attributable Evidence records, and how an explicit
Evidence policy appraises those records for one claim. It keeps record
construction, policy-qualified assessment, and consumer reliance distinct.

This is a system domain for Evidence subjects, provenance, appraisal, claim
scope, and policy vocabulary, not a generic document-kind bucket. A semantic
domain defines what an observation means; Evidence can record and appraise it
without redefining that meaning.

## Owns

- Evidence kinds, regimes, and record schemas;
- the `RecordEvidence` boundary from exact producer-owned material to an
  attributable `EvidenceRecord`;
- exact claim, subject, occurrence, revision, issuer, input, environment,
  procedure, and dependency binding;
- provenance, reproduction, derivation, redaction, freshness, and drift
  information;
- facets and grades for structural, operational, formal, backend, and
  cross-implementation conformance;
- residual trust, exclusions, failures, and unattempted scope;
- formalization receipts and source-reading records as Evidence subjects;
- execution, benchmark, replay, parity, and conformance records;
- Evidence-policy vocabulary and the `AppraiseEvidence` transition to a
  qualified `ClaimAssessment`; and
- the Evidence catalog supporting the global status page.

Evidence files may remain beside executable evaluation assets when that keeps
reproduction honest. This domain can index and govern them without forcing all
records into one physical directory.

## Does not own

- the meaning of a raw projection, relation, compiler, endpoint, realization,
  deployment, invocation, theorem, test, or benchmark observation;
- intended Protocol, relation, Analysis, compiler, OIR, or realization
  semantics;
- theorem truth merely because a source or declaration is cited;
- Protocol, OIR, realization, or other semantic admission;
- global current-capability claims, which belong to project status;
- a release, deployment, publication, or other use-specific reliance decision;
- future work order;
- a generic “verified” label spanning unrelated facets; or
- broader conclusions than the exact subjects, observations, procedure, and
  policy support.

## Selected evidence chain

The selected architecture preserves three non-collapsible transitions across
four owner-separated stages:

```text
producer-owned observation or external receipt
  -> EvidenceRecord
  -> policy-qualified ClaimAssessment or EvidenceQualifiedEstimate
  -> consumer-owned, use-specific RelianceDecision
```

`EvidenceQualifiedEstimate` names an Evidence-owned quantitative appraisal over
exact attributable records, policy, units, epistemic form, uncertainty, and
scope. It is not an Analysis proposition. An
`AnalysisEvidenceDerivedEstimate` is instead an Analysis-owned cost judgment
derived through an exact family rule over qualified Evidence inputs. Equal
numbers never erase this owner/type distinction.

The producer owns event ordering, result taxonomy, sensitivity, completeness
frontier, and the statement its raw material actually makes. Evidence cannot
rename a partial log as a complete execution, reinterpret verifier rejection
as operational failure, or turn reproducibility into independent validation.

### Observation to record

`RecordEvidence` closes one record over the exact material, claim or facet,
subject and occurrence references, issuer or recorder, attribution mechanism,
procedure, environment and pins, regime, disclosure scope, and derivation or
redaction lineage. A successful result establishes that the record is
well-formed and attributes its bounded contents under the stated recording
regime.

It does not establish that the claim is true, the procedure is adequate, the
issuer is trusted for an intended use, the result is current, or any consumer
should rely on it. Record refusal is also distinct from storage, signing, or
partial-publication failure when those effectful operations are combined with
logical record construction.

### Record to assessment

`AppraiseEvidence` consumes the exact Evidence set, claim, policy and version,
reference values, trust anchors, context, and freshness basis. Its successful
outcomes may include `supported`, `contradicted`, `insufficient`, `stale`, and
`indeterminate`. Negative or insufficient conclusions are successful policy
results; `AppraisalRefusal` means the policy could not be applied because a
record, dependency, evidence kind, or checker was unavailable, malformed,
unauthenticated, or unsupported.

A durable `ClaimAssessment` binds its Evidence set, policy, trust context,
time or freshness basis, conclusion, validity scope, conditions, and residuals.
A new policy, reference value, trust anchor, or time may yield a different
assessment without changing any Evidence record or semantic subject.

### Assessment to reliance

The relying consumer, not `evidence/`, owns `DecideReliance`. That transition
adds the actual consumer, intended use, use policy, current context and state,
trust anchors, validity interval, expiry, revocation, and residual conditions.
Its successful result may permit, deny, condition, limit, or defer one use.

Two consumers may therefore reach different valid reliance decisions over the
same assessment. One consumer may decide differently for deployment,
publication, benchmark reporting, or release. Reliance does not mutate an
assessment or make its underlying claim semantically true.

## Dependencies and no-backflow rule

Evidence depends on the owning domain for every claim and observation it
records. Each record identifies that authority and the exact semantic,
artifact, transition, or occurrence subjects. It may also depend on external
tools, theorem libraries, hardware, providers, upstream implementations,
reference values, or trust anchors, all attributed and pinned where possible.

No semantic domain depends on the presence of an Evidence record for subject
meaning or identity. A release, deployment, or publication policy may require
an assessment, but that is an explicit downstream consumer policy. No arrow
from observation, record, appraisal, or reliance points backward to change or
admit a Protocol, Interface, Plan, OIR, realization, deployment, or completed
endpoint result.

Authenticating record bytes or an issuer establishes only what the selected
authentication regime states. It neither authenticates every cited subject by
implication nor proves the recorded claim.

## Identity and occurrence rules

An Evidence record identity, when durable, depends on its exact material or
observation identity, claim/facet and subject references, issuer or recorder,
procedure, environment and pins, scope, exclusions, freshness material,
regime, and record content. Equal observed values may therefore produce
different records when their activities, issuers, procedures, environments,
or scopes differ.

Immutable assessment content and appraisal occurrence remain separate. A
repeat appraisal can yield equal assessment content while constituting a new
attributed activity. Evidence attachment never remints the observed semantic
subject. Redaction or aggregation creates derived material with explicit
omissions and lineage; it does not preserve an unqualified source-record
identity.

## Consumers and outputs

- global status cites bounded Evidence records and assessments under its own
  reporting policy;
- maintainers use reproduction and drift results to find conformance gaps;
- decisions may cite Evidence without turning observations into semantics;
- downstream consumers apply their own intended-use policies to qualified
  assessments; and
- guides link to reproducible procedures rather than restating results.

## Bounded executable evidence routes

The [Native FRI/IOR Semantic
Validation](../../evaluation/native-fri-ior/README.md) package is the current
reproduction route for one retained two-lane research case. It records an
early-terminated structural control and a separate frozen exact classical
control with public replay, owner regeneration, named negatives, and explicit
nonclaims. The package remains beside its executable assets; this index does
not convert its reports, fixtures, tests, or construction receipts into an
Evidence record, assessment, property judgment, or implementation-conformance
claim.

Any later `RecordEvidence` operation over that package must bind the exact
case inputs, source ledger, code basis, procedure, environment, result scope,
and final checkpoint. Its admissible claim must distinguish deterministic
source-schedule correspondence, structural construction authority, one-run
receipts, implementation-diversity replay, and unattempted property questions.

## Bridge ownership

`evidence/` owns two separate bridges:

1. raw producer-owned observation, external receipt, or comparison result to
   an attributable Evidence record; and
2. an exact Evidence set plus Evidence policy to a qualified claim assessment.

The producing domain retains authority over what the raw result means. The
claim's semantic owner retains authority over the proposition. The relying
consumer owns the later intended-use decision. Bridge ownership does not
authorize Evidence to widen an observation, and appraisal authority does not
authorize every downstream use.

## Minimum record contract

Every Evidence record should state:

```text
claim or facet
exact semantic, artifact, transition, and occurrence subjects
issuer or recorder and attribution mechanism
inputs and configuration
environment, dependencies, providers, toolchain, and external pins
procedure or checker and its version or identity
observed result and outcome category
covered and uncovered observations
conditions, exclusions, residual trust, and non-claims
freshness material when relevant
reproduction or independent-check path
derivation and redaction lineage when applicable
```

Missing fields narrow or invalidate the record's admissible claim; they are
not filled by assumption.

## Candidate internal topics

- claim, observation, assessment, and outcome taxonomy;
- record schema, attribution, identity, and provenance;
- formalization and external-tool receipts;
- reference and differential Evidence;
- endpoint and backend conformance;
- execution, replay, and partial-effect records;
- benchmarks and performance observations;
- Evidence appraisal, aggregation, and status routing; and
- reproduction, freshness, and drift checking.

## Open design questions

- Should the domain be renamed `assurance/` to avoid collision with Evidence as
  a local document kind?
- What exact record encoding, authentication, signature, issuer, disclosure,
  redaction, retention, and provenance-of-provenance schemas are required?
- Which conformance facets and grades are cross-domain Evidence concepts, and
  which remain domain-specific obligations?
- What Evidence-policy language, reference-value, trust-anchor, freshness, and
  aggregation model can preserve qualified outcomes without implying universal
  proof?
- Which assessments need portable schemas and independent validation, and
  which should remain local recomputations?
- How should global status derive concise claims from records and assessments
  without creating a second manually synchronized inventory?
