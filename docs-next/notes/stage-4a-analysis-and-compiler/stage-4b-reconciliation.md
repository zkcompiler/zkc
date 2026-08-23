# Stage 4A and Stage 4B peer-boundary reconciliation

> **Document kind:** Temporary cross-branch reconciliation record
> **Document state:** CLEAN and CLOSED Stage 4A peer-boundary audit; Stage 4B
> remains unactivated
> **Authority:** None. This record does not define Analysis, Compiler, OIR, or
> Realization semantics; establish a property, projection, realization, cost,
> or endpoint result; admit a subject; mint authority; activate Stage 4B; or
> reopen a frozen Stage 3 decision.
> **Inputs:** The frozen Stage 3 Stage 4A and Stage 4B entry contracts, durable
> Stage 3 target owners, the selected Stage 4A target, and the durable OIR
> and Realization scaffolds
> **Disposition:** Absorb the shared boundary into the durable Stage 4A
> architecture and exact Analysis/Compiler owner pages. Retain only the bounded
> Stage 4B handoff and reversal condition after Stage 4A closes; delete this
> page with the temporary package.

## 1. Reconciliation result

The peer boundary is **CLEAN and CLOSED**. Stage 4A and the unactivated
Stage 4B branch agree on their shared subject, observation, authority,
occurrence, outcome, and noninterference boundaries. No frozen Stage 3 target
or handoff needs reopening.

The four former Stage 4A precision conditions are closed:

1. a Compiler decision may identify and, during one live operation, retain an
   independently PIR-admitted target, but Compiler never mints or serializes
   Protocol admission;
2. Stage 4B facts enter Analysis or Compiler only as exact later-owned
   qualified results, never as raw subjects, ambient registries, or inferred
   feasibility;
3. shared occurrence and path maps retain their exact domain, totality,
   guard, multiplicity, order, failure, terminal, nonproduction, and
   availability meaning; and
4. default OIR projection and Realization remain invariant under Compiler
   search, proposal, path, domain, assessment, and selection history when
   their explicit Stage 4B inputs are unchanged.

The selected target and durable architecture now preserve all four clauses.
They remain Stage 4B intake and future cross-branch validation conditions, not
permission to design or activate Stage 4B here.

Final closure also hardened two adjacent seams without changing either branch's
meaning: cold selected-target transfer is a separately authorized reconstruction
bundle rather than a property of the decision record, and a future relation-
facing OIR transition requires the complete source-authority envelope rather
than a source ID, capability name, and read set.

The frozen Stage 3 handoff remains an historical input. Its prospective
relation-satisfaction wording is resolved by the durable Stage 4A owners:
Relations owns base occurrence-local `RelationSatisfies`; Analysis consumes its
exact result and owns family-specific property judgments and transport. This is
not a correction to the frozen snapshot and grants no Stage 4B authority.

## 2. Shared semantic vocabulary

Stage 4A imports without redefining the Stage 3 meanings of:

- `ProtocolId`, `ProtocolInterfaceId`, and `ProverPlanId`;
- endpoint roles and exact Protocol, Interface, and Plan occurrences;
- observer sets and protected observations;
- event/action occurrence and potential-versus-action-occurring distinctions;
- transcript framing and schedule order;
- challenges, checks, claims, artifacts, failures, terminals, aborts,
  nonproduction, divergence, and completion;
- boundary-indexed existence, knowledge, and availability; and
- source-owned views, complete read manifests, adequacy, process-local
  authority, qualified outcomes, persistence, and cold replay.

An Analysis profile may select an exact subset through a source-owned view. It
cannot change the selected fact's meaning. An OIR projection profile may read
the same owner facts through its own exact contract. Equal labels or carrier
positions do not join the two reads.

Stage 4B introduces later-owned subjects and occurrences, including:

```text
OirId
ProjectionBasis
LocalOirValid result
ProjectionCorrect result
ProjectedOirCapability
RealizationId and target identity
RealizesOir result
supplier and deployment identities
emission, activation, invocation, run, and session occurrences
abstract endpoint and concrete runtime results
```

None is implied by a Protocol property or Compiler decision. Conversely, no
Stage 4B result changes an admitted Protocol or its Analysis proposition.

## 3. Exact later-owned input contract

An Analysis question or Compiler assessment reads a Stage 4B result only when
its request names an exact typed input:

```text
Stage4BOwnedFactOrValue<R> {
  owner_domain,
  result_family_and_regime,
  complete_subject_tuple,
  exact_qualified_outcome_and_polarity,
  exact_maps_and_read_manifest,
  dependency_closure,
  semantic_or_checker_basis,
  exact_owner_operation_policy_disposition:
    BoundTo(exact owner operation-policy identity and authenticated contract)
      | OwnerDefinesNoOperationPolicy(
          exact owner capability-contract identity, exact capability ABI),
  exact_transitive_source_operation_policy_dependency_closure with exactly one
    such authenticated disposition for every direct and transitive source,
  exact_checked_result_authority_binding created by the source owner, including
    the portable result-record coordinate or owner-local result-record reference,
    complete origin coordinates, admitted semantic facts, qualified outcome,
    assurance, residual trust, exact owner-policy disposition, and complete
    transitive source-policy closure,
  residual_trust,
  inert_OwnerCapabilityRequirement naming the exact capability contract, ABI,
    operand/result binding schema, and freshness/lifetime requirements matching
    that checked-result binding whenever a semantic fact or value is consumed,
  extraction_and_comparison_law when used quantitatively
}
```

The record contains only the capability requirement, never the token. An
affirmation-requiring consumer separately supplies and accepts only a fresh
matching affirmative capability. A consumer that explicitly requests an exact
negative polarity must instead separately supply the matching negative owner
capability. In both cases the exact immediate owner-policy disposition and every
source disposition in the transitive source-policy dependency closure are
checked. Every bound policy must permit this consumer and use; the no-policy
variant is legal only under its exact authenticated owner capability contract.
A portable record, ID, or qualified non-result
supplies neither.

The reverse relation-facing OIR seam follows the same authority discipline. A
future OIR transition must take the exact admitted `RelationInterface` or exact
affirmative checked correspondence value; its complete
`ExactAdmittedSubjectAuthorityBinding` or
`ExactCheckedResultAuthorityBinding`, inert `OwnerCapabilityRequirement`,
authenticated owner-policy/no-policy disposition, and canonical total
transitive source-policy closure; a separately supplied fresh binding-matched
capability of the same affirmative polarity; and an exact OIR `NamedConsumer`
plus typed operation purpose. It
must freshly authorize every bound policy and explicit no-policy contract/ABI
branch for that use. This record neither selects the OIR-owned contract and
result nor activates the transition.

The complete subject tuple includes exactly the coordinates read by `R`, which
may include:

```text
ProtocolId
ProtocolInterfaceId and endpoint role
ProjectionBasis
ProverPlanId and affirmative CheckedPlanRealizes when the basis reads Plan
OirId
realization, target-contract, or supplier-binding identity
deployment or invocation occurrence when the result is occurrence-sensitive
```

The following remain non-interchangeable:

- `AdmittedOir` establishes only `LocalOirValid`;
- affirmative `CheckedProjection` and its live `ProjectedOirCapability`
  establish the exact source-relative `ProjectionCorrect` result;
- affirmative `RealizationCheckResult` and `AdmittedRealization` establish the
  exact target-specific `RealizesOir` result;
- supplier binding, deployment, and invocation have later distinct gates; and
- an endpoint execution result says only what its exact abstract or concrete
  occurrence contract states.

Analysis or Compiler may consume one of these exact results as a premise. It
cannot synthesize the result from a property, widen it to another subject
tuple, change polarity, or infer a later lifecycle gate.

## 4. Selected-target handoff

A qualified Compiler decision binds one exact decision domain and returns a
decision-supported best class/representative, complete Pareto frontier with any
policy-permitted representative, or no-eligible result. It does not create a
target, and the certificate branch need not create a candidate assessment. A
selected-target handoff exists only when the exact decision payload names or
permits the chosen transition member; `NoEligibleCandidate` yields no such
handoff.

During a live same-process handoff for such a decision-supported member, a
result bundle may carry two independent products:

```text
QualifiedCompilerDecision
independently PIR-minted AdmittedProtocol for the selected target
```

The decision proves only its bounded comparison claim. The Protocol capability
proves only PIR admission. Neither casts to the other.

A portable decision record transitively identifies the exact selected
candidate and target through its branch support and qualification-resolution
dependencies, but it contains neither target carrier material nor a
reconstruction manifest. A cold handoff requires the separate durable
`CompilerSelectedTargetHandoffBundle<D,Q>`: the exact decision result, selected
member support, exact candidate and equality path, canonical target carrier and
PIR reconstruction material, and fresh creation/retention/disclosure
authorization under the exact `CompilerResultOperationPolicy` and every
governing source policy or explicit no-policy contract for the exact Stage 4B consumer and typed handoff
purpose. Decision-replay permission does not imply handoff permission. Missing
material, a local dependency, unavailable governance, or policy denial means no
cold handoff exists. The consumer must still independently reauthenticate and
readmit the target through PIR; relying on the decision claim also requires
separately reconstructed fresh Compiler decision authority for that exact
consumer and purpose. Neither record implies Interface, Plan, OIR,
realization, supplier, deployment, invocation, execution, Evidence, or reliance
authority.

Stage 4B may project or evaluate any independently admitted Protocol candidate
before Compiler selection. Selection is not a prerequisite for projection or
realization checking.

If the same Protocol transition case is assessed under multiple Plans,
projection bases, OIRs, realizations, or target contracts, those are distinct
assessments unless an explicit higher-level decision problem makes the later
configuration part of its candidate identity. A Protocol-level Compiler
decision does not silently select any of those later subjects.

## 5. Occurrence, path, and projection-map firewall

Every shared map states:

- exact source and target occurrence domains;
- total, partial, injective, surjective, split, merge, or quotient law as
  applicable;
- guard and multiplicity agreement;
- `EventActionOccurs` interpretation;
- potential-versus-action-occurring treatment;
- transcript, framing, and schedule ordering;
- protected-observation preservation or exact permitted change;
- failure, terminal, abort, nonproduction, and divergence correspondence; and
- boundary- and path-indexed existence, knowledge, and availability when read.

A Compiler semantic path names independently admitted Protocol intermediates
and checked transition edges. Producer-internal MLIR or e-graph nodes are not
semantic path members. Neither path kind enters default OIR projection.

For equal complete `ProjectionInput` values, `ProjectEndpoint` and
`CheckProjection` ask the same Stage 4B question regardless of:

- search algorithm, job, budget, seed, or provider;
- proposal source, recipe, provenance, or internal trace;
- Compiler semantic path, except where that path changes an explicit admitted
  projection input;
- candidate-domain formation, closure proof, assessment, comparison, or
  decision; or
- Evidence records and consumer reliance.

Realization has the analogous invariance when its exact admitted OIR and
explicit realization inputs are unchanged.

`CheckAnalysisCoverage` uses property-surface occurrence and projection maps.
Those names do not mean OIR `CheckProjection`, and an affirmative property-
coverage result does not establish `ProjectionCorrect`.

## 6. Interface and Plan read discipline

A Protocol-only Analysis proposition is invariant under substitution of
Interface, Plan, OIR, realization, supplier, deployment, invocation, or runtime
state.

When an Analysis question reads an Interface or Plan field, it includes:

```text
exact Interface or Plan identity
live admitted subject authority
owner-created purpose-specific view
complete semantic read manifest
source-owned adequacy result
```

It additionally includes affirmative `CheckedPlanRealizes` when structural
obligation coverage enters the conclusion. Plan admission alone is not that
coverage result.

Stage 4A does not assign Stage 4B's `ProjectionRelevant`, `RealizationOnly`, or
`ExternalSupplyRequirement` placement classes. OIR and Realization declare
their own exact Plan reads and placement results. The same Plan fact may not
arrive ambiently at both boundaries.

## 7. Objective and assessment association

`EvidenceQualifiedEstimate`, `AnalysisEvidenceDerivedEstimate`, and
`Stage4BOwnedFactOrValue` are pairwise disjoint owner and epistemic kinds.

A raw OIR, admitted realization, runtime observation, build result, supplier
binding, or endpoint receipt is not an objective value. A Stage 4B quantitative
result becomes usable only under an exact later-owned result contract with
units, model, subject tuple, basis, and comparison law. Endpoint cost remains
`Unsupported` until that owner defines such a result.

A runtime observation becomes an attributable Evidence record or
`EvidenceQualifiedEstimate` only through the Evidence-owned recording and
appraisal bridge. Analysis may derive an `AnalysisEvidenceDerivedEstimate` only
through an exact named inference rule over such qualified Evidence inputs.
Equal numeric values do not convert either estimate type into the other, a
Stage 4B fact, or an exact structural cost theorem.

An independently owned Stage 4B result retains only its own exact semantic and
checking operands:

```text
exact target ProtocolId
exact Interface and endpoint role when read
exact ProjectionBasis and Plan when read
exact OIR, realization, and target-contract identities when read
exact Stage 4B qualified result, polarity, basis, authenticated owner operation-
  policy disposition, total transitive source-policy dependency closure, exact owner result-
  origin binding, and residual trust
units, model, uncertainty, and comparison law when quantitative
```

It does not name a future `AssessmentId`, comparison alternative, decision, or
assessment portfolio. After the fact exists and one semantic candidate exists,
a separate Compiler-owned inert `AssessmentInputUseRecord` binds:

```text
exact ExactCompilerValueRef<DecisionPolicy> and required-input schema
exact ExactCompilerValueRef<AssessmentInputPortfolio>, whose body retains the
  exact CandidateRef, transition case, and admitted target
exact canonical typed portfolio-slot coordinate
exact independent Stage 4B fact identity
exact checked-result authority binding, authenticated immediate owner-policy
  disposition, and total transitive source-policy dependency closure
exact matching inert OwnerCapabilityRequirement
checked unique body membership plus subject, candidate, target, policy,
  polarity, owner-policy disposition, assurance, trust, unit, and model
  association
```

The two exact Compiler value references use the durable disjoint portable-ID or
same-owner/generation local-handle law. Neither coordinate is ambient lookup
authority, and a local Stage 4B input makes this portfolio, use record, and
downstream assessment chain owner-local.

The occurrence-local `CheckedAssessmentInputUse` separately retains the exact
fresh matching owner capability for its authority lifetime. The later
assessment consumes that live checked-use capability and the inert record; only
the record may enter content identities or replay material. The Stage 4B fact
therefore remains invariant under Compiler policy, portfolio membership,
comparison-domain formation, and decision history.

Every Compiler use, disclosure, persistence, and replay of the fact or use
record must freshly validate the immediate Stage 4B owner-policy disposition
and every disposition in its transitive closure for the exact consumer and
purpose. Every bound policy must permit the use; an authenticated no-policy
contract is preserved rather than silently omitted. Retaining the closure
coordinate is not itself authorization.

Compiler persistence and replay follow the durable Compiler disposition rule:
each bound-policy preimage or explicit no-policy owner capability-contract/ABI
preimage and its reconstruction/admission material must be retained when the
fact is retained, then freshly reauthenticated through policy authority or
owner admission/mediated confirmation before a fresh Stage 4B capability may be
accepted. This peer record does not create a weaker replay path.

No endpoint condition exists when the compilation problem does not name one.
Ambient backend or registry state cannot reject or reorder candidates.

## 8. Outcome separation

These result families do not cast to one another:

| Result family | Exact owner meaning | Forbidden reinterpretation |
|---|---|---|
| Protocol failure, terminal, abort, or nonproduction | Stage 3 operational Protocol semantics | Runtime infrastructure failure or Analysis polarity |
| OIR abstract endpoint result | OIR abstract execution contract | Concrete realization outcome without an exact realization result |
| Production, provider, executor, or partial-effect failure | Realization/runtime occurrence | Protocol semantic failure, pure refusal, or candidate ineligibility |
| Verifier `Reject` | Completed exact endpoint occurrence result | Analysis `Negative` or checker failure |
| Analysis affirmative or fact-retaining negative | Exact family proposition | Endpoint success, rejection, feasibility, or reliance |
| `Unsupported`, `CannotAnswer`, `Refused`, `Malformed`, `CheckerFailure` | Non-completed owner-qualified outcomes | Either semantic polarity or `NoEligible` |
| Evidence record | Exact attributed observation | Theorem, property, relation, endpoint authority, or reliance |

Prover nonproduction is not a Protocol terminal unless an exact checked map
states that correspondence. Executor failure is not an exact transform or
property counterexample. Verifier rejection may be Evidence about one run but
does not refute a universal property by itself.

## 9. Reopening and activation decision

The peer audit makes these decisions:

- **Frozen Stage 3 semantic target:** do not reopen.
- **Frozen Stage 4A entry contract:** consume as written; do not amend.
- **Frozen Stage 4B entry contract:** do not reopen.
- **Durable OIR and Realization scaffolds:** retain their dormant semantics;
  Stage 4A adds only the complete relation-source intake envelope required
  before any later relation-facing OIR variant may activate.
- **Stage 4B activation:** remain unactivated.
- **Stage 4A target:** frozen and promoted after this reconciliation was
  reflected in target semantics, scenarios, matrices, and durable owners.

Reopen the peer boundary only if a later accepted design makes a Plan, OIR,
realization, endpoint configuration, deployment, or runtime occurrence part of
the semantic Compiler candidate identity rather than an explicitly associated
assessment input. That would require an equal-resolution product-domain model,
new ownership and replay analysis, and a renewed Stage 4B cross-audit.

No such condition is required by the selected Stage 4A target.
