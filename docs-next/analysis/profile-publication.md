# Analysis Semantic Profile Publication

> **Document kind:** Target semantic specification and publication boundary
> **Document state:** Active non-normative target
> **Provisional owner:** `analysis`
> **Authority:** None during transition. This page fixes the six Analysis
> profile boundaries consumed by the Foundation publication mechanism. Current
> normative specifications remain under [`docs/`](../../docs/README.md).

## 1. Publication rule

Analysis publishes one common calculus profile and two independent profile
branches. A profile body is reconstructed from its strict manifest, the exact
marked owner fragments named there, and the Foundation basis. The manifest's
literal supported-kind sequence is authoritative and is required to equal the
corresponding explicit catalog in
[`analysis-model.md`](analysis-model.md#20-analysis-language-profiles-and-exact-evaluators).
There is no set subtraction, host-class enumeration, filesystem discovery, or
ambient Analysis registry.

Each profile has its own local body-compiler, semantic-law,
evaluator-signature, and failure-schema declarations. A child body compiler
reuses its parent's canonical Analysis carrier rules through an exact imported
declaration, then restricts formation to the child's literal supported-kind
set and complete owner schema. This is delegation through a typed profile
edge, not copied law text or a host dispatcher. The generated subject-language
catalog contains one exact row per supported kind and no default row.

The import graph is:

```text
analysis-kernel
  +--> analysis-cryptographic-property
  |      +--> analysis-afk-transport
  |             +--> analysis-afk-theorem-source-validation
  |
  +--> analysis-incremental-composition
           +--> analysis-incremental-composition-source-validation
```

The cryptographic-property and incremental-composition branches do not import
one another. A source-validation profile imports its semantic parent; no
semantic parent imports a validation child. Exact direct owner uses remain
direct edges even when another import reaches the same owner transitively.

<!-- zkc-profile-source:analysis-kernel-publication:start -->

## 2. Common Analysis kernel profile

```text
AnalysisKernelProfileSourceV0 = {
  profile_family: "analysis.kernel",
  revision: 0,
  direct_imports: [],
  supported_subject_kinds: ["analysis.hypothesis-context"]
}

AnalysisKernelBodyCompilerV0(kind,body) =
  require kind = "analysis.hypothesis-context";
  require body satisfies the exact kernel-owned schema;
  AnalysisDomainBodyV0(body)

AdmitAnalysisKernelSubjectV0(
  exact profiled candidate,
  exact evaluator support,
  deterministic limits)
  -> AnalysisKernelAdmissionOutcomeV0

AnalysisKernelAdmissionOutcomeV0 =
    Affirmative(AdmittedAnalysisSubject)
  | Unsupported | MissingDependency | CannotAnswer | KindMismatch
  | Refused | Malformed | DeterministicLimitExceeded | CheckerFailure
```

The kernel owns only the reusable body calculus, exact source-ingress grammar,
question/goal/proposition chain, named-premise grammar and total intake,
basis/support/validation separation, common failure partition, lifecycle, and
the family-neutral empty hypothesis context.
It imports no downstream profile and establishes no cryptographic or
composition property.

<!-- zkc-profile-source:analysis-kernel-publication:end -->

<!-- zkc-profile-source:analysis-property-publication:start -->

## 3. Cryptographic-property profile

```text
AnalysisCryptographicPropertyProfileSourceV0 = {
  profile_family: "analysis.cryptographic-property",
  revision: 0,
  direct_imports: [
    AnalysisKernelLanguageProfileId,
    PIRCanonicalFramedFSProfileId,
    PIRInteractionProfileId,
    PIRPublicSetupProfileId,
    RelationsProfileId
  ],
  supported_subject_kinds:
    AnalysisCryptographicPropertySupportedKinds
}

AnalysisCryptographicPropertyBodyCompilerV0(kind,body) =
  require kind is an exact member of
    AnalysisCryptographicPropertySupportedKinds;
  require body satisfies that kind's exact property-owned schema;
  AnalysisKernelBodyCompilerRulesV0(body)

AdmitAnalysisCryptographicPropertySubjectV0(
  exact profiled candidate,
  exact imported profile preimages,
  exact semantic and module dependencies,
  exact evaluator support,
  deterministic limits)
  -> AnalysisCryptographicPropertyAdmissionOutcomeV0

AnalysisCryptographicPropertyAdmissionOutcomeV0 =
    Affirmative(AdmittedAnalysisSubject)
  | Unsupported | MissingDependency | CannotAnswer | KindMismatch
  | Refused | Malformed | DeterministicLimitExceeded | CheckerFailure
```

This profile owns the finite relation-bound Fresh special-soundness model, the
concrete adaptive classical Fiat--Shamir experiment, exact source and relation
ingress, concrete quantitative language, the concrete named-premise bodies for
Fresh public-coin distributions, provider outcome-carrier maps, and the
relation and Plan premises, and their property-specific adequacy, rule, use,
and authority contracts. It does not own the AFK family
transport theorem or theorem-source validation.

<!-- zkc-profile-source:analysis-property-publication:end -->

<!-- zkc-profile-source:analysis-transport-publication:start -->

## 4. AFK semantic-transport profile

```text
AnalysisAFKTransportProfileSourceV0 = {
  profile_family: "analysis.afk-transport",
  revision: 0,
  direct_imports: [AnalysisCryptographicPropertyLanguageProfileId],
  supported_subject_kinds: AnalysisAFKTransportSupportedKinds
}

AnalysisAFKTransportBodyCompilerV0(kind,body) =
  require kind is an exact member of AnalysisAFKTransportSupportedKinds;
  require body satisfies that kind's exact transport-owned schema;
  AnalysisCryptographicPropertyBodyCompilerRulesV0(body)

AdmitAnalysisAFKTransportSubjectV0(
  exact profiled candidate,
  exact imported property-profile preimage,
  exact semantic and module dependencies,
  exact evaluator support,
  deterministic limits)
  -> AnalysisAFKTransportAdmissionOutcomeV0

AnalysisAFKTransportAdmissionOutcomeV0 =
    Affirmative(AdmittedAnalysisSubject)
  | Unsupported | MissingDependency | CannotAnswer | KindMismatch
  | Refused | Malformed | DeterministicLimitExceeded | CheckerFailure
```

This profile owns the asymptotic family language, AFK theorem statement,
family applicability, semantic property transport, member correspondence,
pointwise specialization, replay distinctions, and the family sampler-adequacy
and oracle-process premise bodies. A citation, artifact
digest, proof-status assertion, or source-validation result is not theorem
meaning and is excluded from this profile's bodies.

<!-- zkc-profile-source:analysis-transport-publication:end -->

<!-- zkc-profile-source:analysis-theorem-validation-publication:start -->

## 5. AFK theorem-source-validation profile

```text
AnalysisAFKTheoremSourceValidationProfileSourceV0 = {
  profile_family: "analysis.afk-theorem-source-validation",
  revision: 0,
  direct_imports: [AnalysisAFKTransportLanguageProfileId],
  supported_subject_kinds:
    AnalysisAFKTheoremSourceValidationSupportedKinds
}

AnalysisAFKTheoremSourceValidationBodyCompilerV0(kind,body) =
  require kind is an exact member of
    AnalysisAFKTheoremSourceValidationSupportedKinds;
  require body satisfies that kind's exact validation-owned schema;
  AnalysisAFKTransportBodyCompilerRulesV0(body)

AdmitAnalysisAFKTheoremSourceValidationSubjectV0(
  exact profiled candidate,
  exact imported transport-profile preimage,
  exact source artifact and validation dependencies,
  exact evaluator support,
  deterministic limits)
  -> AnalysisAFKTheoremSourceValidationAdmissionOutcomeV0

AnalysisAFKTheoremSourceValidationAdmissionOutcomeV0 =
    Affirmative(AdmittedAnalysisSubject)
  | Unsupported | MissingDependency | CannotAnswer | KindMismatch
  | Refused | Malformed | DeterministicLimitExceeded | CheckerFailure
```

This child owns source-kind and source-validation bodies and every support,
validation, policy, judgment, checked-result, consumer, purpose, and authority
contract whose formation actually consumes that validation. It cannot change
the imported theorem statement or establish theorem truth merely by matching a
source artifact.

<!-- zkc-profile-source:analysis-theorem-validation-publication:end -->

<!-- zkc-profile-source:analysis-incremental-publication:start -->

## 6. Incremental-composition semantic profile

```text
AnalysisIncrementalCompositionProfileSourceV0 = {
  profile_family: "analysis.incremental-composition",
  revision: 0,
  direct_imports: [
    AnalysisKernelLanguageProfileId,
    PIRInteractionProfileId,
    PIRInterfacePlanProfileId,
    RelationsProfileId
  ],
  supported_subject_kinds:
    AnalysisIncrementalCompositionSupportedKinds
}

AnalysisIncrementalCompositionBodyCompilerV0(kind,body) =
  require kind is an exact member of
    AnalysisIncrementalCompositionSupportedKinds;
  require body satisfies that kind's exact composition-owned schema;
  AnalysisKernelBodyCompilerRulesV0(body)

AdmitAnalysisIncrementalCompositionSubjectV0(
  exact profiled candidate,
  exact imported profile preimages,
  exact semantic and module dependencies,
  exact evaluator support,
  deterministic limits)
  -> AnalysisIncrementalCompositionAdmissionOutcomeV0

AnalysisIncrementalCompositionAdmissionOutcomeV0 =
    Affirmative(AdmittedAnalysisSubject)
  | Unsupported | MissingDependency | CannotAnswer | KindMismatch
  | Refused | Malformed | DeterministicLimitExceeded | CheckerFailure
```

This profile owns the closed family, member-selection and recurrence premises,
the theorem's independent topology and depth axes, carried-obligation grammar,
and report-qualification law. It consumes exact Relations results through
owner-issued source families but does not turn a finite occurrence chain into
an induction theorem.

<!-- zkc-profile-source:analysis-incremental-publication:end -->

<!-- zkc-profile-source:analysis-incremental-validation-publication:start -->

## 7. Incremental-composition source-validation profile

```text
AnalysisIncrementalCompositionSourceValidationProfileSourceV0 = {
  profile_family: "analysis.incremental-composition-source-validation",
  revision: 0,
  direct_imports: [AnalysisIncrementalCompositionLanguageProfileId],
  supported_subject_kinds:
    AnalysisIncrementalCompositionSourceValidationSupportedKinds
}

AnalysisIncrementalCompositionSourceValidationBodyCompilerV0(kind,body) =
  require kind is an exact member of
    AnalysisIncrementalCompositionSourceValidationSupportedKinds;
  require body satisfies that kind's exact validation-owned schema;
  AnalysisIncrementalCompositionBodyCompilerRulesV0(body)

AdmitAnalysisIncrementalCompositionSourceValidationSubjectV0(
  exact profiled candidate,
  exact imported composition-profile preimage,
  exact theorem-source and live owner-result dependencies,
  exact evaluator support,
  deterministic limits)
  -> AnalysisIncrementalCompositionSourceValidationAdmissionOutcomeV0

AnalysisIncrementalCompositionSourceValidationAdmissionOutcomeV0 =
    Affirmative(AdmittedAnalysisSubject)
  | Unsupported | MissingDependency | CannotAnswer | KindMismatch
  | Refused | Malformed | DeterministicLimitExceeded | CheckerFailure
```

This child owns theorem-source validation and the validation-bearing support,
validation basis, policy, judgment, result-authority, consumer, and purpose
contracts for incremental-composition conclusions. Owner-local recurrence,
coverage, and CycleFold result bindings taint support and judgments forward;
they do not enter or rotate the imported family or theorem meaning.

<!-- zkc-profile-source:analysis-incremental-validation-publication:end -->

## 8. Rotation and nonclaims

A marked semantic change rotates its owning profile and exactly the downstream
import closure. Moving a page or marker without changing selected bytes does
not rotate identity. Adding an unrelated profile does not rotate an existing
root. The six profile IDs establish deterministic finite language identity
only; they prove no theorem, cryptographic property, relation satisfaction,
implementation conformance, or production readiness.
