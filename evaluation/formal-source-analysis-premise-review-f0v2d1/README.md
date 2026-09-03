# Analysis named-premise owner-text review

This package runs the third verification review over `27871e7..e950263`. Its
one exact question is:

> Do the reviewed Analysis owner pages close all nine named-premise questions,
> including the profile-specific hypothesis argument schemas and the provider
> lane/completion law, and do the migrated evaluation packages now carry only
> owner-determined premise identities?

Run from the repository root:

    python3 -B evaluation/formal-source-analysis-premise-review-f0v2d1/run.py --check

The frozen aggregate is
`Negative/F0V2D1-N-ANALYSIS-PREMISE-TEXT-NOT-CLOSED`. Seven review questions
are affirmative and two are negative:

| Review question | Outcome | Stable finding |
|---|---|---|
| Name closure | Affirmative | F0V2D1-A-NAME-CLOSURE |
| Constructor consistency | Affirmative | F0V2D1-A-CONSTRUCTOR-CONSISTENCY |
| Intake soundness | Affirmative | F0V2D1-A-INTAKE-SOUNDNESS |
| Decision fidelity | Affirmative | F0V2D1-A-DECISION-FIDELITY |
| Schnorr coordinate and binding formation | Affirmative | F0V2D1-A-SCHNORR-BINDINGS |
| Profile and manifest closure | Affirmative | F0V2D1-A-PROFILE-MANIFESTS |
| Existing-package refreeze | Negative | F0V2D1-N-MIGRATED-IDENTITY-INPUTS |
| Hypothesis argument-schema closure | Affirmative | F0V2D1-A-HYPOTHESIS-ARGUMENT-SCHEMAS |
| Provider lane and completion consistency | Negative | F0V2D1-N-MIGRATED-COMPLETION-LAW |

## What the check covers

The checker pins the owner pages, profile manifests, intake probe, migrated
Analysis closure model, and its direct migrated consumers. It verifies:

- every reviewed law family has one closed definition; the direct profile,
  kind, provider Protocol, goal binding, construction length, and fresh-law
  leaf binders are explicit;
- all eleven question, twelve goal, six context, five support, one judgment,
  twelve premise-body, and thirty-one anonymous node displays carry their
  required fields;
- all twelve intake branches remain explicit and fail closed;
- the property profile's five argument-schema rows close six hypothesis
  declarations, while the transport profile's two rows close two declarations,
  with the admitted coordinate first and no free or extra argument;
- all six Schnorr premise constructors, the extractor question's separately
  scoped pair, both construction premises, and both family premises are exact;
- both publication compilers agree on the current and review-base sources and
  reproduce the six-profile rotation cone; and
- an encoder implemented in this review, without the migrated model's body
  encoders or identity former, reproduces the migrated relation-bound goal
  digest `79dcc80f...ccb4` and family goal digest `9c49308e...b2f2`.

The independently reproduced family goal is owner-determined. The migrated
relation-bound goal is not: its Fresh premise uses the challenge occurrence
coordinate as a proxy, while the owner now requires the authenticated
`fresh_law` declaration leaf. The imported public-coin projection exposes no
such field. The construction premise similarly reads one legacy
`max_attempts` field rather than identity-bearing challenge rules and their
per-rule `maximum_draws` values.

The provider lane vocabulary and `Image | Unmodelled` law agree across the PIR
partition, Analysis owner pages, intake probe, and migrated model. The tenth
kind is also present everywhere, but the migrated property declaration catalog
has no exact operational-completion hypothesis declaration; its test uses an
arbitrary symbol instead. Provider-bound premises additionally remain
unformable until the property profile publishes exact provider and carrier
declarations.

The exact remaining refreeze inputs are therefore:

- the authenticated public-coin-view `fresh_law` declaration leaf for the
  migrated Schnorr Protocol;
- identity-bearing construction challenge rules and each rule's
  `maximum_draws` value;
- published property-profile provider and closed-carrier declarations; and
- an exact property-profile operational-completion hypothesis declaration
  reference.

## What a pass establishes

A pass establishes only that the nine review classifications, three supporting
findings, two independent finite identity reconstructions, and the two concrete
migration defects are reproduced from the pinned checkout. It does not turn a
proxy identity into an owner-determined one.

## What a pass does not establish

This source and finite-identity review does not edit or publish Analysis
semantics, form a provider premise, establish any premise, prove relation
satisfaction or Plan honesty, prove theorem truth or applicability, validate a
compiler or backend, establish cryptographic security, or authorize deployment.
