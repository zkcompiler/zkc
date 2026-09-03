# Cold protocol holdout readjudication

## Exact question

Do the migrated PIR terminal, owner-view, and outcome contracts represent every
cold protocol holdout at its recorded boundary, with the same verdict as both
the adjudication record and the structural-axes matrix?

## Bounded answer

Yes. The frozen result is
`Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`: all five holdouts have a
verdict, represented by eight rows where the earlier record separated a finite
or virtual form from a broader form. Five rows fit and three break at the same
named boundaries predicted by the matrix. There are no verdict disagreements
and no bends.

| Source form | Verdict | Exact limit |
|---|---|---|
| WHIR finite constructive member | fits | the old two-terminal sketch needs a post-fold rejecting frontier or equivalent guard restructuring |
| Circle STARK finite instance | fits | exact Check, Reduction, Claim, and typed-failure references require a selected source profile |
| WARPfold finite fold | fits | exact typed-failure guard and carrier references require a selected source profile |
| WARPfold broad cross-system application | breaks | cross-execution state and imported challenge authority are absent |
| Physical multiparty Sumcheck | breaks | participant-local execution, knowledge, delivery, decisions, and agreement are absent |
| Commitment-anchored virtual Sumcheck proof | fits | exact commitment and Sumcheck carrier references require a selected source profile |
| Complete noninteractive Galois-ring argument | breaks | the source omits the transform, interpretation, and complete terminal semantics |
| Explicit interactive Galois-ring components | fits | exact component selection and carrier references require a selected source profile |

The complete terminal, view, and outcome ledger is frozen in
[`adjudication.json`](adjudication.json). The supporting note gives the
field-by-field reading and exact owner-section citations.

## Executable evidence

Run from the repository root:

```sh
python3 -B evaluation/formal-source-holdout-readjudication-f0v2c2/run.py --check
```

The checker:

- pins every file in the cold-holdout record, all five migrated owner pages,
  the migration record, and the structural-axes sources by exact bytes;
- requires five named holdouts and eight unique verdict rows;
- compares every row with both the matrix prediction and its embedded
  projection of the adjudication record, emitting a distinct finding if any
  comparison disagrees;
- evaluates the migrated structural `Must` rules on nested guards, proving all
  five positive WHIR literals on acceptance and the two pre-fold positives on
  the post-fold rejecting frontier;
- requires every fitting row to map its Analysis observables through all six
  normalized views with no missing PIR coordinate;
- requires every breaking row to name both a boundary and an observable or
  termination mode with no current coordinate; and
- freezes the finding sequence and adjudication bytes in
  [`expected-findings.json`](expected-findings.json).

Two negative observations are deliberate. The old WHIR two-terminal carrier is
refused by exact terminal-claim liveness after a partial reduction. The
structural-axes description of interpretation failure as a rejecting or
aborting terminal is also refused by the migrated partition: canonical
interpretation failure is a separate completed failure lane and is not a Core
terminal. Neither changes a holdout verdict.

## What a pass establishes

A pass establishes only that these exact source bytes admit the frozen terminal
shapes, view-coordinate mapping, outcome partition, and eight verdict
comparisons. It also establishes that the selected nested guards have the
required positive literals under the migrated syntactic `Must` calculation.

The four boundary analyses do not publish exact Core tables. Their finite or
virtual fitting shapes therefore retain `CannotAnswer` for exact CheckRef,
ReductionRef, ClaimRef, and failure-guard selection until a concrete source
profile is authored. This missing source evidence does not become a target
owner-page defect.

## Nonclaims

A pass does not establish an admitted Core for Circle STARKs, WARPfold,
multiparty Sumcheck, or Galois-ring protocols; correspondence to an
implementation; correctness of a Plan, Relations profile, endpoint, OIR, or
backend; relation satisfaction; theorem truth or applicability; soundness,
knowledge soundness, zero knowledge, Fiat--Shamir security, multiparty
security, or production readiness. It does not edit or publish owner text or
rotate any semantic identity.
