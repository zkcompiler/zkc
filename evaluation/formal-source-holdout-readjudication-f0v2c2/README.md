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
| WHIR finite constructive member | fits | both Reductions are delayed under the exact accepting guard; the unconditional fallback therefore retains the initial Claim |
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

Round five re-pins the same eight verdict rows after the three static-view
profiles acquired explicit law selections. No verdict changes. A separate
`CannotAnswer/F0V2C2-C-FAMILY-VIEW-REFERENCE-BOUNDARY` finding records that
the canonical-framed transcript view's application-domain declaration leaf is
not admitted by the current `PIRReference` union. This owner-text gap limits
family-view transport, but it does not supply or remove a holdout boundary and
therefore does not change the verdict-only aggregate.

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
- evaluates the migrated structural `Must` rule on the accepting nested guard,
  proving all five positive WHIR literals, and exhausts all 32 Check valuations
  for the identically guarded Reduction schedule and two terminal frontiers;
- evaluates the repaired `BoundaryRegion`, `ClaimSourceRegion`, and
  `ClaimStatus` laws on the represented WHIR and WARPfold shapes: no `Unknown`
  arises, WHIR Accept has no live Claim, its fallback has only the initial
  Claim, and no verdict changes;
- requires every fitting row to map its Analysis observables through all six
  normalized views with no missing PIR coordinate;
- requires every breaking row to name both a boundary and an observable or
  termination mode with no current coordinate; and
- freezes the finding sequence and adjudication bytes in
  [`expected-findings.json`](expected-findings.json).

The source's legacy partial-guard Reduction schedule is deliberately refused:
scope openings are deterministic and unguarded, and checked semantic guard
implication is outside this regime. The corrected carrier gives both
Reductions and their accepting consumer exactly the same guard, followed by an
unconditional fallback. The structural-axis meaning for interpretation failure
is also corrected to the separate completed failure lane. Neither correction
changes a holdout verdict.

## What a pass establishes

A pass establishes only that these exact source bytes admit the frozen terminal
shapes, six common-view coordinate mappings, bounded family-view readings,
outcome partition, and eight verdict comparisons. It also establishes that the
selected accepting guard has the required positive literals and that the
corrected WHIR carrier satisfies the owner's syntactic guard-identity rule over
the bounded valuation census.

The four boundary analyses do not publish exact Core tables. Their finite or
virtual fitting shapes therefore retain `CannotAnswer` for exact CheckRef,
ReductionRef, ClaimRef, and failure-guard selection until a concrete source
profile is authored. This missing source evidence does not become a target
owner-page defect.

The represented-shape check reconstructs the owner-authored initial
binding-opening and Reduction-output source regions explicitly. It shows only
that the repaired source map changes none of these frozen holdout verdicts; it
does not prove `ClaimStatus` for arbitrary Core values.

The pass does not establish complete family-view reference transport: the
canonical application-domain leaf remains outside the displayed atomic
boundary until the owner text changes or the family view stops using it.

## Nonclaims

A pass does not establish an admitted Core for Circle STARKs, WARPfold,
multiparty Sumcheck, or Galois-ring protocols; correspondence to an
implementation; correctness of a Plan, Relations profile, endpoint, OIR, or
backend; relation satisfaction; theorem truth or applicability; soundness,
knowledge soundness, zero knowledge, Fiat--Shamir security, multiparty
security, or production readiness. It does not edit or publish owner text or
rotate any semantic identity.
