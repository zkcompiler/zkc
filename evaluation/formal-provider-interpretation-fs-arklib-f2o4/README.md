# ArkLib interpretation of the finite Fiat--Shamir protocol

This package asks one exact question: does ArkLib's
`Reduction.fiatShamir` transform of the generated finite Schnorr reduction
operationally correspond, run for run, to the admitted one-shot
canonical-framed protocol when `fsChallengeOracle` is instantiated by the
source runtime's exact finite derivation table?

Run from the repository root:

```sh
python3 -B evaluation/formal-provider-interpretation-fs-arklib-f2o4/run.py --check
```

The frozen aggregate is
`Affirmative/F2O4-A-FS-FINITE-CORRESPONDENCE`.

## Generated provider

`generator.py` is untrusted. It inserts the authenticated nine-entry
derivation table into `template.lean` and emits
`generated/FiatShamirSchnorrArkLib.lean`. The module:

- imports the generated Schnorr reduction from the preceding ArkLib package;
- applies `Reduction.fiatShamir` to that reduction;
- implements `fsChallengeOracle` as a total lookup on the finite table;
- records the exact round, statement, message-prefix commitment, and answer at
  every prover and verifier query; and
- refuses by panic if execution reaches a point outside the admitted finite
  domain.

The generated certificate pins by content the owner pages, profile manifests,
source runtime model, executor, replay and views, both frozen run sets and
derivation tables, the preceding generated reduction, the term-calculus
inputs, and this package's source templates. It also pins ArkLib revision
`fad5cbf808774838924dc8273715724c6a6caa1f`, its tree, its dependency
revision, its sources, and Lean `v4.31.0`. No research note or sibling
finding file is a certificate input.

The current owner-authored challenge declarations rotate the Core and
construction inputs absorbed by the canonical-framed source runtime. The
nine-point challenge table therefore changes semantically, in row-major
`(statement, commitment)` order, from `(2,2,0,1,2,0,2,2,1)` to
`(0,1,1,1,2,2,1,1,1)`. The generated Lean lookup and certificate are
refrozen to those rederived values; this is not treated as a digest-only
re-pin. The finite correspondence outcomes below are then recomputed against
the new table.

## Independent checker

`checker.py` does not import the generator. It independently:

1. authenticates every certificate input and the generated Lean source;
2. re-admits the Core and one-shot protocol from the pinned owner sources;
3. executes and independently replays all 54 frozen source runs;
4. reconstructs every transcript prefix and authenticates all nine derivation
   table entries against those runs;
5. elaborates the Core term denotations for all 81 finite environments;
6. builds the preceding generated reduction into a package-local overlay,
   elaborates the transformed module under the pinned ArkLib checkout, and
   executes all 54 provider runs; and
7. compares schedule, values, exact oracle-query sequences, checks and
   terminals, and proof/completed-record traces under the declared maps.

The compiled modules contain no `sorryAx`. Their residual axiom closure is
`propext`, `Classical.choice`, and `Quot.sound`.

## Correspondence result

All five clauses hold on the complete one-shot corpus:

| Clause | Frozen finding | Checked evidence |
|---|---|---|
| schedule | `Affirmative/F2O4-A-SCHEDULE` | commitment, oracle query, response, check, and terminal occur in the same total injective order |
| values | `Affirmative/F2O4-A-VALUES` | statement, witness, commitment, challenge, response, check, and terminal carriers agree |
| oracle points | `Affirmative/F2O4-A-ORACLE-POINTS` | both provider sides issue exactly one query matching the source-derived point in every run |
| checks and terminals | `Affirmative/F2O4-A-CHECKS-TERMINALS` | the elaborated check denotation and `Option Unit` terminal equal the source check and lane image |
| traces | `Affirmative/F2O4-A-TRACES` | the proof and completed record agree occurrence by occurrence under the maps, excluding source-only receipts |

The 54 source and provider outcomes are 20 `Accepted` and 34 `Rejected`.
All recorded prover and verifier query sequences are retained in the checker
report.

A deliberately superfluous query, a missing query, and a query with a
different commitment framing are each rejected as `Negative` findings:
`F2O4-N-SUPERFLUOUS-ORACLE-QUERY`,
`F2O4-N-MISSING-ORACLE-QUERY`, and
`F2O4-N-DIFFERENTLY-FRAMED-ORACLE-QUERY`. A lookup outside the finite table
is `Refused/F2O4-R-OUTSIDE-FINITE-TABLE`.

## Provider declaration

The checker derives the closed provider carrier as `Option Unit` from the
executed transform. Its canonical values are `some ()` and `none`.
`Accepted` maps to `some ()`; `Rejected` maps to `none`; `Aborted`,
`InterpretationFailed`, `StrategyStopped`, and
`OperationalNoncompletion` are `Unmodelled`.

The source runtime's separate retrying construction now has zero measured
sampling-exhaustion runs at the repaired identities. The checker authenticates
and reports that exact finite count; it does not generalize the observation
into retrying-sampler totality or collapse the `InterpretationFailed` lane.

## Result boundary

A pass establishes finite, run-for-run operational correspondence for this
exact generated reduction, this exact one-shot protocol, this nine-point
table-backed oracle, and the five declared clauses. It also establishes the
stated provider carrier and lane interpretation for the measured domain.

It does not establish correspondence outside the finite domain, support for an
exhaustion-producing provider construct, arbitrary reductions or protocols,
owner publication, general compiler or evaluator correctness, any theorem,
protocol soundness, zero knowledge, Fiat--Shamir security, random-oracle or
quantum-random-oracle security, concrete-hash suitability,
duplex-sponge correspondence, or production readiness.
