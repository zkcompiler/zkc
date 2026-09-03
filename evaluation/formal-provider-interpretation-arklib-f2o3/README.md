# Finite Schnorr ArkLib provider interpretation

This package asks one exact question:

> Does this generated ArkLib `Reduction` operationally correspond to the
> admitted finite Schnorr Fresh Protocol under all five contract clauses?

Run from the repository root with the pinned ArkLib checkout at
`/home/wonjae/code/ArkLib`, or set `ZKC_ARKLIB_ROOT`:

```sh
python3 -B evaluation/formal-provider-interpretation-arklib-f2o3/run.py --check
```

The frozen aggregate is
`Affirmative/F2O3-A-FINITE-CORRESPONDENCE`. All five clauses agree over
their complete finite domains. The finding inventory separately retains one
`CannotAnswer` because Analysis has not published the provider declaration,
and two refused controls: the entry contract's second `none` producer is not
present at the pin, and two malformed certificate mutations are rejected.

## Provider and carrier

The generated artifact uses ArkLib revision
`fad5cbf808774838924dc8273715724c6a6caa1f`, its VCVio dependency at
`cbd4144b51d92da00dd50f05e068b2348fa6e529`, and
`leanprover/lean4:v4.31.0`. It defines a three-step `ProtocolSpec` with
directions prover-to-verifier, verifier-to-prover, prover-to-verifier. Its
`Reduction` uses field-of-three-elements statements, witnesses, commitments,
challenges, and responses, and `Unit` output types. The generated module also
implements ArkLib's challenge oracle by transporting VCVio's uniform `Fin 3`
sampler through the ring equivalence to `ZMod 3`; Fresh independence remains a
named premise.

ArkLib's source settles the carrier question differently from the entry
contract's premise. `Prover.run` returns the base, failure-free `OracleComp`
carrier. `Verifier.run` returns `OptionT (OracleComp) Unit`, and
`Reduction.run` lifts the total prover result before running that verifier.
For this generated reduction, the run form of `Reduction.verdict` therefore
has closed carrier `Option Unit`, with one producer of `none`: verifier
rejection. There is no prover-failure producer to interpret as a stopped
strategy.

The determinate package-local declaration is:

| Source lane | Provider lane image |
|---|---|
| `Accepted` | `Image(some ())` |
| `Rejected` | `Image(none)` |
| `Aborted` | `Unmodelled` |
| `StrategyStopped` | `Unmodelled` |
| `OperationalNoncompletion` | `Unmodelled` |

The modelled lanes are exactly `Accepted` and `Rejected`. An operational
completion premise is still relevant to property reasoning over the whole
outcome partition, but it is not needed to disambiguate this carrier: the
provider type already excludes prover failure.

## Generated reduction

`generator.py` is untrusted. It deterministically emits:

- `generated/SchnorrArkLib.lean`, which defines the `ProtocolSpec`, stateful
  prover, verifier, and `Reduction`; and
- `generated/certificate.json`, which binds the admitted source views,
  current owner pages and manifests, direct package inputs, generated module,
  ArkLib and dependency trees, and selected provider source files.

The generated prover's commitment and response fields are tied to the
selected Plan recipes by kernel-checked equations. The checker also executes
the actual prover and actual reduction verdict for every honest-plan input;
the equations are not used as a substitute for execution.

The certificate digest-pins owner pages, profile manifests, and direct inputs
consumed by this package. It does not digest-pin this research note or another
package's frozen findings.

## Independent checker

`checker.py` does not import the generator. It:

1. cold-admits the current Core and Protocol and re-derives all six views;
2. authenticates owner-page, manifest, carrier, algorithm, candidate-body,
   provider-source, occurrence, type, and lane-map bindings;
3. reads ArkLib and VCVio source to check where the option layer and failure
   operation actually reside;
4. builds the mechanized term module and evaluates all 81 Check inputs, both
   guard inputs, and both first-active terminal choices;
5. elaborates the generated module under the pinned provider and toolchain,
   rejecting any `sorryAx` dependency;
6. executes all 81 ArkLib verifier inputs and all 81 honest-plan runs; and
7. compares every Check result, terminal image, and completed trace, while
   rejecting an aliased schedule and a collapsed lane map as negative controls.

All required ArkLib and Mathlib object files were already built in the pinned
checkout, so this package does not construct an overlay. The checker fails
closed with an instruction to construct and record a package-local overlay if
either required object is absent.

The 81 honest-plan runs contain 45 accepting and 36 rejecting executions. The
six view bodies contain 329 active leaves.

## Clause results

| Contract clause | Frozen result | Finite evidence |
|---|---|---|
| Schedule | `Affirmative/F2O3-A-SCHEDULE` | Six source occurrences and six distinct provider steps are total and order-preserving; prover rounds are exactly occurrences 0 and 2. |
| Values | `Affirmative/F2O3-A-VALUES` | Statement, witness, three transcript values, the nonce projection of provider state, verifier predicate, and verdict carriers agree with the mapped source values. |
| Checks and guards | `Affirmative/F2O3-A-CHECKS-GUARDS` | Portable-term, ArkLib, frozen-vector, and closed-form results agree on all 81 verifier inputs; both guard inputs agree. |
| Terminals | `Affirmative/F2O3-A-TERMINALS` | The mechanized first-active reading and `Option Unit` image agree on all 81 runs. |
| Traces | `Affirmative/F2O3-A-TRACES` | All 81 completed source records and ArkLib transcripts agree step by step under the certified map. |

## Analysis publication remains open

The five-lane map is an authenticated package-local input, not a formed
`AnalysisNamedPremise`. The proposed owner declaration is recorded in the
companion research note. Until the Analysis owner publishes the ArkLib source
pin, the closed `Option Unit` carrier, the modelled lanes, the total five-lane
map, and corresponding manifest definitions, premise formation remains
`CannotAnswer/F2O3-C-PROVIDER-MAP-PREMISE-UNPUBLISHED`.

## What a pass does and does not establish

A pass establishes reproducibility for one admitted finite subject and one
pinned provider: generated artifacts, five operational correspondence clauses
over complete finite domains, the mechanized terminal reading, and a
determinate proposed provider declaration.

It does not publish an Analysis premise, establish the Fresh sampling premise,
prove a protocol or cryptographic property, establish theorem applicability,
prove general evaluator correctness, establish correspondence for another
subject or provider, prove compiler or backend correctness, validate a
deployment, or establish production readiness. Residual trust remains in the
Lean kernel, the pinned ArkLib and VCVio semantics, the finite evaluator
differential, named premises, and the unproved checker adapter.
