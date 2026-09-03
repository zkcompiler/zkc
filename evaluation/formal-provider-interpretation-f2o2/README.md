# Finite Schnorr provider interpretation

This package asks one exact question:

> Does the generated VCVio artifact operationally correspond to the admitted
> finite Schnorr Fresh Protocol under all five clauses of the entry contract?

Run from the repository root with the pinned VCVio checkout available at the
path named by `ZKC_VCVIO_ROOT`, or at the package default:

```sh
python3 -B evaluation/formal-provider-interpretation-f2o2/run.py --check
```

The frozen aggregate is
`CannotAnswer/F2O2-C-TERMINALS-CLAUSE-4`. Schedule, values, Check and guard
denotations, and completed traces agree across the entire finite domain. The
entry contract nevertheless requires an image for every reachable outcome
lane, and the specified VCVio verifier carrier is `Bool`. It has distinct
images for `Accepted` and `Rejected`, but no third, non-collapsing image for
`OperationalNoncompletion`.

## Artifact and certificate

`generator.py` is untrusted. It reads the admitted subject's six normalized
views, the exact Check and guard algorithm preimages, and the package-local
relation and prover-plan candidates. It deterministically emits:

- `generated/SchnorrProvider.lean`, which instantiates the pinned
  `Schnorr.sigma` over `ZMod 3`, exposes the Fresh challenge draw, and defines
  the candidate commitment and response operations, with kernel-checked
  equations tying both operations to the provider's actual protocol fields;
  and
- `generated/certificate.json`, which binds the current source identities and
  all six view bodies, the algorithm preimages, the candidate bodies, the
  provider revision and Lean toolchain, and the occurrence, type, and outcome
  maps.

Generation has no authority. `generator.py --check` only says that these two
committed artifacts are the deterministic output for the inputs it reads.

## Independent checker

`checker.py` does not import the generator. It independently performs these
checks:

1. It uses the cold canonical-byte path to admit the Core and Protocol and
   rederive all six views. It then checks the certificate's source identities,
   view hashes and leaf counts, algorithm preimages, candidate formulas, and
   provider pin.
2. It derives the six-occurrence schedule, the two prover decisions, the
   public-coin challenge site, the completed-record output schema, and the two
   ordered terminal cases from the views. It checks totality, injectivity, and
   order of the occurrence and type maps.
3. It builds and runs `TermEvaluatorProbe.lean`, which invokes the portable
   term evaluator for all 81 verifier inputs and both guard inputs. Those rows
   must also equal the frozen term vectors and the closed Schnorr equation.
4. It verifies the VCVio revision and Lean version, builds the one absent
   `ZMod` support object in a temporary directory inside this package, and
   elaborates and executes the generated module against the read-only provider
   tree. Lean checks the commit/response field equations, and the provider
   emits all 81 verifier rows and all 81 honest-plan runs.
5. It compares each provider result with the portable-term result and closed
   form, then compares every completed provider transcript with the
   `ExecutionView` record schema and first-active terminal order.
6. It checks the three-lane carrier certificate against the owner's
   non-collapse rule. A missing outcome image remains `CannotAnswer`.

The separate terminal mechanization is absent at this branch head. In
accordance with the entry brief, completed runs use the Python first-active
terminal semantics already exercised by the terminal-projection and integrated
graph packages. The missing mechanized reading is frozen separately as
`CannotAnswer/F2O2-C-TERMINAL-MECHANIZATION-PENDING`; it is not converted into
positive evidence.

## Clause results

| Contract clause | Frozen result | Finite evidence |
|---|---|---|
| Schedule | `Affirmative/F2O2-A-SCHEDULE` | Six source occurrences and six distinct provider steps are total and order-preserving; prover decisions are exactly occurrences 0 and 2. |
| Values | `Affirmative/F2O2-A-VALUES` | Statement, witness, commitment, private state, challenge, response, and verifier-result carriers agree with their mapped source types. |
| Checks and guards | `Affirmative/F2O2-A-CHECKS-GUARDS` | Portable-term, provider, frozen-vector, and closed-form results agree on 81 verifier inputs; both Boolean guards agree. |
| Terminals | `CannotAnswer/F2O2-C-TERMINALS-CLAUSE-4` | All 81 completed runs select the same Accept or Reject terminal, but only two of three required reachable lanes have provider images. |
| Traces | `Affirmative/F2O2-A-TRACES` | All 81 completed records and provider transcripts agree step by step under the certified map. |

The 81 honest-plan runs contain 45 accepting and 36 rejecting executions.
The six view bodies contain 329 active leaves in total.

## Residual trust

The frozen findings retain four explicit residuals:

- the Lean kernel and VCVio's `OracleComp` semantics;
- finite differential evidence between the portable-term evaluator and the
  Python evaluator;
- the Fresh distribution and provider outcome-carrier premises; and
- the unproved checker adapter.

The generated provider module reports only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms for the measured declarations and
contains no `sorryAx` dependency. That is an elaboration observation, not a
proof of source correspondence by itself.

## What a gate pass does and does not establish

A gate pass establishes that the frozen `CannotAnswer` result is reproducible:
the generated artifacts still match their named inputs, both checker paths
cover the complete finite domains, the first four affirmative clause findings
remain supported, and the missing noncompletion image remains explicit rather
than being relabeled.

It does not establish complete operational correspondence, any protocol or
cryptographic property, theorem applicability, the Fresh sampling premise,
the provider outcome-carrier premise, general evaluator correctness, compiler
or backend correctness, production validity, or correspondence for another
subject or provider.
