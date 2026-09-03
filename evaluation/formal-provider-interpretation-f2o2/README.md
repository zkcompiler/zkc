# Finite Schnorr provider interpretation

This package asks one exact question:

> Does the generated VCVio artifact operationally correspond to the admitted
> finite Schnorr Fresh Protocol under all five clauses of the restated entry
> contract?

Run from the repository root with the pinned VCVio checkout available at the
path named by `ZKC_VCVIO_ROOT`, or at the package default:

```sh
python3 -B evaluation/formal-provider-interpretation-f2o2/run.py --check
```

The frozen aggregate is
`Affirmative/F2O2-A-FINITE-CORRESPONDENCE`. All five clauses agree over
their complete finite domains. The finding inventory has eleven affirmative
findings and one `CannotAnswer`: Analysis has not published the provider
declaration that would turn the package's five-lane map into a formed premise.

## Round two

The terminal clause now checks the restated contract on every run. The
declared provider is VCVio at revision
`de0a3108140e3e04a7ebf0075aa110b459ee6e8a` under
`leanprover/lean4:v4.33.1`, with closed carrier `Bool`, modelled lanes
`Accepted` and `Rejected`, and this total map:

| Source lane | Provider lane image |
|---|---|
| `Accepted` | `Image(true)` |
| `Rejected` | `Image(false)` |
| `Aborted` | `Unmodelled` |
| `StrategyStopped` | `Unmodelled` |
| `OperationalNoncompletion` | `Unmodelled` |

For each of the 81 source runs, the checker obtains the source terminal from
the mechanized first-active reading and requires the provider Boolean to equal
the image of that source lane. A lane occurring on the domain without an
image, or an `Image` outside `modelled_lanes`, remains `CannotAnswer`.
Only `Accepted` and `Rejected` occur on this domain.

The mechanization dependency is now consumed. `TermEvaluatorProbe.lean`
imports the mechanized Terminal module, evaluates the package's closed
`Region` reading for both guard values, and emits the unique attempted
terminal. The checker binds
those two results to the owner-derived terminal cases and uses them in every
completed-run and trace comparison. The pinned module also contains the
universal `attempted_iff_region_holds` and `attemptedWhenever_sound`
theorems. The former pending-mechanization finding is therefore retired.

The admitted Core, Protocol, all six view bodies, and the published relation
and Plan candidate bodies changed after round one. The certificate has been
re-derived from the current tree. It pins current PIR and Analysis owner
pages, the relevant profile manifests, the admitted Core and Protocol bodies,
all six active view manifests,
the portable-term vectors, and the mechanized Terminal source. It does not pin
another package's frozen findings.

The generated VCVio module did not require a semantic change. Its digest is
unchanged, and Lean still kernel-checks the equations tying the provider's
commit and respond fields to the selected Plan recipes.

## Independent checker

`generator.py` is untrusted. It deterministically emits the provider module
and source-bound certificate. `checker.py` does not import the generator. It:

1. cold-admits the current Core and Protocol and re-derives all six views;
2. authenticates the certificate's owner-page, manifest, carrier, algorithm,
   candidate-body, provider, occurrence, type, and five-lane pins;
3. builds the mechanized term and Terminal source and evaluates all 81 Check
   inputs, both guard inputs, and both first-active terminal choices;
4. checks the provider revision and toolchain, builds the one absent `ZMod`
   support object in a temporary package-local overlay, and executes the
   generated module;
5. compares all 81 provider checks, all 81 honest-plan runs, all 81 terminal
   images, and all 81 completed traces; and
6. records the still-unpublished Analysis declaration separately from the
   operational correspondence result.

The 81 plan runs contain 45 accepting and 36 rejecting executions. The six
view bodies contain 329 active leaves.

## Clause results

| Contract clause | Frozen result | Finite evidence |
|---|---|---|
| Schedule | `Affirmative/F2O2-A-SCHEDULE` | Six source occurrences and six distinct provider steps are total and order-preserving; prover decisions are exactly occurrences 0 and 2. |
| Values | `Affirmative/F2O2-A-VALUES` | Statement, witness, commitment, private state, challenge, response, and verifier-result carriers agree with their mapped source types. |
| Checks and guards | `Affirmative/F2O2-A-CHECKS-GUARDS` | Portable-term, provider, frozen-vector, and closed-form results agree on 81 verifier inputs; both Boolean guards agree. |
| Terminals | `Affirmative/F2O2-A-TERMINALS` | The mechanized first-active reading and provider image agree on every run; the domain reaches 45 `Accepted` and 36 `Rejected` lanes. |
| Traces | `Affirmative/F2O2-A-TRACES` | All 81 completed records and provider transcripts agree step by step under the certified maps. |

## Analysis publication still required

The five-lane map above is an authenticated package input, not yet an
`AnalysisNamedPremise`. To form that premise, the Analysis owner must publish
the declaration described by the provider-carrier decision packet:

- `VCVioProviderDeclaration`, naming system `vcvio`, the content digest of
  the checkout at the pinned revision computed under the Foundation digest
  rule, toolchain `leanprover/lean4:v4.33.1`, and
  `modelled_lanes = [Accepted, Rejected]`;
- `VCVioBooleanCarrier`, declaring the closed `Bool` schema with canonical
  values `true` and `false`;
- `VCVioSchnorrOutcomeMapPremise` for the admitted Protocol and the exact
  five-lane map above, sourced from the provider declaration at
  `FrozenExecutableFalsification` evidence depth; and
- two `analysis.semantic-law` manifest definitions for the provider
  declaration and Boolean carrier, dependencies from the property core to
  both, and the corresponding profile revision advance.

Until those owner-page and manifest changes are published, the frozen result
is `CannotAnswer/F2O2-C-PROVIDER-MAP-PREMISE-UNPUBLISHED` for premise
formation. The operational five-clause aggregate does not convert that absence
into an affirmative premise claim.

## What a gate pass does and does not establish

A pass establishes reproducibility for one admitted finite subject and one
pinned provider: current generated artifacts, five contract clauses over the
complete finite domains, the mechanized completed-run terminal reading, and
the explicit boundary between the package map and a formed Analysis premise.

It does not establish that the provider map is a published premise, the Fresh
sampling premise, a protocol or cryptographic property, theorem applicability,
general evaluator correctness, correspondence for another subject or provider,
compiler or backend correctness, deployment validity, or production
readiness. The residual trust list still names the Lean kernel and VCVio
`OracleComp` semantics, the finite evaluator differential, the distribution
and provider-map premises, and the unproved checker adapter.
